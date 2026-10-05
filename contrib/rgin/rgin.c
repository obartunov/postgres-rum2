/*
 * rgin.c
 *		Research ranked GIN access method (M1 prototype).  Not for production.
 *
 * rgin reuses the stock GIN page formats, entry tree, posting trees, WAL
 * and build accumulator unchanged.  It differs from GIN in three places:
 *
 *	1. Posting payload.  Each posting stores a "pseudo item pointer" that
 *	   packs the heap TID and a 16-bit client payload:
 *			V  = ((blk << 9 | off) << 16) | payload
 *			ip = item pointer with (block, offset) = split of 2*V+1
 *	   Pseudo items sort by (heap TID, payload), so per-key posting lists
 *	   stay in heap TID order and GIN's compression, page split and merge
 *	   code work on them unmodified.  The extra bits cost about two bytes
 *	   per posting in the varbyte deltas.  Research limit: heap block
 *	   < 2^17 (1 GB of 8 kB pages), heap offset < 512.
 *
 *	2. Root summary and generation.  Per term, a Pareto set of payloads
 *	   (the root frontier) is stored as an ordinary GIN entry under a
 *	   "magic" key (tag byte + lexeme) whose fake item pointers encode
 *	   the points.  df at build, N and sum(dl) are stored the same way.
 *	   No format change; the build-time values are the statistics
 *	   generation G of M0.7 and are never updated.
 *
 *	3. Ordered scan.  amgettuple returns an exact score-ordered stream
 *	   (score desc, heap TID asc) without knowing LIMIT: either FULL
 *	   (decode all eligible postings, score, sort) or C (M0.6 incremental
 *	   phases over terms by decreasing root bound, nothing discarded).
 *
 * Research-only restrictions: fastupdate=off, single-column, serial build
 * in one accumulator pass, no bitmap scans, no bulk delete, no partial
 * match, append-only (frontier only widens).
 */
#include "postgres.h"

#include <math.h>

#include "access/amapi.h"
#include "access/gin_private.h"
#include "access/heapam.h"
#include "access/htup_details.h"
#include "access/reloptions.h"
#include "access/relscan.h"
#include "access/tableam.h"
#include "access/xloginsert.h"
#include "catalog/index.h"
#include "commands/vacuum.h"
#include "miscadmin.h"
#include "portability/instr_time.h"
#include "nodes/pathnodes.h"
#include "storage/bufmgr.h"
#include "tsearch/ts_type.h"
#include "catalog/pg_type.h"
#include "utils/array.h"
#include "utils/builtins.h"
#include "utils/guc.h"
#include "utils/index_selfuncs.h"
#include "utils/memutils.h"
#include "utils/rel.h"
#include "utils/snapmgr.h"

#include "rgin.h"

PG_MODULE_MAGIC_EXT(.name = "rgin",.version = "1.0-m1");

/* ---------------------------------------------------------------- GUCs */

enum
{
	RGIN_STRATEGY_FULL,
	RGIN_STRATEGY_C,
	RGIN_STRATEGY_AUTO
};

static const struct config_enum_entry strategy_options[] = {
	{"full", RGIN_STRATEGY_FULL, false},
	{"c", RGIN_STRATEGY_C, false},
	{"auto", RGIN_STRATEGY_AUTO, false},
	{NULL, 0, false}
};

static int	rgin_strategy = RGIN_STRATEGY_AUTO;
static int	rgin_pool_limit_kb = 65536;
static bool rgin_verify = false;
static bool rgin_build_evidence = true;

/* ---------------------------------------------------------------- pseudo items */

#define RGIN_OFF_BITS		9
#define RGIN_MAX_BLOCK		((BlockNumber) 1 << 17)

static inline uint64
ip_u64(ItemPointer ip)
{
	return ((uint64) GinItemPointerGetBlockNumber(ip) << 11) |
		GinItemPointerGetOffsetNumber(ip);
}

static inline ItemPointerData
u64_ip(uint64 v)
{
	ItemPointerData ip;

	ItemPointerSetBlockNumber(&ip, (BlockNumber) (v >> 11));
	ip.ip_posid = (OffsetNumber) (v & 2047);
	return ip;
}

static inline ItemPointerData
rgin_encode(ItemPointer heaptid, RginPayload p)
{
	BlockNumber blk = ItemPointerGetBlockNumber(heaptid);
	OffsetNumber off = ItemPointerGetOffsetNumber(heaptid);
	uint64		rk;

	if (blk >= RGIN_MAX_BLOCK || off >= (1 << RGIN_OFF_BITS))
		ereport(ERROR,
				(errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
				 errmsg("rgin research prototype: heap TID (%u,%u) out of encodable range",
						blk, off)));
	rk = ((uint64) blk << RGIN_OFF_BITS) | off;
	return u64_ip((((rk << 16) | p) << 1) | 1);
}

/* heap row key (blk << 9 | off) of a pseudo item */
static inline uint64
rgin_rk(ItemPointer ip)
{
	return ip_u64(ip) >> 17;
}

static inline RginPayload
rgin_payload(ItemPointer ip)
{
	return (RginPayload) ((ip_u64(ip) >> 1) & 0xffff);
}

static inline void
rk_to_tid(uint64 rk, ItemPointer tid)
{
	ItemPointerSet(tid, (BlockNumber) (rk >> RGIN_OFF_BITS),
				   (OffsetNumber) (rk & ((1 << RGIN_OFF_BITS) - 1)));
}

/* ---------------------------------------------------------------- magic entries */

static Datum
magic_key(char tag, const char *lex, int len)
{
	text	   *t = (text *) palloc(VARHDRSZ + 1 + len);

	SET_VARSIZE(t, VARHDRSZ + 1 + len);
	VARDATA(t)[0] = tag;
	memcpy(VARDATA(t) + 1, lex, len);
	return PointerGetDatum(t);
}

/*
 * Look up an entry key.  Returns true if found; then either *root is a
 * posting tree root, or *items and *n are the decoded inline posting list.
 */
static bool
lookup_entry(Relation index, GinState *gs, Datum key,
			 BlockNumber *root, ItemPointer *items, int *n)
{
	GinBtreeData btree;
	GinBtreeStack *stack;
	bool		found;

	*root = InvalidBlockNumber;
	*items = NULL;
	*n = 0;
	ginPrepareEntryScan(&btree, FirstOffsetNumber, key, GIN_CAT_NORM_KEY, gs);
	stack = ginFindLeafPage(&btree, true, false);
	found = btree.findItem(&btree, stack);
	if (found)
	{
		Page		page = BufferGetPage(stack->buffer);
		IndexTuple	itup = (IndexTuple) PageGetItem(page, PageGetItemId(page, stack->off));

		if (GinIsPostingTree(itup))
			*root = GinGetPostingTree(itup);
		else if (GinGetNPosting(itup) > 0)
			*items = ginReadTuple(gs, FirstOffsetNumber, itup, n);
	}
	LockBuffer(stack->buffer, GIN_UNLOCK);
	freeGinBtreeStack(stack);
	return found;
}

ItemPointer
rgin_read_magic(Relation index, GinState *gs, char tag,
				const char *lex, int len, int *n)
{
	BlockNumber root;
	ItemPointer items;

	if (!lookup_entry(index, gs, magic_key(tag, lex, len), &root, &items, n))
		return NULL;
	if (root != InvalidBlockNumber)
		elog(ERROR, "rgin: magic entry unexpectedly stored as posting tree");
	return items;
}

static void
insert_magic(GinState *gs, char tag, const char *lex, int len,
			 ItemPointerData *items, int n, GinStatsData *buildStats)
{
	ginEntryInsert(gs, FirstOffsetNumber, magic_key(tag, lex, len),
				   GIN_CAT_NORM_KEY, items, n, buildStats);
}

static void
insert_scalar(GinState *gs, const char *name, int64 v, GinStatsData *buildStats)
{
	ItemPointerData ip;

	if (v < 0 || v >= (int64) InvalidBlockNumber)
		elog(ERROR, "rgin research prototype: statistic %s out of range", name);
	ItemPointerSet(&ip, (BlockNumber) v, FirstOffsetNumber);
	insert_magic(gs, RGIN_TAG_STATS, name, strlen(name), &ip, 1, buildStats);
}

/* Pareto frontier of payloads (tf high, norm low), sorted by tf asc */
static int
frontier_of(ItemPointerData *items, int n, ItemPointerData *out)
{
	int			best[256];
	int			m = 0,
				maxtf = -1;

	for (int c = 0; c < 256; c++)
		best[c] = -1;
	for (int i = 0; i < n; i++)
	{
		RginPayload p = rgin_payload(&items[i]);

		best[p & 0xff] = Max(best[p & 0xff], p >> 8);
	}
	for (int c = 0; c < 256; c++)
	{
		if (best[c] > maxtf)
		{
			out[m++] = rgin_point_to_item((RginPayload) ((best[c] << 8) | c));
			maxtf = best[c];
		}
	}
	return m;
}

/* ---------------------------------------------------------------- instrumentation */

typedef struct RginBuildInfo
{
	int64		N;
	int64		sumdl;
	int64		terms;
	int64		postings;
	int64		frontier_points;
	int64		frontier_hist[65];	/* [64] = >= 64 */
} RginBuildInfo;

static RginBuildInfo build_info;
static int64 widen_events = 0;

typedef struct RginStats
{
	const char *strategy;
	int			nterms;
	int			phases;
	int64		postings;
	int64		leaf_pages;
	int64		descents;
	int64		seeks;
	int64		docs_scored;
	int64		contribs;
	int64		bound_evals;
	int64		pool_peak;
	int64		pool_peak_bytes;
	int64		emitted;
	bool		fallback;
	int64		full_docs;
	double		full_merge_ms;	/* FULL: cursor merge + scoring */
	double		full_sort_ms;	/* FULL: heapify of all scored docs */
	double		phase_ms;		/* C: time inside phases */
} RginStats;

static RginStats last_stats;
static bool last_stats_valid = false;

/* ---------------------------------------------------------------- build */

typedef struct RginBuildState
{
	GinState	gs;
	BuildAccumulator accum;
	MemoryContext tmpCtx;
	MemoryContext funcCtx;
	int64		N;
	int64		sumdl;
	int64		npostings;
	GinStatsData stats;
} RginBuildState;

static void
rgin_build_cb(Relation index, ItemPointer tid, Datum *values,
			  bool *isnull, bool tupleIsAlive, void *state)
{
	RginBuildState *bs = (RginBuildState *) state;
	MemoryContext old;
	TSVector	tsv;
	WordEntry  *we;
	int			dl;
	GinNullCategory cat = GIN_CAT_NORM_KEY;

	if (isnull[0])
		return;
	old = MemoryContextSwitchTo(bs->funcCtx);
	tsv = DatumGetTSVector(values[0]);
	dl = rgin_tsv_dl(tsv);
	bs->N++;
	bs->sumdl += dl;
	we = ARRPTR(tsv);
	for (int i = 0; i < tsv->size; i++)
	{
		Datum		key = PointerGetDatum(cstring_to_text_with_len(STRPTR(tsv) + we[i].pos,
																   we[i].len));
		ItemPointerData item = rgin_encode(tid,
										   rgin_bm25_payload(rgin_tsv_tf(tsv, &we[i]), dl));

		MemoryContextSwitchTo(bs->tmpCtx);
		ginInsertBAEntries(&bs->accum, &item, FirstOffsetNumber, &key, &cat, 1);
		MemoryContextSwitchTo(bs->funcCtx);
	}
	MemoryContextSwitchTo(old);
	MemoryContextReset(bs->funcCtx);

	if (bs->accum.allocatedMemory >= maintenance_work_mem * (Size) 1024)
		ereport(ERROR,
				(errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
				 errmsg("rgin research prototype builds in one accumulator pass; raise maintenance_work_mem")));
}

static IndexBuildResult *
rginbuild(Relation heap, Relation index, IndexInfo *indexInfo)
{
	RginBuildState bs;
	Buffer		RootBuffer,
				MetaBuffer;
	double		reltuples;
	ItemPointerData *list;
	Datum		key;
	GinNullCategory category;
	uint32		nlist;
	OffsetNumber attnum;
	ItemPointerData *fbuf = palloc(sizeof(ItemPointerData) * 257);
	IndexBuildResult *result;
	MemoryContext oldCtx;

	if (RelationGetNumberOfBlocks(index) != 0)
		elog(ERROR, "index \"%s\" already contains data", RelationGetRelationName(index));
	if (GinGetUseFastUpdate(index))
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("rgin research prototype requires fastupdate = off")));
	if (indexInfo->ii_NumIndexAttrs != 1 || indexInfo->ii_IndexAttrNumbers[0] == 0)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("rgin research prototype supports one plain column")));

	memset(&bs, 0, sizeof(bs));
	initGinState(&bs.gs, index);

	MetaBuffer = GinNewBuffer(index);
	RootBuffer = GinNewBuffer(index);
	START_CRIT_SECTION();
	GinInitMetabuffer(MetaBuffer);
	MarkBufferDirty(MetaBuffer);
	GinInitBuffer(RootBuffer, GIN_LEAF);
	MarkBufferDirty(RootBuffer);
	UnlockReleaseBuffer(MetaBuffer);
	UnlockReleaseBuffer(RootBuffer);
	END_CRIT_SECTION();
	bs.stats.nEntryPages++;

	bs.tmpCtx = AllocSetContextCreate(CurrentMemoryContext, "rgin build",
									  ALLOCSET_DEFAULT_SIZES);
	bs.funcCtx = AllocSetContextCreate(CurrentMemoryContext, "rgin build tuple",
									   ALLOCSET_DEFAULT_SIZES);
	bs.accum.ginstate = &bs.gs;
	ginInitBA(&bs.accum);

	/* no sync scan: postings must arrive in TID order */
	reltuples = table_index_build_scan(heap, index, indexInfo, false, true,
									   rgin_build_cb, &bs, NULL);

	memset(&build_info, 0, sizeof(build_info));
	oldCtx = MemoryContextSwitchTo(bs.tmpCtx);
	ginBeginBAScan(&bs.accum);
	while ((list = ginGetBAEntry(&bs.accum, &attnum, &key, &category, &nlist)) != NULL)
	{
		CHECK_FOR_INTERRUPTS();
		ginEntryInsert(&bs.gs, attnum, key, category, list, nlist, &bs.stats);
		bs.npostings += nlist;
		build_info.terms++;
		if (rgin_build_evidence && category == GIN_CAT_NORM_KEY)
		{
			char	   *lex = VARDATA_ANY(DatumGetPointer(key));
			int			len = VARSIZE_ANY_EXHDR(DatumGetPointer(key));
			int			m = frontier_of(list, nlist, fbuf);

			/* one magic entry per term: frontier points, then the df item */
			ItemPointerSet(&fbuf[m], RGIN_DF_BLOCK_BASE + nlist, FirstOffsetNumber);
			insert_magic(&bs.gs, RGIN_TAG_FRONTIER, lex, len, fbuf, m + 1, &bs.stats);
			build_info.frontier_points += m;
			build_info.frontier_hist[Min(m, 64)]++;
		}
	}
	MemoryContextSwitchTo(oldCtx);
	insert_scalar(&bs.gs, "N", bs.N, &bs.stats);
	insert_scalar(&bs.gs, "S", bs.sumdl, &bs.stats);
	build_info.N = bs.N;
	build_info.sumdl = bs.sumdl;
	build_info.postings = bs.npostings;

	MemoryContextDelete(bs.funcCtx);
	MemoryContextDelete(bs.tmpCtx);

	bs.stats.nTotalPages = RelationGetNumberOfBlocks(index);
	ginUpdateStats(index, &bs.stats, true);
	if (RelationNeedsWAL(index))
		log_newpage_range(index, MAIN_FORKNUM, 0, RelationGetNumberOfBlocks(index), true);

	result = palloc_object(IndexBuildResult);
	result->heap_tuples = reltuples;
	result->index_tuples = bs.npostings;
	return result;
}

/* ---------------------------------------------------------------- insert (append-only) */

static bool
rgininsert(Relation index, Datum *values, bool *isnull,
		   ItemPointer ht_ctid, Relation heapRel,
		   IndexUniqueCheck checkUnique, bool indexUnchanged,
		   IndexInfo *indexInfo)
{
	GinState   *gs = (GinState *) indexInfo->ii_AmCache;
	MemoryContext old,
				ctx;
	TSVector	tsv;
	WordEntry  *we;
	int			dl;

	if (GinGetUseFastUpdate(index))
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("rgin research prototype requires fastupdate = off")));
	if (gs == NULL)
	{
		old = MemoryContextSwitchTo(indexInfo->ii_Context);
		gs = palloc_object(GinState);
		initGinState(gs, index);
		indexInfo->ii_AmCache = gs;
		MemoryContextSwitchTo(old);
	}
	if (isnull[0])
		return false;

	ctx = AllocSetContextCreate(CurrentMemoryContext, "rgin insert", ALLOCSET_DEFAULT_SIZES);
	old = MemoryContextSwitchTo(ctx);
	tsv = DatumGetTSVector(values[0]);
	dl = rgin_tsv_dl(tsv);
	we = ARRPTR(tsv);
	for (int i = 0; i < tsv->size; i++)
	{
		char	   *lex = STRPTR(tsv) + we[i].pos;
		RginPayload p = rgin_bm25_payload(rgin_tsv_tf(tsv, &we[i]), dl);
		ItemPointerData item = rgin_encode(ht_ctid, p);
		int			n;
		ItemPointer pts;
		bool		dominated = false;

		CHECK_FOR_INTERRUPTS();
		/*
		 * Widen the root frontier before the posting becomes reachable.  The
		 * frontier is a set of points; dominated points are never removed
		 * (append-only), which keeps the bound safe.
		 */
		pts = rgin_read_magic(index, gs, RGIN_TAG_FRONTIER, lex, we[i].len, &n);
		for (int j = 0; pts && j < n && !dominated; j++)
			dominated = RGIN_IS_POINT(&pts[j]) &&
				rgin_payload_dominates(rgin_item_to_point(&pts[j]), p);
		if (!dominated)
		{
			ItemPointerData pi = rgin_point_to_item(p);

			insert_magic(gs, RGIN_TAG_FRONTIER, lex, we[i].len, &pi, 1, NULL);
			widen_events++;
		}
		ginEntryInsert(gs, FirstOffsetNumber,
					   PointerGetDatum(cstring_to_text_with_len(lex, we[i].len)),
					   GIN_CAT_NORM_KEY, &item, 1, NULL);
	}
	MemoryContextSwitchTo(old);
	MemoryContextDelete(ctx);
	return false;
}

static IndexBulkDeleteResult *
rginbulkdelete(IndexVacuumInfo *info, IndexBulkDeleteResult *stats,
			   IndexBulkDeleteCallback callback, void *callback_state)
{
	ereport(ERROR,
			(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
			 errmsg("rgin research prototype is append-only: bulk delete is not supported")));
	return NULL;
}

/* ---------------------------------------------------------------- posting cursor */

typedef struct RginCursor
{
	bool		done;
	bool		isTree;
	GinBtreeData btree;
	Buffer		buf;			/* pinned, unlocked */
	ItemPointer items;
	int			nitems;
	int			pos;
	bool		rightmost;
	uint64		rbound;
} RginCursor;

typedef struct PoolEntry
{
	double		score;
	uint64		rk;
} PoolEntry;

typedef struct RginScanOpaqueData
{
	MemoryContext ctx;
	GinState	gs;
	RginQuery  *q;
	bool		empty;
	int			strategy;
	double	   *ub;
	int		   *order;
	int			phases_done;
	double		D;
	PoolEntry  *pool;
	int64		npool;
	int64		poolcap;
	bool		in_full;
	PoolEntry  *full;
	int64		nfull;
	double	   *contrib;
	bool	   *has;
	RginStats	st;
} RginScanOpaqueData;

typedef RginScanOpaqueData *RginScanOpaque;

static void
cursor_load(RginScanOpaque so, RginCursor *c, Page page, ItemPointerData adv)
{
	if (c->items)
		pfree(c->items);
	c->items = GinDataLeafPageGetItems(page, &c->nitems, adv);
	c->rightmost = GinPageRightMost(page);
	c->rbound = c->rightmost ? PG_UINT64_MAX : ip_u64(GinDataPageGetRightBound(page));
	c->pos = 0;
	so->st.postings += c->nitems;
	so->st.leaf_pages++;
}

static void
cursor_open(Relation index, RginScanOpaque so, RginCursor *c, int term)
{
	RginQuery  *q = so->q;
	BlockNumber root;
	Datum		key = PointerGetDatum(cstring_to_text_with_len(RGIN_QUERY_LEXEME(q, term),
															   q->terms[term].len));

	memset(c, 0, sizeof(*c));
	c->buf = InvalidBuffer;
	if (!lookup_entry(index, &so->gs, key, &root, &c->items, &c->nitems))
	{
		c->done = true;
		return;
	}
	if (root == InvalidBlockNumber)
	{
		so->st.postings += c->nitems;
		c->rightmost = true;
		c->done = (c->nitems == 0);
		return;
	}
	else
	{
		GinBtreeStack *stack = ginScanBeginPostingTree(&c->btree, index, root);
		ItemPointerData minItem;

		c->isTree = true;
		c->buf = stack->buffer;
		IncrBufferRefCount(c->buf);
		ItemPointerSetMin(&minItem);
		cursor_load(so, c, BufferGetPage(c->buf), minItem);
		LockBuffer(c->buf, GIN_UNLOCK);
		freeGinBtreeStack(stack);
	}
}

static void
cursor_close(RginCursor *c)
{
	if (BufferIsValid(c->buf))
		ReleaseBuffer(c->buf);
	c->buf = InvalidBuffer;
	if (c->items)
		pfree(c->items);
	c->items = NULL;
	c->done = true;
}

/* position on the first posting with heap row key >= target */
static bool
cursor_seek(Relation index, RginScanOpaque so, RginCursor *c, uint64 target)
{
	so->st.seeks++;
	for (;;)
	{
		uint64		lb;
		ItemPointerData adv;

		if (c->done)
			return false;
		if (c->pos < c->nitems)
		{
			/* sequential access: the next posting usually qualifies */
			if (rgin_rk(&c->items[c->pos]) >= target)
				return true;
			if (c->pos + 1 < c->nitems && rgin_rk(&c->items[c->pos + 1]) >= target)
			{
				c->pos++;
				return true;
			}
			if (rgin_rk(&c->items[c->nitems - 1]) >= target)
			{
				int			lo = c->pos,
							hi = c->nitems - 1;

				while (lo < hi)
				{
					int			mid = (lo + hi) / 2;

					if (rgin_rk(&c->items[mid]) >= target)
						hi = mid;
					else
						lo = mid + 1;
				}
				c->pos = lo;
				return true;
			}
			c->pos = c->nitems;
		}
		if (!c->isTree || c->rightmost)
		{
			cursor_close(c);
			return false;
		}
		lb = (target << 17) | 1;
		/*
		 * Items > adv are exactly those with heap row key >= target.  adv
		 * must be a valid item pointer (odd value), or GIN skips nothing.
		 */
		if (lb >= 3)
			adv = u64_ip(lb - 2);
		else
			ItemPointerSetMin(&adv);
		if (c->rbound < lb)
		{
			GinBtreeStack *stack;

			ReleaseBuffer(c->buf);
			c->btree.fullScan = false;
			c->btree.itemptr = u64_ip(lb);
			stack = ginFindLeafPage(&c->btree, true, false);
			c->buf = stack->buffer;
			IncrBufferRefCount(c->buf);
			cursor_load(so, c, BufferGetPage(c->buf), adv);
			LockBuffer(c->buf, GIN_UNLOCK);
			freeGinBtreeStack(stack);
			so->st.descents++;
		}
		else
		{
			LockBuffer(c->buf, GIN_SHARE);
			c->buf = ginStepRight(c->buf, index, GIN_SHARE);
			cursor_load(so, c, BufferGetPage(c->buf), adv);
			LockBuffer(c->buf, GIN_UNLOCK);
		}
	}
}

static inline ItemPointer
cursor_item(RginCursor *c)
{
	return &c->items[c->pos];
}

/* ---------------------------------------------------------------- pool */

static inline bool
better(const PoolEntry *a, const PoolEntry *b)
{
	return a->score > b->score || (a->score == b->score && a->rk < b->rk);
}

static void
pool_push(RginScanOpaque so, double score, uint64 rk)
{
	int64		i;

	if (so->npool == so->poolcap)
	{
		so->poolcap = Max(1024, so->poolcap * 2);
		so->pool = so->pool ? repalloc_huge(so->pool, sizeof(PoolEntry) * so->poolcap)
			: MemoryContextAllocHuge(so->ctx, sizeof(PoolEntry) * so->poolcap);
	}
	i = so->npool++;
	so->pool[i].score = score;
	so->pool[i].rk = rk;
	while (i > 0)
	{
		int64		p = (i - 1) / 2;
		PoolEntry	t;

		if (!better(&so->pool[i], &so->pool[p]))
			break;
		t = so->pool[p];
		so->pool[p] = so->pool[i];
		so->pool[i] = t;
		i = p;
	}
	so->st.pool_peak = Max(so->st.pool_peak, so->npool);
	so->st.pool_peak_bytes = Max(so->st.pool_peak_bytes, so->poolcap * (int64) sizeof(PoolEntry));
}

static void
sift_down(PoolEntry *h, int64 n, int64 i)
{
	for (;;)
	{
		int64		l = 2 * i + 1,
					r = l + 1,
					m = i;
		PoolEntry	t;

		if (l < n && better(&h[l], &h[m]))
			m = l;
		if (r < n && better(&h[r], &h[m]))
			m = r;
		if (m == i)
			break;
		t = h[m];
		h[m] = h[i];
		h[i] = t;
		i = m;
	}
}

static PoolEntry
heap_pop(PoolEntry *h, int64 *n)
{
	PoolEntry	top = h[0];

	h[0] = h[--(*n)];
	sift_down(h, *n, 0);
	return top;
}

static PoolEntry
pool_pop(RginScanOpaque so)
{
	return heap_pop(so->pool, &so->npool);
}

/* exact score of a document from per-term contributions, datum term order */
static inline double
sum_score(RginScanOpaque so)
{
	double		s = 0.0;

	for (int i = 0; i < so->q->nterms; i++)
		if (so->has[i])
			s += so->contrib[i];
	return s;
}

/* ---------------------------------------------------------------- FULL */

static void
run_full(IndexScanDesc scan)
{
	RginScanOpaque so = (RginScanOpaque) scan->opaque;
	RginQuery  *q = so->q;
	int			nt = q->nterms;
	RginCursor *cur = palloc0(sizeof(RginCursor) * nt);
	bool	   *valid = palloc(sizeof(bool) * nt);
	int64		cap = 1024;

	instr_time	t0,
				t1;

	INSTR_TIME_SET_CURRENT(t0);
	so->full = MemoryContextAllocHuge(so->ctx, sizeof(PoolEntry) * cap);
	so->nfull = 0;
	for (int i = 0; i < nt; i++)
	{
		cursor_open(scan->indexRelation, so, &cur[i], i);
		valid[i] = cursor_seek(scan->indexRelation, so, &cur[i], 0);
	}
	for (;;)
	{
		uint64		d = PG_UINT64_MAX;

		CHECK_FOR_INTERRUPTS();
		for (int i = 0; i < nt; i++)
			if (valid[i])
				d = Min(d, rgin_rk(cursor_item(&cur[i])));
		if (d == PG_UINT64_MAX)
			break;
		for (int i = 0; i < nt; i++)
		{
			so->has[i] = false;
			if (valid[i] && rgin_rk(cursor_item(&cur[i])) == d)
			{
				so->has[i] = true;
				so->contrib[i] = rgin_contrib(rgin_payload(cursor_item(&cur[i])),
											  q->terms[i].idf, q);
				so->st.contribs++;
				valid[i] = cursor_seek(scan->indexRelation, so, &cur[i], d + 1);
			}
		}
		if (so->nfull == cap)
		{
			cap *= 2;
			so->full = repalloc_huge(so->full, sizeof(PoolEntry) * cap);
		}
		so->full[so->nfull].score = sum_score(so);
		so->full[so->nfull].rk = d;
		so->nfull++;
	}
	for (int i = 0; i < nt; i++)
		cursor_close(&cur[i]);
	INSTR_TIME_SET_CURRENT(t1);
	INSTR_TIME_SUBTRACT(t1, t0);
	so->st.full_merge_ms += INSTR_TIME_GET_MILLISEC(t1);
	INSTR_TIME_SET_CURRENT(t0);
	for (int64 i = so->nfull / 2 - 1; i >= 0; i--)
		sift_down(so->full, so->nfull, i);
	INSTR_TIME_SET_CURRENT(t1);
	INSTR_TIME_SUBTRACT(t1, t0);
	so->st.full_sort_ms += INSTR_TIME_GET_MILLISEC(t1);
	so->st.docs_scored += so->nfull;
	so->st.full_docs = so->nfull;
	so->in_full = true;
}

/* ---------------------------------------------------------------- C (incremental) */

/* returns false if the pool limit was exceeded */
static bool
run_phase(IndexScanDesc scan)
{
	RginScanOpaque so = (RginScanOpaque) scan->opaque;
	Relation	index = scan->indexRelation;
	RginQuery  *q = so->q;
	int			nt = q->nterms;
	int			j = so->phases_done;
	int			T = so->order[j];
	RginCursor *cur = palloc0(sizeof(RginCursor) * nt);
	int64		limit = (int64) rgin_pool_limit_kb * 1024;
	bool		ok = true;
	bool		valid;
	instr_time	t0,
				t1;

	INSTR_TIME_SET_CURRENT(t0);

	for (int i = 0; i < nt; i++)
		cursor_open(index, so, &cur[i], i);

	for (valid = cursor_seek(index, so, &cur[T], 0); valid;)
	{
		ItemPointer it = cursor_item(&cur[T]);
		uint64		d = rgin_rk(it);
		bool		seen = false;

		CHECK_FOR_INTERRUPTS();
		/* documents containing an earlier-phase term are already exact */
		for (int e = 0; e < j && !seen; e++)
		{
			RginCursor *c = &cur[so->order[e]];

			if (cursor_seek(index, so, c, d) && rgin_rk(cursor_item(c)) == d)
				seen = true;
		}
		if (!seen)
		{
			for (int i = 0; i < nt; i++)
				so->has[i] = false;
			so->has[T] = true;
			so->contrib[T] = rgin_contrib(rgin_payload(it), q->terms[T].idf, q);
			so->st.contribs++;
			for (int l = j + 1; l < nt; l++)
			{
				int			t = so->order[l];
				RginCursor *c = &cur[t];

				if (cursor_seek(index, so, c, d) && rgin_rk(cursor_item(c)) == d)
				{
					so->has[t] = true;
					so->contrib[t] = rgin_contrib(rgin_payload(cursor_item(c)),
												  q->terms[t].idf, q);
					so->st.contribs++;
				}
			}
			pool_push(so, sum_score(so), d);
			so->st.docs_scored++;
			if (so->poolcap * (int64) sizeof(PoolEntry) > limit)
			{
				ok = false;
				break;
			}
		}
		valid = cursor_seek(index, so, &cur[T], d + 1);
	}
	for (int i = 0; i < nt; i++)
		cursor_close(&cur[i]);
	INSTR_TIME_SET_CURRENT(t1);
	INSTR_TIME_SUBTRACT(t1, t0);
	so->st.phase_ms += INSTR_TIME_GET_MILLISEC(t1);
	if (!ok)
		return false;

	so->phases_done++;
	so->st.phases = so->phases_done;
	so->D = 0.0;
	for (int l = so->phases_done; l < nt; l++)
		so->D += so->ub[so->order[l]];
	return true;
}

/* ---------------------------------------------------------------- AM scan API */

static int
order_cmp_arg(const void *a, const void *b, void *arg)
{
	const double *ub = arg;
	int			x = *(const int *) a,
				y = *(const int *) b;

	if (ub[x] > ub[y])
		return -1;
	if (ub[x] < ub[y])
		return 1;
	return x - y;
}

static void
save_stats(RginScanOpaque so)
{
	if (so->q)
	{
		last_stats = so->st;
		last_stats_valid = true;
	}
}

static IndexScanDesc
rginbeginscan(Relation index, int nkeys, int norderbys)
{
	IndexScanDesc scan = RelationGetIndexScan(index, nkeys, norderbys);
	RginScanOpaque so = palloc0(sizeof(RginScanOpaqueData));

	so->ctx = AllocSetContextCreate(CurrentMemoryContext, "rgin scan",
									ALLOCSET_DEFAULT_SIZES);
	initGinState(&so->gs, index);
	scan->opaque = so;
	if (norderbys > 0)
	{
		scan->xs_orderbyvals = palloc0(sizeof(Datum) * norderbys);
		scan->xs_orderbynulls = palloc(sizeof(bool) * norderbys);
		memset(scan->xs_orderbynulls, true, sizeof(bool) * norderbys);
	}
	return scan;
}

static bool
same_terms(RginQuery *a, RginQuery *b)
{
	if (a->nterms != b->nterms)
		return false;
	for (int i = 0; i < a->nterms; i++)
		if (a->terms[i].len != b->terms[i].len ||
			memcmp(RGIN_QUERY_LEXEME(a, i), RGIN_QUERY_LEXEME(b, i), a->terms[i].len) != 0)
			return false;
	return true;
}

static void
rginrescan(IndexScanDesc scan, ScanKey keys, int nkeys,
		   ScanKey orderbys, int norderbys)
{
	RginScanOpaque so = (RginScanOpaque) scan->opaque;
	MemoryContext old;
	RginQuery  *q;

	save_stats(so);
	MemoryContextReset(so->ctx);
	memset(&so->st, 0, sizeof(so->st));
	so->q = NULL;
	so->pool = NULL;
	so->npool = so->poolcap = 0;
	so->full = NULL;
	so->nfull = 0;
	so->in_full = false;
	so->phases_done = 0;
	so->empty = false;

	if (norderbys != 1 || orderbys[0].sk_flags & SK_ISNULL)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("rgin scans require exactly one ORDER BY <=> bm25query")));

	old = MemoryContextSwitchTo(so->ctx);
	q = DatumGetRginQuery(orderbys[0].sk_argument);
	so->q = palloc(VARSIZE(q));
	memcpy(so->q, q, VARSIZE(q));
	q = so->q;
	for (int i = 0; i < nkeys; i++)
	{
		if (keys[i].sk_flags & SK_ISNULL)
		{
			so->empty = true;
			continue;
		}
		if (!same_terms(DatumGetRginQuery(keys[i].sk_argument), q))
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("rgin research prototype: @@ and <=> must use the same query terms")));
	}

	so->contrib = palloc0(sizeof(double) * Max(q->nterms, 1));
	so->has = palloc0(sizeof(bool) * Max(q->nterms, 1));
	so->ub = palloc0(sizeof(double) * Max(q->nterms, 1));
	so->order = palloc0(sizeof(int) * Max(q->nterms, 1));

	so->strategy = rgin_strategy;
	if (so->strategy == RGIN_STRATEGY_AUTO)
		so->strategy = (q->nterms <= 2) ? RGIN_STRATEGY_C : RGIN_STRATEGY_FULL;
	so->st.strategy = so->strategy == RGIN_STRATEGY_C ? "c" : "full";
	so->st.nterms = q->nterms;

	/* root bounds from the stored frontier (C only) */
	if (so->strategy == RGIN_STRATEGY_C)
	{
		for (int i = 0; i < q->nterms; i++)
		{
			int			n;
			ItemPointer pts = rgin_read_magic(scan->indexRelation, &so->gs, RGIN_TAG_FRONTIER,
											  RGIN_QUERY_LEXEME(q, i), q->terms[i].len, &n);

			so->order[i] = i;
			if (pts == NULL)
			{
				/* no stored frontier: weakest safe bound, contrib <= idf*(k1+1) */
				so->ub[i] = q->terms[i].idf * (q->k1 + 1.0);
				continue;
			}
			so->ub[i] = 0.0;
			for (int j = 0; j < n; j++)
			{
				if (!RGIN_IS_POINT(&pts[j]))
					continue;
				so->ub[i] = Max(so->ub[i], rgin_contrib(rgin_item_to_point(&pts[j]),
														q->terms[i].idf, q));
				so->st.bound_evals++;
			}
		}
		qsort_arg(so->order, q->nterms, sizeof(int), order_cmp_arg, so->ub);
		so->D = 0.0;
		for (int i = 0; i < q->nterms; i++)
			so->D += so->ub[so->order[i]];
	}
	MemoryContextSwitchTo(old);
}

static void
verify_emit(IndexScanDesc scan, double score)
{
	RginScanOpaque so = (RginScanOpaque) scan->opaque;
	Relation	heap = scan->heapRelation;
	HeapTupleData tup;
	Buffer		buf = InvalidBuffer;
	bool		isnull;
	Datum		d;
	double		hs;

	if (heap == NULL)
		return;
	tup.t_self = scan->xs_heaptid;
	if (!heap_fetch(heap, SnapshotAny, &tup, &buf, true))
	{
		if (BufferIsValid(buf))
			ReleaseBuffer(buf);
		elog(ERROR, "rgin verify: heap tuple (%u,%u) not found",
			 ItemPointerGetBlockNumber(&tup.t_self), ItemPointerGetOffsetNumber(&tup.t_self));
	}
	d = heap_getattr(&tup, scan->indexRelation->rd_index->indkey.values[0],
					 RelationGetDescr(heap), &isnull);
	hs = isnull ? -1.0 : rgin_tsv_score(DatumGetTSVector(d), so->q);
	ReleaseBuffer(buf);
	if (memcmp(&hs, &score, sizeof(double)) != 0)
		elog(ERROR, "rgin verify: index score %.17g != heap score %.17g at (%u,%u)",
			 score, hs, ItemPointerGetBlockNumber(&tup.t_self),
			 ItemPointerGetOffsetNumber(&tup.t_self));
}

static bool
emit(IndexScanDesc scan, PoolEntry e)
{
	RginScanOpaque so = (RginScanOpaque) scan->opaque;

	rk_to_tid(e.rk, &scan->xs_heaptid);
	scan->xs_recheck = false;
	scan->xs_recheckorderby = false;
	scan->xs_orderbyvals[0] = Float8GetDatum(-e.score);
	scan->xs_orderbynulls[0] = false;
	so->st.emitted++;
	if (rgin_verify)
		verify_emit(scan, e.score);
	return true;
}

static bool
rgingettuple(IndexScanDesc scan, ScanDirection dir)
{
	RginScanOpaque so = (RginScanOpaque) scan->opaque;
	MemoryContext old;
	bool		result = false;

	if (so->empty || so->q == NULL || so->q->nterms == 0)
		return false;
	old = MemoryContextSwitchTo(so->ctx);

	if (so->strategy == RGIN_STRATEGY_FULL && !so->in_full)
		run_full(scan);

	for (;;)
	{
		if (so->in_full)
		{
			if (so->nfull > 0)
				result = emit(scan, heap_pop(so->full, &so->nfull));
			break;
		}
		if (so->npool > 0)
		{
			int			nt = so->q->nterms;
			double		D = so->D;

			so->st.bound_evals++;
			if (so->phases_done == nt ||
				so->pool[0].score > D + fabs(D) * 1e-12 * (nt + 1))
			{
				result = emit(scan, pool_pop(so));
				break;
			}
		}
		else if (so->phases_done == so->q->nterms)
			break;

		if (!run_phase(scan))
		{
			/* pool limit: exact fallback, skip what was already emitted */
			int64		emitted = so->st.emitted;

			so->st.fallback = true;
			if (so->pool)
				pfree(so->pool);
			so->pool = NULL;
			so->npool = so->poolcap = 0;
			run_full(scan);
			for (int64 i = 0; i < emitted && so->nfull > 0; i++)
				(void) heap_pop(so->full, &so->nfull);
		}
	}
	MemoryContextSwitchTo(old);
	return result;
}

static void
rginendscan(IndexScanDesc scan)
{
	RginScanOpaque so = (RginScanOpaque) scan->opaque;

	save_stats(so);
	MemoryContextDelete(so->ctx);
	pfree(so);
	scan->opaque = NULL;
}

/* ---------------------------------------------------------------- planner / validate */

static void
rgincostestimate(PlannerInfo *root, IndexPath *path, double loop_count,
				 Cost *indexStartupCost, Cost *indexTotalCost,
				 Selectivity *indexSelectivity, double *indexCorrelation,
				 double *indexPages)
{
	gincostestimate(root, path, loop_count, indexStartupCost, indexTotalCost,
					indexSelectivity, indexCorrelation, indexPages);
	/* only ordered scans are implemented */
	if (path->indexorderbys == NIL)
	{
		*indexStartupCost = 1.0e10;
		*indexTotalCost = 1.0e10;
	}
}

static bool
rginvalidate(Oid opclassoid)
{
	return true;
}

/* ---------------------------------------------------------------- handler, SQL API */

PG_FUNCTION_INFO_V1(rgin_handler);
PG_FUNCTION_INFO_V1(rgin_last_stats);
PG_FUNCTION_INFO_V1(rgin_build_info);
PG_FUNCTION_INFO_V1(rgin_widen_events);
PG_FUNCTION_INFO_V1(rgin_term_frontier);
PG_FUNCTION_INFO_V1(rgin_term_frontier_points);

Datum
rgin_handler(PG_FUNCTION_ARGS)
{
	static const IndexAmRoutine amroutine = {
		.type = T_IndexAmRoutine,
		.amstrategies = 0,
		.amsupport = GINNProcs,
		.amoptsprocnum = GIN_OPTIONS_PROC,
		.amcanorder = false,
		.amcanorderbyop = true,
		.amcanhash = false,
		.amconsistentequality = false,
		.amconsistentordering = false,
		.amcanbackward = false,
		.amcanunique = false,
		.amcanmulticol = false,
		.amoptionalkey = false,
		.amsearcharray = false,
		.amsearchnulls = false,
		.amstorage = true,
		.amclusterable = false,
		.ampredlocks = false,
		.amcanparallel = false,
		.amcanbuildparallel = false,
		.amcaninclude = false,
		.amusemaintenanceworkmem = true,
		.amsummarizing = false,
		.amparallelvacuumoptions = VACUUM_OPTION_NO_PARALLEL,
		.amkeytype = InvalidOid,

		.ambuild = rginbuild,
		.ambuildempty = ginbuildempty,
		.aminsert = rgininsert,
		.aminsertcleanup = NULL,
		.ambulkdelete = rginbulkdelete,
		.amvacuumcleanup = ginvacuumcleanup,
		.amcanreturn = NULL,
		.amcostestimate = rgincostestimate,
		.amgettreeheight = NULL,
		.amoptions = ginoptions,
		.amproperty = NULL,
		.ambuildphasename = NULL,
		.amvalidate = rginvalidate,
		.amadjustmembers = NULL,
		.ambeginscan = rginbeginscan,
		.amrescan = rginrescan,
		.amgettuple = rgingettuple,
		.amgetbitmap = NULL,
		.amendscan = rginendscan,
		.ammarkpos = NULL,
		.amrestrpos = NULL,
		.amestimateparallelscan = NULL,
		.aminitparallelscan = NULL,
		.amparallelrescan = NULL,
	};

	PG_RETURN_POINTER(&amroutine);
}

bool
rgin_is_rgin_index(Relation index)
{
	return index->rd_indam && index->rd_indam->amgettuple == rgingettuple;
}

Datum
rgin_last_stats(PG_FUNCTION_ARGS)
{
	StringInfoData s;
	RginStats  *st = &last_stats;

	if (!last_stats_valid)
		PG_RETURN_NULL();
	initStringInfo(&s);
	appendStringInfo(&s,
					 "{\"strategy\":\"%s\",\"nterms\":%d,\"phases\":%d,"
					 "\"postings_decoded\":" INT64_FORMAT ",\"leaf_pages\":" INT64_FORMAT
					 ",\"descents\":" INT64_FORMAT ",\"seeks\":" INT64_FORMAT
					 ",\"docs_scored\":" INT64_FORMAT ",\"contribs\":" INT64_FORMAT
					 ",\"bound_evals\":" INT64_FORMAT ",\"pool_peak\":" INT64_FORMAT
					 ",\"pool_peak_bytes\":" INT64_FORMAT ",\"emitted\":" INT64_FORMAT
					 ",\"fallback\":%s,\"full_docs\":" INT64_FORMAT
					 ",\"full_merge_ms\":%.3f,\"full_sort_ms\":%.3f,\"phase_ms\":%.3f}",
					 st->strategy ? st->strategy : "", st->nterms, st->phases,
					 st->postings, st->leaf_pages, st->descents, st->seeks,
					 st->docs_scored, st->contribs, st->bound_evals, st->pool_peak,
					 st->pool_peak_bytes, st->emitted, st->fallback ? "true" : "false",
					 st->full_docs, st->full_merge_ms, st->full_sort_ms, st->phase_ms);
	PG_RETURN_TEXT_P(cstring_to_text(s.data));
}

Datum
rgin_build_info(PG_FUNCTION_ARGS)
{
	StringInfoData s;

	initStringInfo(&s);
	appendStringInfo(&s, "{\"N\":" INT64_FORMAT ",\"sumdl\":" INT64_FORMAT
					 ",\"terms\":" INT64_FORMAT ",\"postings\":" INT64_FORMAT
					 ",\"frontier_points\":" INT64_FORMAT ",\"hist\":[",
					 build_info.N, build_info.sumdl, build_info.terms,
					 build_info.postings, build_info.frontier_points);
	for (int i = 0; i <= 64; i++)
		appendStringInfo(&s, "%s" INT64_FORMAT, i ? "," : "", build_info.frontier_hist[i]);
	appendStringInfoString(&s, "]}");
	PG_RETURN_TEXT_P(cstring_to_text(s.data));
}

Datum
rgin_widen_events(PG_FUNCTION_ARGS)
{
	PG_RETURN_INT64(widen_events);
}

/* number of stored root-frontier points of a term (-1 if none) */
Datum
rgin_term_frontier(PG_FUNCTION_ARGS)
{
	Oid			indexoid = PG_GETARG_OID(0);
	text	   *lex = PG_GETARG_TEXT_PP(1);
	Relation	index = index_open(indexoid, AccessShareLock);
	GinState	gs;
	int			n;
	ItemPointer pts;

	if (!rgin_is_rgin_index(index))
		elog(ERROR, "not an rgin index");
	initGinState(&gs, index);
	pts = rgin_read_magic(index, &gs, RGIN_TAG_FRONTIER, VARDATA_ANY(lex),
						  VARSIZE_ANY_EXHDR(lex), &n);
	index_close(index, NoLock);
	if (pts == NULL)
		PG_RETURN_INT32(-1);
	{
		int			m = 0;

		for (int j = 0; j < n; j++)
			m += RGIN_IS_POINT(&pts[j]);
		PG_RETURN_INT32(m);
	}
}

/* stored root-frontier points of a term as tf_byte*256 + norm_code */
Datum
rgin_term_frontier_points(PG_FUNCTION_ARGS)
{
	Oid			indexoid = PG_GETARG_OID(0);
	text	   *lex = PG_GETARG_TEXT_PP(1);
	Relation	index = index_open(indexoid, AccessShareLock);
	GinState	gs;
	int			n,
				m = 0;
	ItemPointer pts;
	Datum	   *d;

	if (!rgin_is_rgin_index(index))
		elog(ERROR, "not an rgin index");
	initGinState(&gs, index);
	pts = rgin_read_magic(index, &gs, RGIN_TAG_FRONTIER, VARDATA_ANY(lex),
						  VARSIZE_ANY_EXHDR(lex), &n);
	index_close(index, NoLock);
	d = palloc(sizeof(Datum) * Max(n, 1));
	for (int j = 0; pts && j < n; j++)
		if (RGIN_IS_POINT(&pts[j]))
			d[m++] = Int32GetDatum((int32) rgin_item_to_point(&pts[j]));
	PG_RETURN_ARRAYTYPE_P(construct_array_builtin(d, m, INT4OID));
}

void
_PG_init(void)
{
	rgin_bm25_init();
	DefineCustomEnumVariable("rgin.strategy", "Ranked scan strategy (full, c, auto).",
							 NULL, &rgin_strategy, RGIN_STRATEGY_AUTO, strategy_options,
							 PGC_USERSET, 0, NULL, NULL, NULL);
	DefineCustomIntVariable("rgin.pool_limit_kb", "C pool limit before exact FULL fallback.",
							NULL, &rgin_pool_limit_kb, 65536, 64, MAX_KILOBYTES,
							PGC_USERSET, GUC_UNIT_KB, NULL, NULL, NULL);
	DefineCustomBoolVariable("rgin.verify", "Check every emitted score against the heap tsvector.",
							 NULL, &rgin_verify, false, PGC_USERSET, 0, NULL, NULL, NULL);
	DefineCustomBoolVariable("rgin.build_evidence", "Store root frontier and df entries at build.",
							 NULL, &rgin_build_evidence, true, PGC_USERSET, 0, NULL, NULL, NULL);
	MarkGUCPrefixReserved("rgin");
}
