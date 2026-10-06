/*
 * rgin.c
 *		Research ranked GIN access method (M2 prototype).  Not for production.
 *
 * rgin is an AM wrapper over the GIN payload format (metapage version 3):
 *
 *	1. Posting payload.  Every posting is (heap TID, 2 opaque bytes); core
 *	   GIN stores them as P2 segments (TID stream, then a payload array).
 *
 *	2. Per-key metadata in the entry leaf tuple, computed by the opclass
 *	   hook (rgin_bm25.c): build-time df_G, and for posting-tree keys the
 *	   root Pareto frontier of payloads.  N_G and sum(dl)_G are the index
 *	   static metadata on the metapage.  Together they are the statistics
 *	   generation G of M0.7; inserts never change them.
 *
 *	3. Ordered scan.  amgettuple returns an exact score-ordered stream
 *	   (score desc, heap TID asc) without knowing LIMIT: either FULL
 *	   (decode all eligible postings, score, heap) or C (M0.6 incremental
 *	   phases over terms by decreasing root bound, nothing discarded).
 *
 * Research-only restrictions: fastupdate=off, single-column, serial build,
 * no bitmap scans, no partial match.  Bulk delete removes postings with
 * their payloads and keeps entry metadata (bounds stay safe, stale-high).
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
#include "catalog/pg_type.h"
#include "commands/vacuum.h"
#include "miscadmin.h"
#include "nodes/pathnodes.h"
#include "port/pg_crc32c.h"
#include "portability/instr_time.h"
#include "storage/bufmgr.h"
#include "tsearch/ts_type.h"
#include "utils/array.h"
#include "utils/builtins.h"
#include "utils/guc.h"
#include "utils/index_selfuncs.h"
#include "utils/injection_point.h"
#include "utils/memutils.h"
#include "utils/rel.h"
#include "utils/snapmgr.h"

#include "rgin.h"

PG_MODULE_MAGIC_EXT(.name = "rgin",.version = "2.0-m2");

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

enum
{
	RGIN_DECODE_PAGE,			/* decode from covering segment to end of page */
	RGIN_DECODE_SEGMENT			/* decode exactly one segment at a time */
};

static const struct config_enum_entry decode_options[] = {
	{"page", RGIN_DECODE_PAGE, false},
	{"segment", RGIN_DECODE_SEGMENT, false},
	{NULL, 0, false}
};

static int	rgin_strategy = RGIN_STRATEGY_AUTO;
static int	rgin_decode = RGIN_DECODE_PAGE;
static int	rgin_pool_limit_kb = 65536;
static bool rgin_verify = false;

#define W	RGIN_PAYLOAD_WIDTH

/* heap TID as a sortable 64-bit key */
static inline uint64
tid_key(const ItemPointerData *ip)
{
	return ((uint64) GinItemPointerGetBlockNumber(ip) << 16) |
		GinItemPointerGetOffsetNumber(ip);
}

static inline void
key_to_tid(uint64 k, ItemPointer tid)
{
	ItemPointerSet(tid, (BlockNumber) (k >> 16), (OffsetNumber) (k & 0xffff));
}

/*
 * Largest item pointer that sorts before key k, as GIN's advancePast hint
 * ("items > advancePast").  Invalid (no skipping) when k is the first TID.
 */
static inline ItemPointerData
advance_past(uint64 k)
{
	ItemPointerData ip;
	BlockNumber blk = (BlockNumber) (k >> 16);
	OffsetNumber off = (OffsetNumber) (k & 0xffff);

	if (off > 1)
		ItemPointerSet(&ip, blk, off - 1);
	else if (blk > 0)
		ItemPointerSet(&ip, blk - 1, 0xffff);
	else
		ItemPointerSetInvalid(&ip);
	return ip;
}

static bool
rgin_fastupdate(Relation index)
{
	return index->rd_options ? ((GinOptions *) index->rd_options)->useFastUpdate
		: GIN_DEFAULT_USE_FASTUPDATE;
}

/* ---------------------------------------------------------------- state, lookup */

void
rgin_init_state(GinState *gs, Relation index)
{
	GinMetaPageExt ext;

	initGinState(gs, index);
	if (!ginGetMetaExt(index, &ext) || ext.payloadWidth != W)
		ereport(ERROR,
				(errcode(ERRCODE_INDEX_CORRUPTED),
				 errmsg("index \"%s\" does not have the rgin payload format; REINDEX it",
						RelationGetRelationName(index))));
	gs->payloadWidth = W;
	gs->payloadOps = &rgin_bm25_payload_ops;
}

void
rgin_read_index_meta(Relation index, RginIndexMeta *im)
{
	GinMetaPageExt ext;

	if (!ginGetMetaExt(index, &ext) || ext.staticMetaLen != sizeof(RginIndexMeta))
		ereport(ERROR,
				(errcode(ERRCODE_INDEX_CORRUPTED),
				 errmsg("index \"%s\" has no rgin statistics generation",
						RelationGetRelationName(index))));
	memcpy(im, ext.staticMeta, sizeof(RginIndexMeta));
}

/*
 * Look up a key.  Fills *ti with its metadata and either the posting tree
 * root or (if wantItems) the decoded inline postings.
 */
void
rgin_lookup_term(Relation index, GinState *gs, const char *lex, int len,
				 bool wantItems, RginTermInfo *ti)
{
	GinBtreeData btree;
	GinBtreeStack *stack;
	Datum		key = PointerGetDatum(cstring_to_text_with_len(lex, len));

	memset(ti, 0, sizeof(*ti));
	ti->root = InvalidBlockNumber;
	ginPrepareEntryScan(&btree, FirstOffsetNumber, key, GIN_CAT_NORM_KEY, gs);
	stack = ginFindLeafPage(&btree, true, false);
	if (btree.findItem(&btree, stack))
	{
		Page		page = BufferGetPage(stack->buffer);
		IndexTuple	itup = (IndexTuple) PageGetItem(page, PageGetItemId(page, stack->off));
		char	   *meta = GinItupGetMeta(itup, &ti->metalen);

		ti->found = true;
		rgin_meta_parse(meta, ti->metalen, &ti->meta);
		if (GinIsPostingTree(itup))
		{
			ti->isTree = true;
			ti->root = GinGetPostingTree(itup);
		}
		else
		{
			ti->nitems = GinGetNPosting(itup);
			if (wantItems && ti->nitems > 0)
				ti->items = ginReadTuplePayload(gs, FirstOffsetNumber, itup,
												&ti->nitems, &ti->payloads);
		}
	}
	LockBuffer(stack->buffer, GIN_UNLOCK);
	freeGinBtreeStack(stack);
}

/* ---------------------------------------------------------------- instrumentation */

typedef struct RginBuildInfo
{
	int64		N;
	int64		sumdl;
	int64		terms;
	int64		postings;
	int64		flushes;
	int64		trees;
} RginBuildInfo;

static RginBuildInfo build_info;

typedef struct RginInsertInfo
{
	int64		rows;
	int64		postings;
	int64		widen;			/* posting-tree entry tuple rewritten */
	int64		to_tree;		/* posting list converted to a tree */
} RginInsertInfo;

static RginInsertInfo insert_info;

typedef struct RginStats
{
	const char *strategy;
	const char *decode;
	int			nterms;
	int			phases;
	int64		postings;
	int64		segments;
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

/* move the accumulator contents into the index */
static void
rgin_flush(RginBuildState *bs)
{
	ItemPointerData *list;
	char	   *payloads;
	Datum		key;
	GinNullCategory category;
	uint32		nlist;
	OffsetNumber attnum;
	MemoryContext oldCtx = MemoryContextSwitchTo(bs->tmpCtx);

	ginBeginBAScan(&bs->accum);
	while ((list = ginGetBAEntryPayload(&bs->accum, &attnum, &key, &category,
										&nlist, &payloads)) != NULL)
	{
		int			flags;

		CHECK_FOR_INTERRUPTS();
		flags = ginEntryInsertPayload(&bs->gs, attnum, key, category,
									  list, payloads, nlist, &bs->stats);
		bs->npostings += nlist;
		build_info.terms++;
		if (flags & GIN_INSERT_TO_TREE)
			build_info.trees++;
	}
	MemoryContextSwitchTo(oldCtx);
	MemoryContextReset(bs->tmpCtx);
	ginInitBA(&bs->accum);
	build_info.flushes++;
}

static void
rgin_build_cb(Relation index, ItemPointer tid, Datum *values,
			  bool *isnull, bool tupleIsAlive, void *state)
{
	RginBuildState *bs = (RginBuildState *) state;
	MemoryContext old;
	TSVector	tsv;
	WordEntry  *we;
	int			dl;
	Datum	   *keys;
	GinNullCategory *cats;
	char	   *payloads;

	if (isnull[0])
		return;
	old = MemoryContextSwitchTo(bs->funcCtx);
	tsv = DatumGetTSVector(values[0]);
	dl = rgin_tsv_dl(tsv);
	bs->N++;
	bs->sumdl += dl;
	we = ARRPTR(tsv);
	keys = palloc(sizeof(Datum) * Max(tsv->size, 1));
	cats = palloc0(sizeof(GinNullCategory) * Max(tsv->size, 1));
	payloads = palloc(W * Max(tsv->size, 1));
	for (int i = 0; i < tsv->size; i++)
	{
		keys[i] = PointerGetDatum(cstring_to_text_with_len(STRPTR(tsv) + we[i].pos,
														   we[i].len));
		rgin_payload_put(payloads + i * W,
						 rgin_bm25_payload(rgin_tsv_tf(tsv, &we[i]), dl));
	}
	MemoryContextSwitchTo(bs->tmpCtx);
	ginInsertBAEntriesPayload(&bs->accum, tid, FirstOffsetNumber, keys, cats,
							  payloads, tsv->size);
	MemoryContextSwitchTo(old);
	MemoryContextReset(bs->funcCtx);

	if (bs->accum.allocatedMemory >= maintenance_work_mem * (Size) 1024)
		rgin_flush(bs);
}

static IndexBuildResult *
rginbuild(Relation heap, Relation index, IndexInfo *indexInfo)
{
	RginBuildState bs;
	Buffer		RootBuffer,
				MetaBuffer;
	double		reltuples;
	IndexBuildResult *result;
	RginIndexMeta im;

	if (RelationGetNumberOfBlocks(index) != 0)
		elog(ERROR, "index \"%s\" already contains data", RelationGetRelationName(index));
	if (rgin_fastupdate(index))
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("rgin research prototype requires fastupdate = off")));
	if (indexInfo->ii_NumIndexAttrs != 1 || indexInfo->ii_IndexAttrNumbers[0] == 0)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("rgin payload index must have exactly one plain column")));

	memset(&bs, 0, sizeof(bs));
	memset(&build_info, 0, sizeof(build_info));

	MetaBuffer = GinNewBuffer(index);
	RootBuffer = GinNewBuffer(index);
	START_CRIT_SECTION();
	GinInitMetabufferPayload(MetaBuffer, W);
	MarkBufferDirty(MetaBuffer);
	GinInitBuffer(RootBuffer, GIN_LEAF);
	MarkBufferDirty(RootBuffer);
	UnlockReleaseBuffer(MetaBuffer);
	UnlockReleaseBuffer(RootBuffer);
	END_CRIT_SECTION();
	bs.stats.nEntryPages++;

	rgin_init_state(&bs.gs, index);

	bs.tmpCtx = AllocSetContextCreate(CurrentMemoryContext, "rgin build",
									  ALLOCSET_DEFAULT_SIZES);
	bs.funcCtx = AllocSetContextCreate(CurrentMemoryContext, "rgin build tuple",
									   ALLOCSET_DEFAULT_SIZES);
	bs.accum.ginstate = &bs.gs;
	ginInitBA(&bs.accum);

	/* no sync scan: postings should arrive in TID order */
	reltuples = table_index_build_scan(heap, index, indexInfo, false, true,
									   rgin_build_cb, &bs, NULL);
	rgin_flush(&bs);

	MemoryContextDelete(bs.funcCtx);
	MemoryContextDelete(bs.tmpCtx);

	im.N = bs.N;
	im.sumdl = bs.sumdl;
	ginSetIndexStaticMeta(index, (char *) &im, sizeof(im));
	build_info.N = bs.N;
	build_info.sumdl = bs.sumdl;
	build_info.postings = bs.npostings;

	bs.stats.nTotalPages = RelationGetNumberOfBlocks(index);
	ginUpdateStats(index, &bs.stats, true);
	if (RelationNeedsWAL(index))
		log_newpage_range(index, MAIN_FORKNUM, 0, RelationGetNumberOfBlocks(index), true);

	result = palloc_object(IndexBuildResult);
	result->heap_tuples = reltuples;
	result->index_tuples = bs.npostings;
	return result;
}

/* like ginbuildempty, with the payload metapage */
static void
rginbuildempty(Relation index)
{
	Buffer		RootBuffer,
				MetaBuffer;

	MetaBuffer = ExtendBufferedRel(BMR_REL(index), INIT_FORKNUM, NULL,
								   EB_LOCK_FIRST | EB_SKIP_EXTENSION_LOCK);
	RootBuffer = ExtendBufferedRel(BMR_REL(index), INIT_FORKNUM, NULL,
								   EB_LOCK_FIRST | EB_SKIP_EXTENSION_LOCK);
	START_CRIT_SECTION();
	GinInitMetabufferPayload(MetaBuffer, W);
	{
		GinMetaPageExt *ext = GinPageGetMetaExt(BufferGetPage(MetaBuffer));
		RginIndexMeta im = {0, 0};

		memcpy(ext->staticMeta, &im, sizeof(im));
		ext->staticMetaLen = sizeof(im);
	}
	MarkBufferDirty(MetaBuffer);
	log_newpage_buffer(MetaBuffer, true);
	GinInitBuffer(RootBuffer, GIN_LEAF);
	MarkBufferDirty(RootBuffer);
	log_newpage_buffer(RootBuffer, false);
	END_CRIT_SECTION();
	UnlockReleaseBuffer(MetaBuffer);
	UnlockReleaseBuffer(RootBuffer);
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

	if (rgin_fastupdate(index))
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("rgin research prototype requires fastupdate = off")));
	if (gs == NULL)
	{
		old = MemoryContextSwitchTo(indexInfo->ii_Context);
		gs = palloc_object(GinState);
		rgin_init_state(gs, index);
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
		char		payload[W];
		int			flags;

		CHECK_FOR_INTERRUPTS();
		rgin_payload_put(payload, rgin_bm25_payload(rgin_tsv_tf(tsv, &we[i]), dl));
		flags = ginEntryInsertPayload(gs, FirstOffsetNumber,
									  PointerGetDatum(cstring_to_text_with_len(STRPTR(tsv) + we[i].pos,
																			   we[i].len)),
									  GIN_CAT_NORM_KEY, ht_ctid, payload, 1, NULL);
		insert_info.postings++;
		if (flags & GIN_INSERT_META_WIDENED)
			insert_info.widen++;
		if (flags & GIN_INSERT_TO_TREE)
			insert_info.to_tree++;
	}
	insert_info.rows++;
	MemoryContextSwitchTo(old);
	MemoryContextDelete(ctx);
	return false;
}

static IndexBulkDeleteResult *
rginbulkdelete(IndexVacuumInfo *info, IndexBulkDeleteResult *stats,
			   IndexBulkDeleteCallback callback, void *callback_state)
{
	GinMetaPageExt ext;

	if (!ginGetMetaExt(info->index, &ext) || ext.payloadWidth != W)
		ereport(ERROR,
				(errcode(ERRCODE_INDEX_CORRUPTED),
				 errmsg("index \"%s\" does not have the rgin payload format; REINDEX it",
						RelationGetRelationName(info->index))));

	/*
	 * Postings die with their payloads; entry metadata (df_G, frontier) is
	 * kept as is, so the frontier may become wider than the remaining
	 * postings, which keeps the bound safe.
	 */
	return ginbulkdeletePayload(info, stats, callback, callback_state, W);
}

/* ---------------------------------------------------------------- posting cursor */

typedef struct RginCursor
{
	bool		done;
	bool		isTree;
	GinBtreeData btree;			/* for descents in the posting tree */
	Buffer		buf;			/* current leaf, pinned, unlocked */
	bool		rightmost;
	uint64		rbound;			/* key of the page's right bound */
	/* decoded unit: items[pos .. nitems) */
	ItemPointer items;
	char	   *payloads;
	int			nitems;
	int			pos;
	/* segment mode: private copy of the leaf, next segment to decode */
	char	   *page;
	GinPostingList *seg;
	char	   *segend;
} RginCursor;

typedef struct PoolEntry
{
	double		score;
	uint64		key;
} PoolEntry;

typedef struct RginScanOpaqueData
{
	MemoryContext ctx;
	GinState	gs;
	RginQuery  *q;
	bool		empty;
	int			strategy;
	int			decode;
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
cursor_set_items(RginCursor *c, ItemPointer items, char *payloads, int n)
{
	if (c->items)
		pfree(c->items);
	if (c->payloads)
		pfree(c->payloads);
	c->items = items;
	c->payloads = payloads;
	c->nitems = n;
	c->pos = 0;
}

/* segment mode: decode the next segment of the page copy, if any */
static bool
cursor_next_segment(RginScanOpaque so, RginCursor *c)
{
	ItemPointer items;
	char	   *payloads;
	int			n;

	if (c->seg == NULL)
		return false;
	items = ginPostingListDecodePayload(c->seg, W, &n, &payloads);
	cursor_set_items(c, items, payloads, n);
	so->st.postings += n;
	so->st.segments++;
	c->seg = GinNextPostingListSegment(c->seg);
	if ((char *) c->seg >= c->segend)
		c->seg = NULL;
	return true;
}

/* load a leaf page (locked by the caller), skipping items <= adv */
static void
cursor_load(RginScanOpaque so, RginCursor *c, Page page, ItemPointerData adv)
{
	c->rightmost = GinPageRightMost(page);
	c->rbound = c->rightmost ? PG_UINT64_MAX : tid_key(GinDataPageGetRightBound(page));
	so->st.leaf_pages++;
	if (so->decode == RGIN_DECODE_PAGE)
	{
		ItemPointer items;
		char	   *payloads;
		int			n;
		char	   *endptr;
		GinPostingList *seg = GinDataLeafPageFindSegment(page, adv, &endptr);

		items = GinDataLeafPageGetItemsPayload(page, W, &n, adv, &payloads);
		cursor_set_items(c, items, payloads, n);
		so->st.postings += n;
		for (; seg && (char *) seg < endptr; seg = GinNextPostingListSegment(seg))
			so->st.segments++;
	}
	else
	{
		if (c->page == NULL)
			c->page = palloc(BLCKSZ);
		memcpy(c->page, page, BLCKSZ);
		c->seg = GinDataLeafPageFindSegment(c->page, adv, &c->segend);
		cursor_set_items(c, NULL, NULL, 0);
		(void) cursor_next_segment(so, c);
	}
}

static void
cursor_open(Relation index, RginScanOpaque so, RginCursor *c, int term)
{
	RginQuery  *q = so->q;
	RginTermInfo ti;

	memset(c, 0, sizeof(*c));
	c->buf = InvalidBuffer;
	rgin_lookup_term(index, &so->gs, RGIN_QUERY_LEXEME(q, term), q->terms[term].len,
					 true, &ti);
	if (!ti.found)
	{
		c->done = true;
		return;
	}
	if (!ti.isTree)
	{
		c->items = ti.items;
		c->payloads = ti.payloads;
		c->nitems = ti.nitems;
		so->st.postings += c->nitems;
		c->rightmost = true;
		c->done = (c->nitems == 0);
	}
	else
	{
		GinBtreeStack *stack = ginScanBeginPostingTree(&c->btree, index, ti.root);
		ItemPointerData minItem;

		c->isTree = true;
		c->buf = stack->buffer;
		IncrBufferRefCount(c->buf);
		ItemPointerSetInvalid(&minItem);
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
	cursor_set_items(c, NULL, NULL, 0);
	if (c->page)
		pfree(c->page);
	c->page = NULL;
	c->seg = NULL;
	c->done = true;
}

/* position on the first posting with TID key >= target */
static bool
cursor_seek(Relation index, RginScanOpaque so, RginCursor *c, uint64 target)
{
	so->st.seeks++;
	for (;;)
	{
		ItemPointerData adv;

		if (c->done)
			return false;
		if (c->pos < c->nitems)
		{
			/* sequential access: the next posting usually qualifies */
			if (tid_key(&c->items[c->pos]) >= target)
				return true;
			if (c->pos + 1 < c->nitems && tid_key(&c->items[c->pos + 1]) >= target)
			{
				c->pos++;
				return true;
			}
			if (tid_key(&c->items[c->nitems - 1]) >= target)
			{
				int			lo = c->pos,
							hi = c->nitems - 1;

				while (lo < hi)
				{
					int			mid = (lo + hi) / 2;

					if (tid_key(&c->items[mid]) >= target)
						hi = mid;
					else
						lo = mid + 1;
				}
				c->pos = lo;
				return true;
			}
			c->pos = c->nitems;
		}
		if (c->seg != NULL)
		{
			/* segment mode: skip segments wholly below target by header */
			GinPostingList *next = GinNextPostingListSegment(c->seg);

			while ((char *) next < c->segend && tid_key(&next->first) <= target)
			{
				c->seg = next;
				next = GinNextPostingListSegment(c->seg);
			}
			(void) cursor_next_segment(so, c);
			continue;
		}
		if (!c->isTree || c->rightmost)
		{
			cursor_close(c);
			return false;
		}
		adv = advance_past(target);
		if (c->rbound < target)
		{
			GinBtreeStack *stack;

			ReleaseBuffer(c->buf);
			c->btree.fullScan = false;
			key_to_tid(target, &c->btree.itemptr);
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
		/* next leaf loaded and pinned, no lock held */
		INJECTION_POINT("rgin-cursor-after-next-leaf", NULL);
	}
}

static inline uint64
cursor_key(RginCursor *c)
{
	return tid_key(&c->items[c->pos]);
}

static inline RginPayload
cursor_payload(RginCursor *c)
{
	return rgin_payload_get(c->payloads + c->pos * W);
}

/* ---------------------------------------------------------------- pool */

static inline bool
better(const PoolEntry *a, const PoolEntry *b)
{
	return a->score > b->score || (a->score == b->score && a->key < b->key);
}

static void
pool_push(RginScanOpaque so, double score, uint64 key)
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
	so->pool[i].key = key;
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
				d = Min(d, cursor_key(&cur[i]));
		if (d == PG_UINT64_MAX)
			break;
		for (int i = 0; i < nt; i++)
		{
			so->has[i] = false;
			if (valid[i] && cursor_key(&cur[i]) == d)
			{
				so->has[i] = true;
				so->contrib[i] = rgin_contrib(cursor_payload(&cur[i]), q->terms[i].idf, q);
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
		so->full[so->nfull].key = d;
		so->nfull++;
		if (so->nfull == 1)
			INJECTION_POINT("rgin-full-after-first-doc", NULL);
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
	if (j > 0)
		INJECTION_POINT("rgin-c-before-phase", NULL);

	for (int i = 0; i < nt; i++)
		cursor_open(index, so, &cur[i], i);

	for (valid = cursor_seek(index, so, &cur[T], 0); valid;)
	{
		uint64		d = cursor_key(&cur[T]);
		bool		seen = false;

		CHECK_FOR_INTERRUPTS();
		/* documents containing an earlier-phase term are already exact */
		for (int e = 0; e < j && !seen; e++)
		{
			RginCursor *c = &cur[so->order[e]];

			if (cursor_seek(index, so, c, d) && cursor_key(c) == d)
				seen = true;
		}
		if (!seen)
		{
			for (int i = 0; i < nt; i++)
				so->has[i] = false;
			so->has[T] = true;
			so->contrib[T] = rgin_contrib(cursor_payload(&cur[T]), q->terms[T].idf, q);
			so->st.contribs++;
			for (int l = j + 1; l < nt; l++)
			{
				int			t = so->order[l];
				RginCursor *c = &cur[t];

				if (cursor_seek(index, so, c, d) && cursor_key(c) == d)
				{
					so->has[t] = true;
					so->contrib[t] = rgin_contrib(cursor_payload(c), q->terms[t].idf, q);
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
	rgin_init_state(&so->gs, index);
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

/*
 * Root bound of one term: frontier maximum for a posting-tree key, exact
 * maximum over the inline postings otherwise.
 */
static double
term_bound(RginScanOpaque so, Relation index, int i)
{
	RginQuery  *q = so->q;
	RginTermInfo ti;
	double		ub = 0.0;

	rgin_lookup_term(index, &so->gs, RGIN_QUERY_LEXEME(q, i), q->terms[i].len,
					 true, &ti);
	if (!ti.found)
		return 0.0;
	if (ti.isTree)
	{
		if (ti.meta.npoints == 0)
			return q->terms[i].idf * (q->k1 + 1.0);	/* weakest safe bound */
		for (int j = 0; j < ti.meta.npoints; j++)
		{
			ub = Max(ub, rgin_contrib(ti.meta.points[j], q->terms[i].idf, q));
			so->st.bound_evals++;
		}
	}
	else
	{
		for (int j = 0; j < ti.nitems; j++)
		{
			ub = Max(ub, rgin_contrib(rgin_payload_get(ti.payloads + j * W),
									  q->terms[i].idf, q));
			so->st.bound_evals++;
		}
	}
	return ub;
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
	so->decode = rgin_decode;
	so->st.strategy = so->strategy == RGIN_STRATEGY_C ? "c" : "full";
	so->st.decode = so->decode == RGIN_DECODE_PAGE ? "page" : "segment";
	so->st.nterms = q->nterms;

	if (so->strategy == RGIN_STRATEGY_C)
	{
		for (int i = 0; i < q->nterms; i++)
		{
			so->order[i] = i;
			so->ub[i] = term_bound(so, scan->indexRelation, i);
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
	if (!heap_fetch(heap, scan->xs_snapshot, &tup, &buf, true))
	{
		/*
		 * Not visible to the scan, e.g. an aborted insert whose index entries
		 * may be partial after a crash.  The executor does not return it, so
		 * there is nothing to verify.
		 */
		if (BufferIsValid(buf))
			ReleaseBuffer(buf);
		return;
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

	key_to_tid(e.key, &scan->xs_heaptid);
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

/* ---------------------------------------------------------------- handler */

PG_FUNCTION_INFO_V1(rgin_handler);

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
		.ambuildempty = rginbuildempty,
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

/* ---------------------------------------------------------------- SQL inspection */

PG_FUNCTION_INFO_V1(rgin_last_stats);
PG_FUNCTION_INFO_V1(rgin_build_info);
PG_FUNCTION_INFO_V1(rgin_insert_info);
PG_FUNCTION_INFO_V1(rgin_term_meta);
PG_FUNCTION_INFO_V1(rgin_term_frontier_points);
PG_FUNCTION_INFO_V1(rgin_check);

Datum
rgin_last_stats(PG_FUNCTION_ARGS)
{
	StringInfoData s;
	RginStats  *st = &last_stats;

	if (!last_stats_valid)
		PG_RETURN_NULL();
	initStringInfo(&s);
	appendStringInfo(&s,
					 "{\"strategy\":\"%s\",\"decode\":\"%s\",\"nterms\":%d,\"phases\":%d,"
					 "\"postings_decoded\":" INT64_FORMAT ",\"segments_decoded\":" INT64_FORMAT
					 ",\"leaf_pages\":" INT64_FORMAT
					 ",\"descents\":" INT64_FORMAT ",\"seeks\":" INT64_FORMAT
					 ",\"docs_scored\":" INT64_FORMAT ",\"contribs\":" INT64_FORMAT
					 ",\"bound_evals\":" INT64_FORMAT ",\"pool_peak\":" INT64_FORMAT
					 ",\"pool_peak_bytes\":" INT64_FORMAT ",\"emitted\":" INT64_FORMAT
					 ",\"fallback\":%s,\"full_docs\":" INT64_FORMAT
					 ",\"full_merge_ms\":%.3f,\"full_sort_ms\":%.3f,\"phase_ms\":%.3f}",
					 st->strategy ? st->strategy : "", st->decode ? st->decode : "",
					 st->nterms, st->phases,
					 st->postings, st->segments, st->leaf_pages, st->descents, st->seeks,
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
					 ",\"flushes\":" INT64_FORMAT ",\"trees\":" INT64_FORMAT "}",
					 build_info.N, build_info.sumdl, build_info.terms,
					 build_info.postings, build_info.flushes, build_info.trees);
	PG_RETURN_TEXT_P(cstring_to_text(s.data));
}

Datum
rgin_insert_info(PG_FUNCTION_ARGS)
{
	StringInfoData s;

	initStringInfo(&s);
	appendStringInfo(&s, "{\"rows\":" INT64_FORMAT ",\"postings\":" INT64_FORMAT
					 ",\"widen\":" INT64_FORMAT ",\"to_tree\":" INT64_FORMAT "}",
					 insert_info.rows, insert_info.postings, insert_info.widen,
					 insert_info.to_tree);
	PG_RETURN_TEXT_P(cstring_to_text(s.data));
}

static Relation
open_rgin(Oid indexoid, GinState *gs)
{
	Relation	index = index_open(indexoid, AccessShareLock);

	if (!rgin_is_rgin_index(index))
		elog(ERROR, "\"%s\" is not an rgin index", RelationGetRelationName(index));
	rgin_init_state(gs, index);
	return index;
}

/* entry metadata of a key, as JSON (NULL if the key is absent) */
Datum
rgin_term_meta(PG_FUNCTION_ARGS)
{
	text	   *lex = PG_GETARG_TEXT_PP(1);
	GinState	gs;
	Relation	index = open_rgin(PG_GETARG_OID(0), &gs);
	RginTermInfo ti;
	StringInfoData s;

	rgin_lookup_term(index, &gs, VARDATA_ANY(lex), VARSIZE_ANY_EXHDR(lex), false, &ti);
	index_close(index, NoLock);
	if (!ti.found)
		PG_RETURN_NULL();
	initStringInfo(&s);
	appendStringInfo(&s, "{\"tree\":%s,\"nposting_inline\":%d,\"metalen\":%d,"
					 "\"has_static\":%s,\"df\":" INT64_FORMAT ",\"npoints\":%d}",
					 ti.isTree ? "true" : "false", ti.nitems, ti.metalen,
					 ti.meta.has_static ? "true" : "false", ti.meta.df, ti.meta.npoints);
	PG_RETURN_TEXT_P(cstring_to_text(s.data));
}

/* stored root-frontier points of a key as tf_byte*256 + norm_code */
Datum
rgin_term_frontier_points(PG_FUNCTION_ARGS)
{
	text	   *lex = PG_GETARG_TEXT_PP(1);
	GinState	gs;
	Relation	index = open_rgin(PG_GETARG_OID(0), &gs);
	RginTermInfo ti;
	Datum	   *d;

	rgin_lookup_term(index, &gs, VARDATA_ANY(lex), VARSIZE_ANY_EXHDR(lex), false, &ti);
	index_close(index, NoLock);
	d = palloc(sizeof(Datum) * Max(ti.meta.npoints, 1));
	for (int j = 0; j < ti.meta.npoints; j++)
		d[j] = Int32GetDatum((int32) ti.meta.points[j]);
	PG_RETURN_ARRAYTYPE_P(construct_array_builtin(d, ti.meta.npoints, INT4OID));
}

/*
 * rgin_check(index): walk the whole index and verify the format invariants:
 *	- interior entry tuples carry no metadata flag;
 *	- postings are in strictly increasing TID order within each key;
 *	- every payload of a posting-tree key is dominated by its root frontier;
 *	- metadata parses.
 * Returns counters and the number of violations as JSON.
 */
typedef struct CheckCounters
{
	int64		entry_pages;
	int64		interior_tuples;
	int64		interior_with_meta;
	int64		leaf_tuples;
	int64		tree_keys;
	int64		inline_keys;
	int64		keys_with_static;
	int64		meta_bytes;
	int64		frontier_points;
	int64		postings;
	int64		data_leaf_pages;
	int64		segments;
	int64		order_violations;
	int64		bound_violations;
	int64		tree_without_frontier;
	int64		segment_violations;
	int64		empty_tree_keys;
	int64		empty_inline_keys;
	pg_crc32c	meta_crc;
} CheckCounters;

/*
 * Structure of one payload segment: item count >= 1, payload area of
 * exactly nitems * W bytes after the TID stream, and a TID stream length
 * possible for nitems - 1 varbyte deltas.
 */
static bool
segment_ok(GinPostingList *seg)
{
	int			n = GinPayloadListGetNItems(seg);
	int			tidbytes = (int) seg->nbytes - (int) sizeof(uint16) - n * W;

	return n >= 1 && tidbytes >= n - 1 && tidbytes <= 7 * (n - 1);
}

static bool
covered(const RginMeta *m, RginPayload p)
{
	for (int i = 0; i < m->npoints; i++)
		if (rgin_payload_dominates(m->points[i], p))
			return true;
	return false;
}

static void
check_tree(Relation index, BlockNumber root, const RginMeta *m, CheckCounters *cc)
{
	Buffer		buf = ReadBuffer(index, root);
	uint64		prev = 0;
	bool		first = true;

	LockBuffer(buf, GIN_SHARE);
	/* descend to the leftmost leaf */
	while (!GinPageIsLeaf(BufferGetPage(buf)))
	{
		Page		page = BufferGetPage(buf);
		BlockNumber child = PostingItemGetBlockNumber(GinDataPageGetPostingItem(page, FirstOffsetNumber));

		UnlockReleaseBuffer(buf);
		buf = ReadBuffer(index, child);
		LockBuffer(buf, GIN_SHARE);
	}
	for (;;)
	{
		Page		page = BufferGetPage(buf);
		char	   *endptr;
		ItemPointerData inv;
		GinPostingList *seg;
		BlockNumber next;

		ItemPointerSetInvalid(&inv);
		seg = GinDataLeafPageFindSegment(page, inv, &endptr);
		cc->data_leaf_pages++;
		for (; seg && (char *) seg < endptr; seg = GinNextPostingListSegment(seg))
		{
			int			n;
			char	   *pl;
			ItemPointer items;

			cc->segments++;
			if (!segment_ok(seg))
			{
				cc->segment_violations++;
				continue;
			}
			items = ginPostingListDecodePayload(seg, W, &n, &pl);
			for (int i = 0; i < n; i++)
			{
				uint64		k = tid_key(&items[i]);

				if (!first && k <= prev)
					cc->order_violations++;
				first = false;
				prev = k;
				if (!covered(m, rgin_payload_get(pl + i * W)))
					cc->bound_violations++;
			}
			cc->postings += n;
			pfree(items);
			pfree(pl);
		}
		next = GinPageGetOpaque(page)->rightlink;
		UnlockReleaseBuffer(buf);
		if (next == InvalidBlockNumber)
			break;
		buf = ReadBuffer(index, next);
		LockBuffer(buf, GIN_SHARE);
	}
}

Datum
rgin_check(PG_FUNCTION_ARGS)
{
	GinState	gs;
	Relation	index = open_rgin(PG_GETARG_OID(0), &gs);
	CheckCounters cc;
	BlockNumber levelStart = GIN_ROOT_BLKNO;
	StringInfoData s;

	memset(&cc, 0, sizeof(cc));
	INIT_CRC32C(cc.meta_crc);
	for (;;)
	{
		BlockNumber blk = levelStart;
		BlockNumber firstChild = InvalidBlockNumber;
		bool		leafLevel = false;

		while (blk != InvalidBlockNumber)
		{
			Buffer		buf = ReadBuffer(index, blk);
			Page		page;
			OffsetNumber maxoff;

			LockBuffer(buf, GIN_SHARE);
			page = BufferGetPage(buf);
			maxoff = PageGetMaxOffsetNumber(page);
			leafLevel = GinPageIsLeaf(page);
			cc.entry_pages++;
			for (OffsetNumber off = FirstOffsetNumber; off <= maxoff; off++)
			{
				IndexTuple	itup = (IndexTuple) PageGetItem(page, PageGetItemId(page, off));

				if (!leafLevel)
				{
					cc.interior_tuples++;
					if (GinItupHasMeta(itup))
						cc.interior_with_meta++;
					if (off == FirstOffsetNumber && firstChild == InvalidBlockNumber)
						firstChild = GinGetDownlink(itup);
				}
				else
				{
					int			metalen;
					char	   *meta = GinItupGetMeta(itup, &metalen);
					RginMeta	m;

					rgin_meta_parse(meta, metalen, &m);
					{
						GinNullCategory cat;
						Datum		key = gintuple_get_key(&gs, itup, &cat);
						uint16		ml = metalen;

						if (cat == GIN_CAT_NORM_KEY)
							COMP_CRC32C(cc.meta_crc, VARDATA_ANY(DatumGetPointer(key)),
										VARSIZE_ANY_EXHDR(DatumGetPointer(key)));
						COMP_CRC32C(cc.meta_crc, &ml, sizeof(ml));
						if (metalen > 0)
							COMP_CRC32C(cc.meta_crc, meta, metalen);
					}
					cc.leaf_tuples++;
					cc.meta_bytes += metalen;
					cc.frontier_points += m.npoints;
					if (m.has_static)
						cc.keys_with_static++;
					if (GinIsPostingTree(itup))
					{
						int64		before = cc.postings;

						cc.tree_keys++;
						if (m.npoints == 0)
							cc.tree_without_frontier++;
						check_tree(index, GinGetPostingTree(itup), &m, &cc);
						if (cc.postings == before)
							cc.empty_tree_keys++;
					}
					else
					{
						int			n;
						char	   *pl;
						ItemPointer items;

						cc.inline_keys++;
						if (GinGetNPosting(itup) == 0)
						{
							cc.empty_inline_keys++;
							continue;
						}
						if (!segment_ok((GinPostingList *) GinGetPosting(itup)))
						{
							cc.segment_violations++;
							continue;
						}
						items = ginReadTuplePayload(&gs, FirstOffsetNumber, itup, &n, &pl);
						for (int i = 1; i < n; i++)
							if (tid_key(&items[i]) <= tid_key(&items[i - 1]))
								cc.order_violations++;
						cc.postings += n;
					}
				}
			}
			blk = GinPageGetOpaque(page)->rightlink;
			UnlockReleaseBuffer(buf);
		}
		if (leafLevel || firstChild == InvalidBlockNumber)
			break;
		levelStart = firstChild;
	}
	index_close(index, NoLock);
	FIN_CRC32C(cc.meta_crc);

	initStringInfo(&s);
	appendStringInfo(&s,
					 "{\"entry_pages\":" INT64_FORMAT ",\"interior_tuples\":" INT64_FORMAT
					 ",\"interior_with_meta\":" INT64_FORMAT ",\"leaf_tuples\":" INT64_FORMAT
					 ",\"tree_keys\":" INT64_FORMAT ",\"inline_keys\":" INT64_FORMAT
					 ",\"keys_with_static\":" INT64_FORMAT ",\"meta_bytes\":" INT64_FORMAT
					 ",\"frontier_points\":" INT64_FORMAT ",\"postings\":" INT64_FORMAT
					 ",\"data_leaf_pages\":" INT64_FORMAT ",\"segments\":" INT64_FORMAT
					 ",\"order_violations\":" INT64_FORMAT ",\"bound_violations\":" INT64_FORMAT
					 ",\"tree_without_frontier\":" INT64_FORMAT
					 ",\"segment_violations\":" INT64_FORMAT ",\"empty_tree_keys\":" INT64_FORMAT
					 ",\"empty_inline_keys\":" INT64_FORMAT ",\"meta_crc\":\"%08x\"}",
					 cc.entry_pages, cc.interior_tuples, cc.interior_with_meta,
					 cc.leaf_tuples, cc.tree_keys, cc.inline_keys, cc.keys_with_static,
					 cc.meta_bytes, cc.frontier_points, cc.postings, cc.data_leaf_pages,
					 cc.segments, cc.order_violations, cc.bound_violations,
					 cc.tree_without_frontier, cc.segment_violations, cc.empty_tree_keys,
					 cc.empty_inline_keys, (unsigned) cc.meta_crc);
	PG_RETURN_TEXT_P(cstring_to_text(s.data));
}

/*
 * rgin_debug_insert(index, lexeme, tid, payload): insert one posting with an
 * arbitrary payload.  Research test hook for the duplicate-TID invariant.
 */
PG_FUNCTION_INFO_V1(rgin_debug_insert);

Datum
rgin_debug_insert(PG_FUNCTION_ARGS)
{
	text	   *lex = PG_GETARG_TEXT_PP(1);
	ItemPointer tid = PG_GETARG_ITEMPOINTER(2);
	int32		p = PG_GETARG_INT32(3);
	GinState	gs;
	Relation	index = index_open(PG_GETARG_OID(0), RowExclusiveLock);
	char		payload[W];
	int			flags;

	if (!rgin_is_rgin_index(index))
		elog(ERROR, "\"%s\" is not an rgin index", RelationGetRelationName(index));
	rgin_init_state(&gs, index);
	rgin_payload_put(payload, (RginPayload) p);
	flags = ginEntryInsertPayload(&gs, FirstOffsetNumber,
								  PointerGetDatum(cstring_to_text_with_len(VARDATA_ANY(lex),
																		   VARSIZE_ANY_EXHDR(lex))),
								  GIN_CAT_NORM_KEY, tid, payload, 1, NULL);
	index_close(index, NoLock);
	PG_RETURN_INT32(flags);
}

/*
 * rgin_term_segments(index, lexeme): physical layout of a key's postings as
 * JSON: {"inline": n} or {"pages": [[blkno, [nitems, ...]], ...]}.
 */
PG_FUNCTION_INFO_V1(rgin_term_segments);

Datum
rgin_term_segments(PG_FUNCTION_ARGS)
{
	text	   *lex = PG_GETARG_TEXT_PP(1);
	GinState	gs;
	Relation	index = open_rgin(PG_GETARG_OID(0), &gs);
	RginTermInfo ti;
	StringInfoData s;

	rgin_lookup_term(index, &gs, VARDATA_ANY(lex), VARSIZE_ANY_EXHDR(lex), false, &ti);
	initStringInfo(&s);
	if (!ti.found)
		appendStringInfoString(&s, "null");
	else if (!ti.isTree)
		appendStringInfo(&s, "{\"inline\":%d}", ti.nitems);
	else
	{
		Buffer		buf = ReadBuffer(index, ti.root);
		bool		first = true;

		LockBuffer(buf, GIN_SHARE);
		while (!GinPageIsLeaf(BufferGetPage(buf)))
		{
			BlockNumber child = PostingItemGetBlockNumber(GinDataPageGetPostingItem(BufferGetPage(buf),
																				   FirstOffsetNumber));

			UnlockReleaseBuffer(buf);
			buf = ReadBuffer(index, child);
			LockBuffer(buf, GIN_SHARE);
		}
		appendStringInfoString(&s, "{\"pages\":[");
		for (;;)
		{
			Page		page = BufferGetPage(buf);
			char	   *endptr;
			ItemPointerData inv;
			GinPostingList *seg;
			BlockNumber next;

			ItemPointerSetInvalid(&inv);
			seg = GinDataLeafPageFindSegment(page, inv, &endptr);
			appendStringInfo(&s, "%s[%u,[", first ? "" : ",", BufferGetBlockNumber(buf));
			first = false;
			for (bool f2 = true; seg && (char *) seg < endptr; seg = GinNextPostingListSegment(seg), f2 = false)
				appendStringInfo(&s, "%s%d", f2 ? "" : ",", GinPayloadListGetNItems(seg));
			appendStringInfoString(&s, "]]");
			next = GinPageGetOpaque(page)->rightlink;
			UnlockReleaseBuffer(buf);
			if (next == InvalidBlockNumber)
				break;
			buf = ReadBuffer(index, next);
			LockBuffer(buf, GIN_SHARE);
		}
		appendStringInfoString(&s, "]}");
	}
	index_close(index, NoLock);
	PG_RETURN_TEXT_P(cstring_to_text(s.data));
}

void
_PG_init(void)
{
	rgin_bm25_init();
	DefineCustomEnumVariable("rgin.strategy", "Ranked scan strategy (full, c, auto).",
							 NULL, &rgin_strategy, RGIN_STRATEGY_AUTO, strategy_options,
							 PGC_USERSET, 0, NULL, NULL, NULL);
	DefineCustomEnumVariable("rgin.decode", "Posting decode unit (page: rest of page, segment: one segment).",
							 NULL, &rgin_decode, RGIN_DECODE_PAGE, decode_options,
							 PGC_USERSET, 0, NULL, NULL, NULL);
	DefineCustomIntVariable("rgin.pool_limit_kb", "C pool limit before exact FULL fallback.",
							NULL, &rgin_pool_limit_kb, 65536, 64, MAX_KILOBYTES,
							PGC_USERSET, GUC_UNIT_KB, NULL, NULL, NULL);
	DefineCustomBoolVariable("rgin.verify", "Check every emitted score against the heap tsvector.",
							 NULL, &rgin_verify, false, PGC_USERSET, 0, NULL, NULL, NULL);
	MarkGUCPrefixReserved("rgin");
}
