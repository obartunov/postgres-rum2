/*
 * rgin_bm25.c
 *		BM25 opclass side of the research ranked GIN (M2 prototype).
 *
 * Score definition (M0.7): exact relative to the statistics generation G
 * carried by the bm25query datum, computed on the stored encodings:
 *	tf byte  = min(#positions of the lexeme (1 if none), 255)
 *	norm     = SmallFloat byte of dl (Lucene intToByte4, rounds down),
 *			   dl = sum over lexemes of #positions (1 if none)
 * The index payload and the SQL operator both go through
 * rgin_bm25_payload() and rgin_contrib(), and sum contributions in datum
 * term order, so the two scores are bit-identical.
 */
#include "postgres.h"

#include <math.h>

#include "access/gin.h"
#include "access/relation.h"
#include "catalog/pg_type.h"
#include "port/pg_bitutils.h"
#include "tsearch/ts_type.h"
#include "tsearch/ts_utils.h"
#include "utils/builtins.h"
#include "utils/memutils.h"
#include "utils/rel.h"

#include "rgin.h"

/* ---------------------------------------------------------------- norm */

static double dl_table[256];
static int	num_free_values;

static int
long_to_int4(uint64 i)
{
	int			nbits;
	int			shift;

	if (i == 0)
		return 0;
	nbits = pg_leftmost_one_pos64(i) + 1;
	if (nbits < 4)
		return (int) i;
	shift = nbits - 4;
	return ((int) (i >> shift) & 0x07) | ((shift + 1) << 3);
}

static uint64
int4_to_long(int i)
{
	uint64		bits = i & 0x07;
	int			shift = (i >> 3) - 1;

	if (shift == -1)
		return bits;
	return (bits | 0x08) << shift;
}

static int
int_to_byte4(int i)
{
	if (i < num_free_values)
		return i;
	return num_free_values + long_to_int4((uint64) (i - num_free_values));
}

static int64
byte4_to_int(int b)
{
	if (b < num_free_values)
		return b;
	return num_free_values + (int64) int4_to_long(b - num_free_values);
}

void
rgin_bm25_init(void)
{
	num_free_values = 255 - long_to_int4((uint64) PG_INT32_MAX);
	for (int c = 0; c < 256; c++)
		dl_table[c] = (double) byte4_to_int(c);
}

/* ---------------------------------------------------------------- payload */

RginPayload
rgin_bm25_payload(int tf, int dl)
{
	int			tfb = Min(tf, 255);

	Assert(tf >= 1 && dl >= 0);
	return (RginPayload) ((tfb << 8) | int_to_byte4(dl));
}

int
rgin_tsv_tf(TSVector tsv, WordEntry *we)
{
	return we->haspos ? POSDATALEN(tsv, we) : 1;
}

int
rgin_tsv_dl(TSVector tsv)
{
	WordEntry  *we = ARRPTR(tsv);
	int			dl = 0;

	for (int i = 0; i < tsv->size; i++)
		dl += rgin_tsv_tf(tsv, &we[i]);
	return dl;
}

/* summary order: higher tf and lower norm code dominate */
bool
rgin_payload_dominates(RginPayload a, RginPayload b)
{
	return (a >> 8) >= (b >> 8) && (a & 0xff) <= (b & 0xff);
}

/*
 * Contribution of one term.  Written as w - w/(1 + tf/K) so that it is
 * monotone (nondecreasing in tf, nonincreasing in dl) in floating point;
 * the root bound relies on that.
 */
double
rgin_contrib(RginPayload p, double idf, const RginQuery *q)
{
	double		tf = (double) (p >> 8);
	double		dl = dl_table[p & 0xff];
	double		K = q->k1 * (1.0 - q->b + q->b * dl / q->avgdl);
	double		w = idf * (q->k1 + 1.0);

	if (K == 0.0)
		return w;
	return w - w / (1.0 + tf / K);
}

/* ---------------------------------------------------------------- entry metadata */

void
rgin_meta_parse(const char *meta, int len, RginMeta *m)
{
	const uint8 *p = (const uint8 *) meta;
	int			slen;
	int			shift = 0;

	m->has_static = false;
	m->df = 0;
	m->npoints = 0;
	if (len == 0)
		return;
	slen = p[0];
	if (1 + slen > len || (len - 1 - slen) % 2 != 0 ||
		(len - 1 - slen) / 2 > RGIN_MAX_POINTS)
		elog(ERROR, "rgin: malformed entry metadata (length %d)", len);
	for (int i = 0; i < slen; i++)
	{
		m->df |= (int64) (p[1 + i] & 0x7f) << shift;
		shift += 7;
	}
	m->has_static = (slen > 0);
	m->npoints = (len - 1 - slen) / 2;
	for (int i = 0; i < m->npoints; i++)
		m->points[i] = rgin_payload_get(meta + 1 + slen + 2 * i);
}

static int
rgin_meta_encode(const RginMeta *m, char *out, int maxlen)
{
	uint8		buf[10];
	int			slen = 0;
	int			len;

	if (!m->has_static && m->npoints == 0)
		return 0;
	if (m->has_static)
	{
		uint64		v = (uint64) m->df;

		do
		{
			buf[slen++] = (v & 0x7f) | (v > 0x7f ? 0x80 : 0);
			v >>= 7;
		} while (v > 0);
	}
	len = 1 + slen + 2 * m->npoints;
	if (len > maxlen)
		elog(ERROR, "rgin: entry metadata of %d bytes exceeds %d", len, maxlen);
	out[0] = (char) slen;
	memcpy(out + 1, buf, slen);
	for (int i = 0; i < m->npoints; i++)
		rgin_payload_put(out + 1 + slen + 2 * i, m->points[i]);
	return len;
}

/*
 * Replace m's frontier by the Pareto frontier of (frontier U payloads):
 * higher tf and lower norm code dominate.  The result dominates every
 * input point, so it never narrows the bound.  Canonical order (ascending
 * code, ascending tf) makes an unchanged frontier encode identically.
 */
static void
frontier_union(RginMeta *m, const char *payloads, int n)
{
	int			best[256];
	int			maxtf = -1;

	for (int c = 0; c < 256; c++)
		best[c] = -1;
	for (int i = 0; i < m->npoints; i++)
		best[m->points[i] & 0xff] = Max(best[m->points[i] & 0xff], m->points[i] >> 8);
	for (int i = 0; i < n; i++)
	{
		RginPayload p = rgin_payload_get(payloads + i * RGIN_PAYLOAD_WIDTH);

		best[p & 0xff] = Max(best[p & 0xff], p >> 8);
	}
	m->npoints = 0;
	for (int c = 0; c < 256; c++)
	{
		if (best[c] > maxtf)
		{
			m->points[m->npoints++] = (RginPayload) ((best[c] << 8) | c);
			maxtf = best[c];
		}
	}
}

/*
 * Posting-tree metadata changed outside index build, by direct insertion or
 * pending-list cleanup (including conversion of a posting list to a tree).
 * Instrumentation only.
 */
int64		rgin_tree_meta_widen = 0;

/*
 * GinPayloadOps.metaUpdate: build postings count into df_G (static); a
 * posting-tree key keeps the frontier of all its payloads (dynamic).
 * Posting-list keys carry no frontier: the scan reads their payloads.
 */
static int
rgin_meta_update(GinState *ginstate, const char *oldmeta, int oldlen,
				 const char *payloads, int npayloads,
				 bool isBuild, bool isTree, char *out, int maxlen)
{
	RginMeta	m;
	int			len;

	rgin_meta_parse(oldmeta, oldlen, &m);
	if (isBuild)
	{
		m.has_static = true;
		m.df += npayloads;
	}
	if (isTree)
		frontier_union(&m, payloads, npayloads);
	len = rgin_meta_encode(&m, out, maxlen);
	if (isTree && !isBuild && oldmeta != NULL &&
		(len != oldlen || memcmp(out, oldmeta, len) != 0))
		rgin_tree_meta_widen++;
	return len;
}

const GinPayloadOps rgin_bm25_payload_ops = {
	.metaUpdate = rgin_meta_update,
};

/* ---------------------------------------------------------------- tsvector side */

static WordEntry *
tsv_find(TSVector tsv, const char *lex, int len)
{
	WordEntry  *we = ARRPTR(tsv);
	char	   *str = STRPTR(tsv);
	int			lo = 0,
				hi = tsv->size;

	while (lo < hi)
	{
		int			mid = (lo + hi) / 2;
		int			c = tsCompareString(str + we[mid].pos, we[mid].len,
										(char *) lex, len, false);

		if (c == 0)
			return &we[mid];
		if (c < 0)
			lo = mid + 1;
		else
			hi = mid;
	}
	return NULL;
}

double
rgin_tsv_score(TSVector tsv, const RginQuery *q)
{
	int			dl = rgin_tsv_dl(tsv);
	double		score = 0.0;

	for (int i = 0; i < q->nterms; i++)
	{
		WordEntry  *we = tsv_find(tsv, RGIN_QUERY_LEXEME(q, i), q->terms[i].len);

		if (we)
			score += rgin_contrib(rgin_bm25_payload(rgin_tsv_tf(tsv, we), dl),
								  q->terms[i].idf, q);
	}
	return score;
}

static bool
tsv_match_any(TSVector tsv, const RginQuery *q)
{
	for (int i = 0; i < q->nterms; i++)
		if (tsv_find(tsv, RGIN_QUERY_LEXEME(q, i), q->terms[i].len))
			return true;
	return false;
}

/* ---------------------------------------------------------------- datum I/O */

PG_FUNCTION_INFO_V1(bm25query_in);
PG_FUNCTION_INFO_V1(bm25query_out);
PG_FUNCTION_INFO_V1(bm25query_make);
PG_FUNCTION_INFO_V1(bm25_score);
PG_FUNCTION_INFO_V1(rgin_distance);
PG_FUNCTION_INFO_V1(rgin_match);
PG_FUNCTION_INFO_V1(rgin_extract_query);
PG_FUNCTION_INFO_V1(rgin_consistent);

Datum
bm25query_in(PG_FUNCTION_ARGS)
{
	ereport(ERROR,
			(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
			 errmsg("bm25query has no input form; use bm25query(index, tsquery)")));
	PG_RETURN_NULL();
}

Datum
bm25query_out(PG_FUNCTION_ARGS)
{
	RginQuery  *q = DatumGetRginQuery(PG_GETARG_DATUM(0));
	StringInfoData s;

	initStringInfo(&s);
	appendStringInfo(&s, "{index:%u, rel:%u, N:%.17g, avgdl:%.17g, k1:%g, b:%g, terms:[",
					 q->indexoid, q->relnumber, q->N, q->avgdl, q->k1, q->b);
	for (int i = 0; i < q->nterms; i++)
		appendStringInfo(&s, "%s%.*s/df=" INT64_FORMAT "/idf=%.17g", i ? ", " : "",
						 (int) q->terms[i].len, RGIN_QUERY_LEXEME(q, i),
						 q->terms[i].df, q->terms[i].idf);
	appendStringInfoString(&s, "]}");
	PG_RETURN_CSTRING(s.data);
}

/* ---------------------------------------------------------------- constructor */

typedef struct LexRef
{
	char	   *lex;
	int			len;
} LexRef;

static int
lexref_cmp(const void *a, const void *b)
{
	const LexRef *x = a,
			   *y = b;

	return tsCompareString(x->lex, x->len, y->lex, y->len, false);
}

typedef struct QCache
{
	Oid			indexoid;
	RelFileNumber relnumber;
	double		k1,
				b;
	Size		qlen;
	char	   *qbytes;
	RginQuery  *result;
} QCache;

/*
 * bm25query(index regclass, query tsquery, k1 float8, b float8)
 *
 * STABLE: reads the build-time generation of the index.  The index lock
 * taken here is held to end of transaction, so every evaluation within a
 * transaction (scan key and per-row projection) sees the same generation.
 */
Datum
bm25query_make(PG_FUNCTION_ARGS)
{
	Oid			indexoid = PG_GETARG_OID(0);
	TSQuery		tsq = PG_GETARG_TSQUERY(1);
	double		k1 = PG_GETARG_FLOAT8(2);
	double		b = PG_GETARG_FLOAT8(3);
	QCache	   *cache = (QCache *) fcinfo->flinfo->fn_extra;
	Relation	index;
	GinState	gs;
	QueryItem  *item = GETQUERY(tsq);
	char	   *operand = GETOPERAND(tsq);
	LexRef	   *lx;
	int			nlx = 0;
	Size		strbytes = 0,
				size;
	RginQuery  *q;
	char	   *p;
	int64		N,
				sumdl;
	RginIndexMeta im;

	if (!(k1 >= 0.0) || !(b >= 0.0 && b <= 1.0))
		ereport(ERROR,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("bm25query: require k1 >= 0 and 0 <= b <= 1")));

	index = index_open(indexoid, AccessShareLock);	/* held to xact end */
	if (!rgin_is_rgin_index(index))
		ereport(ERROR,
				(errcode(ERRCODE_WRONG_OBJECT_TYPE),
				 errmsg("\"%s\" is not an rgin index", RelationGetRelationName(index))));

	if (cache && cache->indexoid == indexoid &&
		cache->relnumber == index->rd_locator.relNumber &&
		cache->k1 == k1 && cache->b == b &&
		cache->qlen == VARSIZE(tsq) && memcmp(cache->qbytes, tsq, cache->qlen) == 0)
	{
		index_close(index, NoLock);
		q = palloc(VARSIZE(cache->result));
		memcpy(q, cache->result, VARSIZE(cache->result));
		PG_RETURN_POINTER(q);
	}

	lx = palloc(sizeof(LexRef) * Max(tsq->size, 1));
	for (int i = 0; i < tsq->size; i++)
	{
		if (item[i].type != QI_VAL)
			continue;
		if (item[i].qoperand.prefix)
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("bm25query: prefix terms are not supported")));
		lx[nlx].lex = operand + item[i].qoperand.distance;
		lx[nlx].len = item[i].qoperand.length;
		nlx++;
	}
	if (nlx > 1)
	{
		int			k = 1;

		qsort(lx, nlx, sizeof(LexRef), lexref_cmp);
		for (int i = 1; i < nlx; i++)
			if (lexref_cmp(&lx[i], &lx[k - 1]) != 0)
				lx[k++] = lx[i];
		nlx = k;
	}
	for (int i = 0; i < nlx; i++)
		strbytes += lx[i].len;

	rgin_init_state(&gs, index);
	rgin_read_index_meta(index, &im);
	N = im.N;
	sumdl = im.sumdl;

	size = offsetof(RginQuery, terms) + sizeof(RginQTerm) * nlx + strbytes;
	q = palloc0(size);
	SET_VARSIZE(q, size);
	q->indexoid = indexoid;
	q->relnumber = index->rd_locator.relNumber;
	q->nterms = nlx;
	q->N = (double) N;
	q->avgdl = (N > 0 && sumdl > 0) ? (double) sumdl / (double) N : 1.0;
	q->k1 = k1;
	q->b = b;
	p = (char *) &q->terms[nlx];
	for (int i = 0; i < nlx; i++)
	{
		int64		df = 0;
		double		idf;
		RginTermInfo ti;

		rgin_lookup_term(index, &gs, lx[i].lex, lx[i].len, false, &ti);
		if (ti.found && ti.meta.has_static)
			df = ti.meta.df;

		df = Min(df, N);		/* consistent generation: df <= N */
		idf = log(1.0 + ((double) N - (double) df + 0.5) / ((double) df + 0.5));
		q->terms[i].idf = Max(idf, 0.0);
		q->terms[i].df = df;
		q->terms[i].off = (uint32) (p - (char *) q);
		q->terms[i].len = lx[i].len;
		memcpy(p, lx[i].lex, lx[i].len);
		p += lx[i].len;
	}
	index_close(index, NoLock);

	/* remember for subsequent per-row evaluations at this call site */
	{
		MemoryContext old = MemoryContextSwitchTo(fcinfo->flinfo->fn_mcxt);

		if (cache == NULL)
			cache = palloc0(sizeof(QCache));
		else
		{
			if (cache->qbytes)
				pfree(cache->qbytes);
			if (cache->result)
				pfree(cache->result);
		}
		cache->indexoid = indexoid;
		cache->relnumber = q->relnumber;
		cache->k1 = k1;
		cache->b = b;
		cache->qlen = VARSIZE(tsq);
		cache->qbytes = palloc(cache->qlen);
		memcpy(cache->qbytes, tsq, cache->qlen);
		cache->result = palloc(size);
		memcpy(cache->result, q, size);
		fcinfo->flinfo->fn_extra = cache;
		MemoryContextSwitchTo(old);
	}
	PG_RETURN_POINTER(q);
}

/* ---------------------------------------------------------------- operators */

Datum
bm25_score(PG_FUNCTION_ARGS)
{
	TSVector	tsv = PG_GETARG_TSVECTOR(0);
	RginQuery  *q = DatumGetRginQuery(PG_GETARG_DATUM(1));

	PG_RETURN_FLOAT8(rgin_tsv_score(tsv, q));
}

/* ORDER BY operator: ascending distance = descending score */
Datum
rgin_distance(PG_FUNCTION_ARGS)
{
	TSVector	tsv = PG_GETARG_TSVECTOR(0);
	RginQuery  *q = DatumGetRginQuery(PG_GETARG_DATUM(1));

	PG_RETURN_FLOAT8(-rgin_tsv_score(tsv, q));
}

/* tsv @@ bm25query: contains any query term (OR semantics) */
Datum
rgin_match(PG_FUNCTION_ARGS)
{
	TSVector	tsv = PG_GETARG_TSVECTOR(0);
	RginQuery  *q = DatumGetRginQuery(PG_GETARG_DATUM(1));

	PG_RETURN_BOOL(tsv_match_any(tsv, q));
}

/* GIN support procs; used only by gincostestimate (no bitmap scans) */
Datum
rgin_extract_query(PG_FUNCTION_ARGS)
{
	RginQuery  *q = DatumGetRginQuery(PG_GETARG_DATUM(0));
	int32	   *nentries = (int32 *) PG_GETARG_POINTER(1);
	Datum	   *entries;

	*nentries = q->nterms;
	if (q->nterms == 0)
		PG_RETURN_POINTER(NULL);
	entries = palloc(sizeof(Datum) * q->nterms);
	for (int i = 0; i < q->nterms; i++)
		entries[i] = PointerGetDatum(cstring_to_text_with_len(RGIN_QUERY_LEXEME(q, i),
															   q->terms[i].len));
	PG_RETURN_POINTER(entries);
}

Datum
rgin_consistent(PG_FUNCTION_ARGS)
{
	bool	   *check = (bool *) PG_GETARG_POINTER(0);
	int32		nkeys = PG_GETARG_INT32(3);
	bool	   *recheck = (bool *) PG_GETARG_POINTER(5);

	*recheck = false;
	for (int i = 0; i < nkeys; i++)
		if (check[i])
			PG_RETURN_BOOL(true);
	PG_RETURN_BOOL(false);
}
