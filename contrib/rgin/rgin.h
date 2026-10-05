/*
 * rgin.h
 *		Research ranked GIN (M1 prototype).  Not for production.
 *
 * Split:
 *	rgin.c		 GIN-side machinery: payload-carrying postings, root summary
 *				 storage, build/insert, ordered scan (amgettuple).
 *	rgin_bm25.c	 BM25 client: tf/norm encoding, frontier dominance,
 *				 contribution and bound, query datum, SQL operators.
 *
 * The machinery treats a posting payload as an opaque uint16 and a summary
 * as a set of payloads; only the client knows what they mean.
 */
#ifndef RGIN_H
#define RGIN_H

#include "access/gin_private.h"
#include "tsearch/ts_type.h"
#include "fmgr.h"

/* ---- payload (client-defined, 16 bits) ---- */
typedef uint16 RginPayload;

/* ---- BM25 query datum ---- */
typedef struct RginQTerm
{
	double		idf;			/* clamped >= 0 */
	int64		df;				/* df_G, 0 if absent at build */
	uint32		off;			/* byte offset of lexeme from datum start */
	uint32		len;
} RginQTerm;

typedef struct RginQuery
{
	int32		vl_len_;
	Oid			indexoid;		/* generation tag: index OID ... */
	RelFileNumber relnumber;	/* ... and relfilenumber at construction */
	int32		nterms;
	int32		pad;
	double		N;
	double		avgdl;
	double		k1;
	double		b;
	RginQTerm	terms[FLEXIBLE_ARRAY_MEMBER];	/* sorted by tsCompareString */
	/* lexeme bytes follow */
} RginQuery;

#define RGIN_QUERY_LEXEME(q, i)	((char *) (q) + (q)->terms[i].off)
#define DatumGetRginQuery(d)	((RginQuery *) PG_DETOAST_DATUM(d))

/* ---- BM25 client API (rgin_bm25.c) ---- */
extern void rgin_bm25_init(void);
extern RginPayload rgin_bm25_payload(int tf, int dl);
extern int	rgin_tsv_dl(TSVector tsv);
extern int	rgin_tsv_tf(TSVector tsv, WordEntry *we);
extern bool rgin_payload_dominates(RginPayload a, RginPayload b);
extern double rgin_contrib(RginPayload p, double idf, const RginQuery *q);
extern double rgin_tsv_score(TSVector tsv, const RginQuery *q);

/* summary point <-> fake item pointer (stored in a magic entry) */
extern ItemPointerData rgin_point_to_item(RginPayload p);
extern RginPayload rgin_item_to_point(ItemPointer ip);

/* ---- machinery API used by the client (rgin.c) ---- */
extern bool rgin_is_rgin_index(Relation index);
extern ItemPointer rgin_read_magic(Relation index, GinState *gs, char tag,
								   const char *lex, int len, int *n);

/* magic entry tags (first key byte) */
#define RGIN_TAG_FRONTIER	'\x01'
#define RGIN_TAG_STATS		'\x03'

/*
 * A frontier entry holds the term's frontier points (block = tf byte <= 255)
 * followed by one df item (block = RGIN_DF_BLOCK_BASE + df_G) written at build.
 */
#define RGIN_DF_BLOCK_BASE	256
#define RGIN_IS_POINT(ip)	(GinItemPointerGetBlockNumber(ip) < RGIN_DF_BLOCK_BASE)

#endif							/* RGIN_H */
