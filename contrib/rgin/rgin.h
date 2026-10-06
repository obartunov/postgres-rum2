/*
 * rgin.h
 *		Research ranked GIN (M2 prototype).  Not for production.
 *
 * Split:
 *	rgin.c		 AM wrapper over the GIN payload format: build/insert through
 *				 core GIN payload routines, ordered scan (amgettuple).
 *	rgin_bm25.c	 BM25 opclass side: payload encoding, entry metadata
 *				 (df_G, root frontier), contribution and bound, query datum.
 *
 * Core GIN sees a fixed-width opaque payload per posting (RGIN_PAYLOAD_WIDTH
 * bytes) and opaque per-key metadata; only rgin_bm25.c knows their meaning.
 */
#ifndef RGIN_H
#define RGIN_H

#include "access/gin_private.h"
#include "tsearch/ts_type.h"
#include "fmgr.h"

/* ---- payload: tf byte, norm code byte ---- */
#define RGIN_PAYLOAD_WIDTH	2
typedef uint16 RginPayload;		/* logical value (tf << 8) | norm code */

static inline RginPayload
rgin_payload_get(const char *p)
{
	return (RginPayload) (((uint8) p[0] << 8) | (uint8) p[1]);
}

static inline void
rgin_payload_put(char *p, RginPayload v)
{
	p[0] = (char) (v >> 8);
	p[1] = (char) (v & 0xff);
}

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

/*
 * Per-key metadata, opaque to GIN:
 *
 *	uint8 static_len | static: varint df_G | dynamic: frontier points
 *
 * The static part is written only by index build (df_G counts the build
 * postings of the key).  The dynamic part is the Pareto frontier of the
 * key's payloads (2 bytes per point, ascending norm code), kept only for
 * posting-tree keys, and only ever widened.
 */
#define RGIN_MAX_POINTS		256

typedef struct RginMeta
{
	bool		has_static;
	int64		df;
	int			npoints;
	RginPayload points[RGIN_MAX_POINTS];
} RginMeta;

/* index-level static metadata (metapage), the rest of generation G */
typedef struct RginIndexMeta
{
	int64		N;
	int64		sumdl;
} RginIndexMeta;

/* ---- BM25 client API (rgin_bm25.c) ---- */
extern const GinPayloadOps rgin_bm25_payload_ops;
extern int64 rgin_tree_meta_widen;
extern void rgin_bm25_init(void);
extern RginPayload rgin_bm25_payload(int tf, int dl);
extern int	rgin_tsv_dl(TSVector tsv);
extern int	rgin_tsv_tf(TSVector tsv, WordEntry *we);
extern bool rgin_payload_dominates(RginPayload a, RginPayload b);
extern double rgin_contrib(RginPayload p, double idf, const RginQuery *q);
extern double rgin_tsv_score(TSVector tsv, const RginQuery *q);
extern void rgin_meta_parse(const char *meta, int len, RginMeta *m);

/* ---- machinery API used by the client (rgin.c) ---- */
typedef struct RginTermInfo
{
	bool		found;
	bool		isTree;
	BlockNumber root;			/* posting tree root, if isTree */
	ItemPointer items;			/* inline postings, if !isTree and wanted */
	char	   *payloads;
	int			nitems;
	int			metalen;
	RginMeta	meta;
} RginTermInfo;

extern bool rgin_is_rgin_index(Relation index);
extern void rgin_init_state(GinState *gs, Relation index);
extern void rgin_lookup_term(Relation index, GinState *gs, const char *lex, int len,
							 bool wantItems, RginTermInfo *ti);
extern void rgin_read_index_meta(Relation index, RginIndexMeta *im);

#endif							/* RGIN_H */
