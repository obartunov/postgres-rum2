/* contrib/rgin/rgin--1.0.sql -- research ranked GIN (M2 prototype) */

\echo Use "CREATE EXTENSION rgin" to load this file. \quit

CREATE TYPE bm25query;

CREATE FUNCTION bm25query_in(cstring) RETURNS bm25query
AS 'MODULE_PATHNAME' LANGUAGE C STRICT IMMUTABLE;
CREATE FUNCTION bm25query_out(bm25query) RETURNS cstring
AS 'MODULE_PATHNAME' LANGUAGE C STRICT IMMUTABLE;

CREATE TYPE bm25query (
	INTERNALLENGTH = VARIABLE,
	INPUT = bm25query_in,
	OUTPUT = bm25query_out,
	ALIGNMENT = double,
	STORAGE = main
);

-- Query object carrying the build-time statistics generation G of the index.
CREATE FUNCTION bm25query(regclass, tsquery, k1 float8 DEFAULT 1.2, b float8 DEFAULT 0.75)
RETURNS bm25query
AS 'MODULE_PATHNAME', 'bm25query_make'
LANGUAGE C STRICT STABLE PARALLEL SAFE;

CREATE FUNCTION bm25_score(tsvector, bm25query) RETURNS float8
AS 'MODULE_PATHNAME' LANGUAGE C STRICT IMMUTABLE PARALLEL SAFE;

CREATE FUNCTION rgin_distance(tsvector, bm25query) RETURNS float8
AS 'MODULE_PATHNAME' LANGUAGE C STRICT IMMUTABLE PARALLEL SAFE;

CREATE FUNCTION rgin_match(tsvector, bm25query) RETURNS bool
AS 'MODULE_PATHNAME' LANGUAGE C STRICT IMMUTABLE PARALLEL SAFE;

CREATE OPERATOR <=> (LEFTARG = tsvector, RIGHTARG = bm25query, PROCEDURE = rgin_distance);
CREATE OPERATOR @@ (LEFTARG = tsvector, RIGHTARG = bm25query, PROCEDURE = rgin_match,
                    RESTRICT = contsel, JOIN = contjoinsel);

CREATE FUNCTION rgin_extract_query(bm25query, internal, int2, internal, internal, internal, internal)
RETURNS internal AS 'MODULE_PATHNAME' LANGUAGE C STRICT IMMUTABLE;
CREATE FUNCTION rgin_consistent(internal, int2, bm25query, int4, internal, internal, internal, internal)
RETURNS bool AS 'MODULE_PATHNAME' LANGUAGE C STRICT IMMUTABLE;

CREATE FUNCTION rgin_handler(internal) RETURNS index_am_handler
AS 'MODULE_PATHNAME' LANGUAGE C;
CREATE ACCESS METHOD rgin TYPE INDEX HANDLER rgin_handler;

CREATE OPERATOR CLASS rgin_tsvector_ops DEFAULT FOR TYPE tsvector USING rgin AS
	OPERATOR 1 @@ (tsvector, bm25query),
	OPERATOR 2 <=> (tsvector, bm25query) FOR ORDER BY float_ops,
	FUNCTION 1 gin_cmp_tslexeme(text, text),
	FUNCTION 2 gin_extract_tsvector(tsvector, internal, internal),
	FUNCTION 3 rgin_extract_query(bm25query, internal, int2, internal, internal, internal, internal),
	FUNCTION 4 rgin_consistent(internal, int2, bm25query, int4, internal, internal, internal, internal),
	STORAGE text;

-- instrumentation
CREATE FUNCTION rgin_last_stats() RETURNS text AS 'MODULE_PATHNAME' LANGUAGE C;
CREATE FUNCTION rgin_build_info() RETURNS text AS 'MODULE_PATHNAME' LANGUAGE C;
CREATE FUNCTION rgin_insert_info() RETURNS text AS 'MODULE_PATHNAME' LANGUAGE C;
CREATE FUNCTION rgin_term_meta(regclass, text) RETURNS text AS 'MODULE_PATHNAME' LANGUAGE C STRICT;
CREATE FUNCTION rgin_term_frontier_points(regclass, text) RETURNS int4[] AS 'MODULE_PATHNAME' LANGUAGE C STRICT;
CREATE FUNCTION rgin_check(regclass) RETURNS text AS 'MODULE_PATHNAME' LANGUAGE C STRICT;
CREATE FUNCTION rgin_debug_insert(regclass, text, tid, int4) RETURNS int4 AS 'MODULE_PATHNAME' LANGUAGE C STRICT;
