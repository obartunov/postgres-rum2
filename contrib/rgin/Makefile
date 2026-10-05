# contrib/rgin/Makefile

MODULE_big = rgin
OBJS = \
	$(WIN32RES) \
	rgin.o \
	rgin_bm25.o

EXTENSION = rgin
DATA = rgin--1.0.sql
PGFILEDESC = "rgin - research ranked GIN access method (M2 prototype)"

ifdef USE_PGXS
PG_CONFIG = pg_config
PGXS := $(shell $(PG_CONFIG) --pgxs)
include $(PGXS)
else
subdir = contrib/rgin
top_builddir = ../..
include $(top_builddir)/src/Makefile.global
include $(top_srcdir)/contrib/contrib-global.mk
endif
