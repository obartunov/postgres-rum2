/*-------------------------------------------------------------------------
 *
 * ginpostinglist.c
 *	  routines for dealing with posting lists.
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *			src/backend/access/gin/ginpostinglist.c
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "access/gin_private.h"

#ifdef USE_ASSERT_CHECKING
#define CHECK_ENCODING_ROUNDTRIP
#endif

/*
 * For encoding purposes, item pointers are represented as 64-bit unsigned
 * integers. The lowest 11 bits represent the offset number, and the next
 * lowest 32 bits are the block number. That leaves 21 bits unused, i.e.
 * only 43 low bits are used.
 *
 * 11 bits is enough for the offset number, because MaxHeapTuplesPerPage <
 * 2^11 on all supported block sizes. We are frugal with the bits, because
 * smaller integers use fewer bytes in the varbyte encoding, saving disk
 * space. (If we get a new table AM in the future that wants to use the full
 * range of possible offset numbers, we'll need to change this.)
 *
 * These 43-bit integers are encoded using varbyte encoding. In each byte,
 * the 7 low bits contain data, while the highest bit is a continuation bit.
 * When the continuation bit is set, the next byte is part of the same
 * integer, otherwise this is the last byte of this integer. 43 bits need
 * at most 7 bytes in this encoding:
 *
 * 0XXXXXXX
 * 1XXXXXXX 0XXXXYYY
 * 1XXXXXXX 1XXXXYYY 0YYYYYYY
 * 1XXXXXXX 1XXXXYYY 1YYYYYYY 0YYYYYYY
 * 1XXXXXXX 1XXXXYYY 1YYYYYYY 1YYYYYYY 0YYYYYYY
 * 1XXXXXXX 1XXXXYYY 1YYYYYYY 1YYYYYYY 1YYYYYYY 0YYYYYYY
 * 1XXXXXXX 1XXXXYYY 1YYYYYYY 1YYYYYYY 1YYYYYYY 1YYYYYYY 0uuuuuuY
 *
 * X = bits used for offset number
 * Y = bits used for block number
 * u = unused bit
 *
 * The bytes are in stored in little-endian order.
 *
 * An important property of this encoding is that removing an item from list
 * never increases the size of the resulting compressed posting list. Proof:
 *
 * Removing number is actually replacement of two numbers with their sum. We
 * have to prove that varbyte encoding of a sum can't be longer than varbyte
 * encoding of its summands. Sum of two numbers is at most one bit wider than
 * the larger of the summands. Widening a number by one bit enlarges its length
 * in varbyte encoding by at most one byte. Therefore, varbyte encoding of sum
 * is at most one byte longer than varbyte encoding of larger summand. Lesser
 * summand is at least one byte, so the sum cannot take more space than the
 * summands, Q.E.D.
 *
 * This property greatly simplifies VACUUM, which can assume that posting
 * lists always fit on the same page after vacuuming. Note that even though
 * that holds for removing items from a posting list, you must also be
 * careful to not cause expansion e.g. when merging uncompressed items on the
 * page into the compressed lists, when vacuuming.
 */

/*
 * How many bits do you need to encode offset number? OffsetNumber is a 16-bit
 * integer, but you can't fit that many items on a page. 11 ought to be more
 * than enough. It's tempting to derive this from MaxHeapTuplesPerPage, and
 * use the minimum number of bits, but that would require changing the on-disk
 * format if MaxHeapTuplesPerPage changes. Better to leave some slack.
 */
#define MaxHeapTuplesPerPageBits		11

/* Max. number of bytes needed to encode the largest supported integer. */
#define MaxBytesPerInteger				7

static inline uint64
itemptr_to_uint64(const ItemPointerData *iptr)
{
	uint64		val;

	Assert(ItemPointerIsValid(iptr));
	Assert(GinItemPointerGetOffsetNumber(iptr) < (1 << MaxHeapTuplesPerPageBits));

	val = GinItemPointerGetBlockNumber(iptr);
	val <<= MaxHeapTuplesPerPageBits;
	val |= GinItemPointerGetOffsetNumber(iptr);

	return val;
}

static inline void
uint64_to_itemptr(uint64 val, ItemPointer iptr)
{
	GinItemPointerSetOffsetNumber(iptr, val & ((1 << MaxHeapTuplesPerPageBits) - 1));
	val = val >> MaxHeapTuplesPerPageBits;
	GinItemPointerSetBlockNumber(iptr, val);

	Assert(ItemPointerIsValid(iptr));
}

/*
 * Varbyte-encode 'val' into *ptr. *ptr is incremented to next integer.
 */
static void
encode_varbyte(uint64 val, unsigned char **ptr)
{
	unsigned char *p = *ptr;

	while (val > 0x7F)
	{
		*(p++) = 0x80 | (val & 0x7F);
		val >>= 7;
	}
	*(p++) = (unsigned char) val;

	*ptr = p;
}

/*
 * Decode varbyte-encoded integer at *ptr. *ptr is incremented to next integer.
 */
static uint64
decode_varbyte(unsigned char **ptr)
{
	uint64		val;
	unsigned char *p = *ptr;
	uint64		c;

	/* 1st byte */
	c = *(p++);
	val = c & 0x7F;
	if (c & 0x80)
	{
		/* 2nd byte */
		c = *(p++);
		val |= (c & 0x7F) << 7;
		if (c & 0x80)
		{
			/* 3rd byte */
			c = *(p++);
			val |= (c & 0x7F) << 14;
			if (c & 0x80)
			{
				/* 4th byte */
				c = *(p++);
				val |= (c & 0x7F) << 21;
				if (c & 0x80)
				{
					/* 5th byte */
					c = *(p++);
					val |= (c & 0x7F) << 28;
					if (c & 0x80)
					{
						/* 6th byte */
						c = *(p++);
						val |= (c & 0x7F) << 35;
						if (c & 0x80)
						{
							/* 7th byte, should not have continuation bit */
							c = *(p++);
							val |= c << 42;
							Assert((c & 0x80) == 0);
						}
					}
				}
			}
		}
	}

	*ptr = p;

	return val;
}

/*
 * Encode a posting list.
 *
 * The encoded list is returned in a palloc'd struct, which will be at most
 * 'maxsize' bytes in size.  The number items in the returned segment is
 * returned in *nwritten. If it's not equal to nipd, not all the items fit
 * in 'maxsize', and only the first *nwritten were encoded.
 *
 * The allocated size of the returned struct is short-aligned, and the padding
 * byte at the end, if any, is zero.
 */
GinPostingList *
ginCompressPostingList(const ItemPointerData *ipd, int nipd, int maxsize,
					   int *nwritten)
{
	uint64		prev;
	int			totalpacked = 0;
	int			maxbytes;
	GinPostingList *result;
	unsigned char *ptr;
	unsigned char *endptr;

	maxsize = SHORTALIGN_DOWN(maxsize);

	result = palloc(maxsize);

	maxbytes = maxsize - offsetof(GinPostingList, bytes);
	Assert(maxbytes > 0);

	/* Store the first special item */
	result->first = ipd[0];

	prev = itemptr_to_uint64(&result->first);

	ptr = result->bytes;
	endptr = result->bytes + maxbytes;
	for (totalpacked = 1; totalpacked < nipd; totalpacked++)
	{
		uint64		val = itemptr_to_uint64(&ipd[totalpacked]);
		uint64		delta = val - prev;

		Assert(val > prev);

		if (endptr - ptr >= MaxBytesPerInteger)
			encode_varbyte(delta, &ptr);
		else
		{
			/*
			 * There are less than 7 bytes left. Have to check if the next
			 * item fits in that space before writing it out.
			 */
			unsigned char buf[MaxBytesPerInteger];
			unsigned char *p = buf;

			encode_varbyte(delta, &p);
			if (p - buf > (endptr - ptr))
				break;			/* output is full */

			memcpy(ptr, buf, p - buf);
			ptr += (p - buf);
		}
		prev = val;
	}
	result->nbytes = ptr - result->bytes;

	/*
	 * If we wrote an odd number of bytes, zero out the padding byte at the
	 * end.
	 */
	if (result->nbytes != SHORTALIGN(result->nbytes))
		result->bytes[result->nbytes] = 0;

	if (nwritten)
		*nwritten = totalpacked;

	Assert(SizeOfGinPostingList(result) <= maxsize);

	/*
	 * Check that the encoded segment decodes back to the original items.
	 */
#if defined (CHECK_ENCODING_ROUNDTRIP)
	{
		int			ndecoded;
		ItemPointer tmp = ginPostingListDecode(result, &ndecoded);

		Assert(ndecoded == totalpacked);
		Assert(memcmp(tmp, ipd, ndecoded * sizeof(ItemPointerData)) == 0);
		pfree(tmp);
	}
#endif

	return result;
}

/*
 * Decode a compressed posting list into an array of item pointers.
 * The number of items is returned in *ndecoded.
 */
ItemPointer
ginPostingListDecode(GinPostingList *plist, int *ndecoded_out)
{
	return ginPostingListDecodeAllSegments(plist,
										   SizeOfGinPostingList(plist),
										   ndecoded_out);
}

/*
 * Decode multiple posting list segments into an array of item pointers.
 * The number of items is returned in *ndecoded_out. The segments are stored
 * one after each other, with total size 'len' bytes.
 */
ItemPointer
ginPostingListDecodeAllSegments(GinPostingList *segment, int len, int *ndecoded_out)
{
	ItemPointer result;
	int			nallocated;
	uint64		val;
	char	   *endseg = ((char *) segment) + len;
	int			ndecoded;
	unsigned char *ptr;
	unsigned char *endptr;

	/*
	 * Guess an initial size of the array.
	 */
	nallocated = segment->nbytes * 2 + 1;
	result = palloc_array(ItemPointerData, nallocated);

	ndecoded = 0;
	while ((char *) segment < endseg)
	{
		/* enlarge output array if needed */
		if (ndecoded >= nallocated)
		{
			nallocated *= 2;
			result = repalloc_array(result, ItemPointerData, nallocated);
		}

		/* copy the first item */
		Assert(OffsetNumberIsValid(ItemPointerGetOffsetNumber(&segment->first)));
		Assert(ndecoded == 0 || ginCompareItemPointers(&segment->first, &result[ndecoded - 1]) > 0);
		result[ndecoded] = segment->first;
		ndecoded++;

		val = itemptr_to_uint64(&segment->first);
		ptr = segment->bytes;
		endptr = segment->bytes + segment->nbytes;
		while (ptr < endptr)
		{
			/* enlarge output array if needed */
			if (ndecoded >= nallocated)
			{
				nallocated *= 2;
				result = repalloc_array(result, ItemPointerData, nallocated);
			}

			val += decode_varbyte(&ptr);

			uint64_to_itemptr(val, &result[ndecoded]);
			ndecoded++;
		}
		segment = GinNextPostingListSegment(segment);
	}

	if (ndecoded_out)
		*ndecoded_out = ndecoded;
	return result;
}

/*
 * Add all item pointers from a bunch of posting lists to a TIDBitmap.
 */
int
ginPostingListDecodeAllSegmentsToTbm(GinPostingList *ptr, int len,
									 TIDBitmap *tbm)
{
	int			ndecoded;
	ItemPointer items;

	items = ginPostingListDecodeAllSegments(ptr, len, &ndecoded);
	tbm_add_tuples(tbm, items, ndecoded, false);
	pfree(items);

	return ndecoded;
}

/*
 * Merge two ordered arrays of itempointers, eliminating any duplicates.
 *
 * Returns a palloc'd array, and *nmerged is set to the number of items in
 * the result, after eliminating duplicates.
 */
ItemPointer
ginMergeItemPointers(ItemPointerData *a, uint32 na,
					 ItemPointerData *b, uint32 nb,
					 int *nmerged)
{
	ItemPointerData *dst;

	dst = palloc_array(ItemPointerData, na + nb);

	/*
	 * If the argument arrays don't overlap, we can just append them to each
	 * other.
	 */
	if (na == 0 || nb == 0 || ginCompareItemPointers(&a[na - 1], &b[0]) < 0)
	{
		memcpy(dst, a, na * sizeof(ItemPointerData));
		memcpy(&dst[na], b, nb * sizeof(ItemPointerData));
		*nmerged = na + nb;
	}
	else if (ginCompareItemPointers(&b[nb - 1], &a[0]) < 0)
	{
		memcpy(dst, b, nb * sizeof(ItemPointerData));
		memcpy(&dst[nb], a, na * sizeof(ItemPointerData));
		*nmerged = na + nb;
	}
	else
	{
		ItemPointerData *dptr = dst;
		ItemPointerData *aptr = a;
		ItemPointerData *bptr = b;

		while (aptr - a < na && bptr - b < nb)
		{
			int			cmp = ginCompareItemPointers(aptr, bptr);

			if (cmp > 0)
				*dptr++ = *bptr++;
			else if (cmp == 0)
			{
				/* only keep one copy of the identical items */
				*dptr++ = *bptr++;
				aptr++;
			}
			else
				*dptr++ = *aptr++;
		}

		while (aptr - a < na)
			*dptr++ = *aptr++;

		while (bptr - b < nb)
			*dptr++ = *bptr++;

		*nmerged = dptr - dst;
	}

	return dst;
}


/*
 * Payload posting lists (payload width W > 0).  See GinPostingList in
 * ginblock.h for the layout.  Ordering and duplicate elimination use the
 * TID only; the payload of an item travels with it.
 */

/*
 * Like ginCompressPostingList, for an index with payload width W.  The
 * payload of ipd[i] is payloads[i * W .. (i + 1) * W).
 */
GinPostingList *
ginCompressPostingListPayload(const ItemPointerData *ipd, const char *payloads,
							  int payloadWidth, int nipd, int maxsize,
							  int *nwritten)
{
	uint64		prev;
	int			totalpacked;
	int			budget;
	GinPostingList *result;
	unsigned char *ptr;
	uint16		n;

	Assert(payloadWidth > 0 && nipd > 0);
	maxsize = SHORTALIGN_DOWN(maxsize);
	result = palloc(maxsize);

	/* header, item count and the first item's payload must always fit */
	budget = maxsize - offsetof(GinPostingList, bytes) - sizeof(uint16) - payloadWidth;
	Assert(budget >= 0);

	result->first = ipd[0];
	prev = itemptr_to_uint64(&result->first);
	ptr = result->bytes + sizeof(uint16);
	for (totalpacked = 1; totalpacked < nipd; totalpacked++)
	{
		uint64		val = itemptr_to_uint64(&ipd[totalpacked]);
		unsigned char buf[MaxBytesPerInteger];
		unsigned char *p = buf;

		Assert(val > prev);
		encode_varbyte(val - prev, &p);
		if ((p - buf) + payloadWidth > budget)
			break;				/* output is full */
		memcpy(ptr, buf, p - buf);
		ptr += p - buf;
		budget -= (p - buf) + payloadWidth;
		prev = val;
	}

	n = totalpacked;
	memcpy(result->bytes, &n, sizeof(uint16));
	memcpy(ptr, payloads, (Size) totalpacked * payloadWidth);
	ptr += totalpacked * payloadWidth;
	result->nbytes = ptr - result->bytes;
	if (result->nbytes != SHORTALIGN(result->nbytes))
		result->bytes[result->nbytes] = 0;

	if (nwritten)
		*nwritten = totalpacked;

	Assert(SizeOfGinPostingList(result) <= maxsize);

#if defined (CHECK_ENCODING_ROUNDTRIP)
	{
		int			ndecoded;
		char	   *ptmp;
		ItemPointer tmp = ginPostingListDecodePayload(result, payloadWidth,
													  &ndecoded, &ptmp);

		Assert(ndecoded == totalpacked);
		Assert(memcmp(tmp, ipd, ndecoded * sizeof(ItemPointerData)) == 0);
		Assert(memcmp(ptmp, payloads, (Size) ndecoded * payloadWidth) == 0);
		pfree(tmp);
		pfree(ptmp);
	}
#endif

	return result;
}

/*
 * Decode consecutive payload segments of total size 'len'.  TIDs are
 * returned as a palloc'd array, payloads as a palloc'd byte array in
 * *payloads_out (both parallel, *ndecoded_out items).
 */
ItemPointer
ginPostingListDecodeAllSegmentsPayload(GinPostingList *segment, int len,
									   int payloadWidth, int *ndecoded_out,
									   char **payloads_out)
{
	char	   *endseg = ((char *) segment) + len;
	GinPostingList *seg;
	ItemPointer result;
	char	   *pres;
	int			total = 0;
	int			ndecoded = 0;

	Assert(payloadWidth > 0);

	/* item counts are in the segment headers, so size the arrays exactly */
	for (seg = segment; (char *) seg < endseg; seg = GinNextPostingListSegment(seg))
		total += GinPayloadListGetNItems(seg);

	result = palloc_array(ItemPointerData, Max(total, 1));
	pres = palloc(Max((Size) total * payloadWidth, 1));

	for (seg = segment; (char *) seg < endseg; seg = GinNextPostingListSegment(seg))
	{
		int			nitems = GinPayloadListGetNItems(seg);
		char	   *pl = GinPayloadListGetPayloads(seg, payloadWidth);
		unsigned char *ptr = seg->bytes + sizeof(uint16);
		unsigned char *endptr = (unsigned char *) pl;
		uint64		val;
		int			start = ndecoded;

		Assert(nitems > 0);
		Assert(ndecoded == 0 || ginCompareItemPointers(&seg->first, &result[ndecoded - 1]) > 0);
		result[ndecoded++] = seg->first;
		val = itemptr_to_uint64(&seg->first);
		while (ptr < endptr)
		{
			if (ndecoded >= total)
				elog(ERROR, "GIN payload posting list holds more items than its header says");
			val += decode_varbyte(&ptr);
			uint64_to_itemptr(val, &result[ndecoded]);
			ndecoded++;
		}
		if (ndecoded - start != nitems)
			elog(ERROR, "number of items mismatch in GIN payload posting list, %d in header, %d decoded",
				 nitems, ndecoded - start);
		memcpy(pres + (Size) start * payloadWidth, pl, (Size) nitems * payloadWidth);
	}

	*ndecoded_out = ndecoded;
	*payloads_out = pres;
	return result;
}

ItemPointer
ginPostingListDecodePayload(GinPostingList *plist, int payloadWidth,
							int *ndecoded_out, char **payloads_out)
{
	return ginPostingListDecodeAllSegmentsPayload(plist,
												  SizeOfGinPostingList(plist),
												  payloadWidth, ndecoded_out,
												  payloads_out);
}

/*
 * Merge two ordered (TID, payload) arrays.  An item present in both keeps
 * one copy; its payloads must be equal, since one key and one heap TID have
 * exactly one payload.  Unequal payloads raise an error.
 */
ItemPointer
ginMergeItemPointersPayload(ItemPointerData *a, char *pa, uint32 na,
							ItemPointerData *b, char *pb, uint32 nb,
							int payloadWidth, int *nmerged, char **pmerged)
{
	ItemPointerData *dst = palloc_array(ItemPointerData, na + nb);
	char	   *pdst = palloc(Max((Size) (na + nb) * payloadWidth, 1));
	uint32		i = 0,
				j = 0,
				k = 0;

	while (i < na && j < nb)
	{
		int			cmp = ginCompareItemPointers(&a[i], &b[j]);

		if (cmp < 0)
		{
			dst[k] = a[i];
			memcpy(pdst + (Size) k * payloadWidth, pa + (Size) i * payloadWidth, payloadWidth);
			i++;
		}
		else
		{
			if (cmp == 0)
			{
				if (memcmp(pa + (Size) i * payloadWidth, pb + (Size) j * payloadWidth,
						   payloadWidth) != 0)
					ereport(ERROR,
							(errcode(ERRCODE_INTERNAL_ERROR),
							 errmsg("conflicting GIN posting payloads for heap TID (%u,%u)",
									GinItemPointerGetBlockNumber(&b[j]),
									GinItemPointerGetOffsetNumber(&b[j]))));
				i++;
			}
			dst[k] = b[j];
			memcpy(pdst + (Size) k * payloadWidth, pb + (Size) j * payloadWidth, payloadWidth);
			j++;
		}
		k++;
	}
	if (i < na)
	{
		memcpy(&dst[k], &a[i], (na - i) * sizeof(ItemPointerData));
		memcpy(pdst + (Size) k * payloadWidth, pa + (Size) i * payloadWidth,
			   (Size) (na - i) * payloadWidth);
		k += na - i;
	}
	if (j < nb)
	{
		memcpy(&dst[k], &b[j], (nb - j) * sizeof(ItemPointerData));
		memcpy(pdst + (Size) k * payloadWidth, pb + (Size) j * payloadWidth,
			   (Size) (nb - j) * payloadWidth);
		k += nb - j;
	}

	*nmerged = k;
	*pmerged = pdst;
	return dst;
}
