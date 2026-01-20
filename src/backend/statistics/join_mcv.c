/*-------------------------------------------------------------------------
 *
 * join_mcv.c
 *	  POSTGRES join MCV lists
 *
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/statistics/join_mcv.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/genam.h"
#include "access/heapam.h"
#include "access/htup_details.h"
#include "access/table.h"
#include "access/tableam.h"
#include "catalog/pg_am.h"
#include "catalog/pg_statistic_ext.h"
#include "catalog/pg_statistic_ext_data.h"
#include "commands/defrem.h"
#include "fmgr.h"
#include "funcapi.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/pathnode.h"
#include "statistics/extended_stats_internal.h"
#include "statistics/statistics.h"
#include "utils/array.h"
#include "utils/builtins.h"
#include "utils/datum.h"
#include "utils/fmgrprotos.h"
#include "utils/lsyscache.h"
#include "utils/snapmgr.h"
#include "utils/syscache.h"
#include "utils/fmgroids.h"
#include "utils/typcache.h"

/*
 * statext_join_mcv_serialize
 * 			Serialize a JoinMCVList into bytea format for storage
 *
 * The overall structure of the serialized representation looks like this:
 *
 * +---------+-------+----------+
 * | header  | items | varlena  |
 * +---------+-------+----------+
 *
 * The header contains magic number, type, and filter metadata (number of
 * filters, type OIDs, typlens, typbyvaltypbyvals).  Items store the frequency values
 * plus Datum arrays.  For each Datum, byval types are stored inline while
 * non-byval types are stored as offsets into the varlena section, which
 * contains the actual variable-length data.
 *
 * Unlike regular MCV lists which deduplicate values and use indexes into
 * separate arrays, join MCV lists store all values directly in each item.
 * During serialization, Datum pointers are converted to offsets; during
 * deserialization, offsets are converted back to pointers.
 */
bytea *
statext_join_mcv_serialize(JoinMCVList * mcvlist)
{
	int			i,
				j;
	Size		len;
	bytea	   *result;
	char	   *ptr;
	char	   *data_ptr;
	Size		header_len;
	AttrNumber	nfilters;

	if (!mcvlist || mcvlist->nitems == 0)
		return NULL;

	nfilters = mcvlist->ndimensions;

	Assert(nfilters > 0 && nfilters <= STATS_MAX_DIMENSIONS);
	Assert(mcvlist->nitems <= MAX_STATISTICS_TARGET);

	/* Calculate header size (up to items array) */
	header_len = offsetof(JoinMCVList, items);

	/* Start with header size */
	len = header_len;

	/* Add space for item structs */
	len += mcvlist->nitems * sizeof(JoinMCVItem);

	/* Add space for isnull arrays (one per item) */
	len += mcvlist->nitems * nfilters * sizeof(bool);

	/* Add space for values arrays (one per item) */
	len += mcvlist->nitems * nfilters * sizeof(Datum);

	/* Add space for actual datum data (for non-byval types) */
	for (i = 0; i < mcvlist->nitems; i++)
	{
		JoinMCVItem *item = &mcvlist->items[i];

		for (j = 0; j < nfilters; j++)
		{
			if (!item->isnull[j])
			{
				bool		typbyval = get_typbyval(mcvlist->filter_types[j]);
				int16		typlen = get_typlen(mcvlist->filter_types[j]);

				if (!typbyval)
					len += datumGetSize(item->values[j], false, typlen);
			}
		}
	}

	/* Allocate result */
	result = (bytea *) palloc(len + VARHDRSZ);
	SET_VARSIZE(result, len + VARHDRSZ);

	/* Initialize pointers */
	ptr = VARDATA(result);
	data_ptr = ptr;

	/* Copy header (fixed fields before items array) */
	memcpy(data_ptr, mcvlist, header_len);
	data_ptr += header_len;

	/* Copy item structs (we'll fix pointers later) */
	memcpy(data_ptr, mcvlist->items, mcvlist->nitems * sizeof(JoinMCVItem));
	data_ptr += mcvlist->nitems * sizeof(JoinMCVItem);

	/* Copy isnull arrays and set pointers */
	for (i = 0; i < mcvlist->nitems; i++)
	{
		JoinMCVItem *out_item = &((JoinMCVList *) ptr)->items[i];
		JoinMCVItem *in_item = &mcvlist->items[i];

		/* Store offset to isnull array */
		out_item->isnull = (bool *) (data_ptr - ptr);

		/* Copy isnull array */
		memcpy(data_ptr, in_item->isnull, nfilters * sizeof(bool));
		data_ptr += nfilters * sizeof(bool);
	}

	/* Copy values arrays and set pointers */
	for (i = 0; i < mcvlist->nitems; i++)
	{
		JoinMCVItem *out_item = &((JoinMCVList *) ptr)->items[i];
		JoinMCVItem *in_item = &mcvlist->items[i];

		/* Store offset to values array */
		out_item->values = (Datum *) (data_ptr - ptr);

		/* Copy values array (byval types) and prepare for non-byval */
		memcpy(data_ptr, in_item->values, nfilters * sizeof(Datum));
		data_ptr += nfilters * sizeof(Datum);
	}

	/* Now copy actual data for non-byval types and fix up pointers */
	for (i = 0; i < mcvlist->nitems; i++)
	{
		JoinMCVItem *out_item = &((JoinMCVList *) ptr)->items[i];
		JoinMCVItem *in_item = &mcvlist->items[i];
		Datum	   *out_values = (Datum *) (ptr + (size_t) out_item->values);

		for (j = 0; j < nfilters; j++)
		{
			if (!in_item->isnull[j])
			{
				bool		typbyval = get_typbyval(mcvlist->filter_types[j]);
				int16		typlen = get_typlen(mcvlist->filter_types[j]);

				if (!typbyval)
				{
					Size		datum_len = datumGetSize(in_item->values[j], false, typlen);
					Size		offset = data_ptr - ptr;

					/* Store offset in the values array */
					out_values[j] = PointerGetDatum((char *) NULL + offset);

					/* Copy the actual data */
					memcpy(data_ptr, DatumGetPointer(in_item->values[j]), datum_len);
					data_ptr += datum_len;
				}
			}
		}
	}

	/* Verify we didn't write past the allocated size */
	Assert(data_ptr <= ptr + len);

	return result;
}

/*
 * statext_join_mcv_deserialize
 *		Deserialize a JoinMCVList from bytea format
 */
JoinMCVList *
statext_join_mcv_deserialize(bytea *data)
{
	JoinMCVList *mcvlist;
	Size		len;
	char	   *base;
	int			i,
				j;
	AttrNumber	nfilters;

	if (!data)
		return NULL;

	len = VARSIZE_ANY_EXHDR(data);

	/* Allocate and copy */
	mcvlist = (JoinMCVList *) palloc(len);
	base = VARDATA_ANY(data);
	memcpy(mcvlist, base, len);

	/* Verify magic number */
	if (mcvlist->magic != STATS_JOIN_MCV_MAGIC)
		elog(ERROR, "invalid magic number in cross-table MCV list");

	nfilters = mcvlist->ndimensions;
	Assert(nfilters > 0 && nfilters <= STATS_MAX_DIMENSIONS);

	/*
	 * Fix up pointers for isnull arrays, values arrays, and non-byval Datums.
	 * These are stored as offsets from the start of the data.
	 */
	for (i = 0; i < mcvlist->nitems; i++)
	{
		JoinMCVItem *item = &mcvlist->items[i];

		/* Fix isnull array pointer */
		item->isnull = (bool *) ((char *) mcvlist + (size_t) item->isnull);

		/* Fix values array pointer */
		item->values = (Datum *) ((char *) mcvlist + (size_t) item->values);

		/* Fix individual non-byval Datum pointers */
		for (j = 0; j < nfilters; j++)
		{
			if (!item->isnull[j])
			{
				bool		typbyval = get_typbyval(mcvlist->filter_types[j]);

				if (!typbyval)
				{
					Size		offset = (Size) DatumGetPointer(item->values[j]);

					item->values[j] = PointerGetDatum((char *) mcvlist + offset);
				}
			}
		}
	}

	return mcvlist;
}

/*
 * statext_join_mcv_build
 *		Build join MCV statistics from sampled rows
 *
 * This function builds a JoinMCVList by:
 * 1. Extracting the referencing column values from the sampled rows
 * 2. Looking up the corresponding filter column values from referenced table
 * 3. Counting occurrences of each (referencing, filter) pair
 * 4. Keeping the most common combinations
 *
 * The sampled rows come from ANALYZE of the referencing table.
 */
JoinMCVList *
statext_join_mcv_build(Oid stxoid,
					   Oid primary_relid,
					   Oid orther_relid,
					   int2vector *joinkeys,
					   int2vector *filter_attnums,
					   int numrows,
					   HeapTuple *rows,
					   int natts,
					   VacAttrStats **vacattrstats)
{
	JoinMCVList *mcvlist;
	Relation	other_rel;
	TupleDesc	other_desc;
	AttrNumber	primary_joinkey;
	AttrNumber	other_joinkey;
	AttrNumber	nfilters;
	int			i;
	Datum	   *primary_joinkey_mcv_values = NULL;
	float4	   *primary_joinkey_mcv_freqs = NULL;
	int			num_primary_joinkey_mcvs = 0;
	Snapshot	snapshot;
	bool		pushed_snapshot = false;
	double		total_freq = 0.0;
	VacAttrStats *primary_joinkey_stats = NULL;
	int			mcv_slot_idx = -1;

	/* Skip invalid stats */
	if (!OidIsValid(primary_relid) || !OidIsValid(orther_relid))
	{
		elog(DEBUG1, "statext_join_mcv_build: invalid relation OIDs (primary=%u, other=%u)",
			 primary_relid, orther_relid);
		return NULL;
	}

	/*
	 * Extract join keys TODO: currently only supports single equality qual
	 */
	Assert(joinkeys->dim1 == 2);
	primary_joinkey = joinkeys->values[0];
	other_joinkey = joinkeys->values[1];

	/*
	 * Extract filter attributes TODO: currently filter attributes are only
	 * from the other_rel
	 */
	nfilters = filter_attnums->dim1;
	Assert(nfilters > 0 && nfilters <= STATS_MAX_DIMENSIONS);

	elog(DEBUG1, "statext_join_mcv_build: stxoid=%u, target_rel=%u, other_rel=%u, target_joinkey=%d, other_joinkey=%d, ndimensions=%d",
		 stxoid, primary_relid, orther_relid, primary_joinkey, other_joinkey, nfilters);

	/*
	 * We reuse the already-computed MCV statistics for the join key column of
	 * the primary relation. This gives us ~100 most common values with their
	 * frequencies already calculated by the current ANALYZE.
	 *
	 * We get the MCV data from the in-memory VacAttrStats structure, not from
	 * pg_statistic, so this works in a single ANALYZE pass.
	 *
	 * FIXME: This approach works well for FK joins (many-to-one) where MCV in
	 * primary table ≈ MCV after join. For general joins (M:N), we should
	 * join the sample rows with other_rel and find MCVs in the join result,
	 * not assume primary table MCVs remain representative.
	 */
	for (i = 0; i < natts; i++)
	{
		if (vacattrstats[i]->tupattnum == primary_joinkey)
		{
			primary_joinkey_stats = vacattrstats[i];
			break;
		}
	}

	if (!primary_joinkey_stats)
	{
		elog(DEBUG1, "statext_join_mcv_build: VacAttrStats not found for primary joinkey attr=%d",
			 primary_joinkey);
		return NULL;
	}

	/* Find the MCV slot in the stats */
	for (i = 0; i < STATISTIC_NUM_SLOTS; i++)
	{
		if (primary_joinkey_stats->stakind[i] == STATISTIC_KIND_MCV)
		{
			mcv_slot_idx = i;
			break;
		}
	}

	if (mcv_slot_idx < 0)
	{
		elog(DEBUG1, "statext_join_mcv_build: No MCV statistics for primary joinkey attr=%d",
			 primary_joinkey);
		return NULL;
	}

	primary_joinkey_mcv_values = primary_joinkey_stats->stavalues[mcv_slot_idx];
	primary_joinkey_mcv_freqs = primary_joinkey_stats->stanumbers[mcv_slot_idx];
	num_primary_joinkey_mcvs = primary_joinkey_stats->numvalues[mcv_slot_idx];

	if (num_primary_joinkey_mcvs <= 0)
		return NULL;

	elog(DEBUG1, "statext_join_mcv_build: Found %d MCV entries, building join mcv stats",
		 num_primary_joinkey_mcvs);

	/* Open the other table */
	other_rel = table_open(orther_relid, AccessShareLock);
	other_desc = RelationGetDescr(other_rel);

	/* Ensure we have an active snapshot */
	if (!ActiveSnapshotSet())
	{
		PushActiveSnapshot(GetTransactionSnapshot());
		pushed_snapshot = true;
	}
	snapshot = GetActiveSnapshot();

	/* Build the join mcv list */
	mcvlist = (JoinMCVList *) palloc0(
									  offsetof(JoinMCVList, items) +
									  num_primary_joinkey_mcvs * sizeof(JoinMCVItem));

	mcvlist->magic = STATS_JOIN_MCV_MAGIC;
	mcvlist->type = STATS_JOIN_MCV_TYPE_BASIC;
	mcvlist->nitems = num_primary_joinkey_mcvs;
	mcvlist->ndimensions = nfilters;

	/* Get filter attribute numbers and types from the other table */
	for (i = 0; i < nfilters; i++)
	{
		mcvlist->filter_attnums[i] = filter_attnums->values[i];
		mcvlist->filter_types[i] = TupleDescAttr(other_desc,
												 filter_attnums->values[i] - 1)->atttypid;
	}

	/*
	 * For each MCV value of the join key column, look up the corresponding
	 * filter value in the referenced table.
	 */
	for (i = 0; i < num_primary_joinkey_mcvs; i++)
	{
		Datum		joinkey_value = primary_joinkey_mcv_values[i];
		float4		frequency = primary_joinkey_mcv_freqs[i];
		ScanKeyData scankey;
		TableScanDesc scan;
		HeapTuple	orthertuple;
		Oid			eq_opr;
		Oid			eq_func;
		Oid			primary_type;
		int			j;

		primary_type = get_atttype(primary_relid, primary_joinkey);

		/* Get the equality operator for lookups */
		eq_opr = get_opfamily_member(get_opclass_family(
														GetDefaultOpClass(primary_type, BTREE_AM_OID)),
									 primary_type, primary_type,
									 BTEqualStrategyNumber);
		eq_func = get_opcode(eq_opr);

		ScanKeyInit(&scankey,
					other_joinkey,
					BTEqualStrategyNumber,
					eq_func,
					joinkey_value);

		/* Set collation for the scan key */
		scankey.sk_collation = TupleDescAttr(other_desc, other_joinkey - 1)->attcollation;

		/* TODO: table_beginscan does sequential scan - use index if available */
		scan = table_beginscan(other_rel, snapshot, 1, &scankey);
		orthertuple = heap_getnext(scan, ForwardScanDirection);

		/* Allocate arrays for all filter columns */
		mcvlist->items[i].frequency = frequency;
		mcvlist->items[i].isnull = (bool *) palloc(nfilters * sizeof(bool));
		mcvlist->items[i].values = (Datum *) palloc(nfilters * sizeof(Datum));

		if (HeapTupleIsValid(orthertuple))
		{
			/* Extract all filter column values */
			for (j = 0; j < nfilters; j++)
			{
				AttrNumber	filter_attr = filter_attnums->values[j];
				Datum		filter_value;
				bool		filter_isnull;

				filter_value = heap_getattr(orthertuple, filter_attr,
											other_desc, &filter_isnull);

				/* Copy the value if not null */
				if (!filter_isnull)
					filter_value = datumCopy(filter_value,
											 TupleDescAttr(other_desc, filter_attr - 1)->attbyval,
											 TupleDescAttr(other_desc, filter_attr - 1)->attlen);

				mcvlist->items[i].isnull[j] = filter_isnull;
				mcvlist->items[i].values[j] = filter_value;
			}
		}
		else
		{
			/* No matching row found - mark all filter values as NULL */
			for (j = 0; j < nfilters; j++)
			{
				mcvlist->items[i].isnull[j] = true;
				mcvlist->items[i].values[j] = (Datum) 0;
			}
		}

		table_endscan(scan);

		total_freq += frequency;
	}

	/* Clean up */
	if (pushed_snapshot)
		PopActiveSnapshot();

	table_close(other_rel, AccessShareLock);

	elog(DEBUG1, "statext_join_mcv_build: Built join MCV with %d items, ndimensions=%d, total_freq=%.3f",
		 num_primary_joinkey_mcvs, nfilters, total_freq);

	return mcvlist;
}

/*
 * statext_join_mcv_load
 *		Look up join MCV statistics from the catalog
 *
 * Uses the index on (stxrelid, stxotherrel) for lookup, then post-filters
 * on stxjoinkeys and filter_attnums since int2vector can't be indexed.
 *
 * Returns deserialized JoinMCVList if found, NULL otherwise.
 * The caller is responsible for freeing the returned structure.
 */
JoinMCVList *
statext_join_mcv_load(Oid relid,
					  AttrNumber rel_joinkey_attnum,
					  Oid other_relid,
					  AttrNumber otherrel_joinkey_attnum,
					  List *filter_attnums)
{
	Relation	statext_rel;
	Relation	statext_data_rel;
	SysScanDesc scan;
	ScanKeyData keys[2];
	HeapTuple	htup;
	JoinMCVList *mcvlist = NULL;
	int16		expected_joinkeys[2];

	/* Build expected joinkeys for comparison */
	expected_joinkeys[0] = rel_joinkey_attnum;
	expected_joinkeys[1] = otherrel_joinkey_attnum;

	/* Open both catalog relations */
	statext_rel = table_open(StatisticExtRelationId, AccessShareLock);
	statext_data_rel = table_open(StatisticExtDataRelationId, AccessShareLock);

	/*
	 * Use the index on (stxrelid, stxotherrel) to find statistics objects for
	 * this table pair.
	 */
	ScanKeyInit(&keys[0],
				Anum_pg_statistic_ext_stxrelid,
				BTEqualStrategyNumber, F_OIDEQ,
				ObjectIdGetDatum(relid));

	ScanKeyInit(&keys[1],
				Anum_pg_statistic_ext_stxotherrel,
				BTEqualStrategyNumber, F_OIDEQ,
				ObjectIdGetDatum(other_relid));

	scan = systable_beginscan(statext_rel, StatisticExtOtherrelIndexId, true,
							  NULL, 2, keys);

	/*
	 * Iterate through matching rows (typically 1-2 for a given table pair).
	 * Post-filter on stxjoinkeys and filter_attnums.
	 */
	while (HeapTupleIsValid(htup = systable_getnext(scan)))
	{
		Form_pg_statistic_ext st = (Form_pg_statistic_ext) GETSTRUCT(htup);
		Datum		datum;
		bool		isnull;
		int2vector *joinkeys;
		int2vector *stxkeys;
		bool		match = true;
		ArrayType  *arr;
		char	   *kinds;
		int			nkinds;
		bool		has_join_mcv = false;
		HeapTuple	data_htup;
		int			i,
					j;

		/* Skip if not join MCV type */
		datum = SysCacheGetAttrNotNull(STATEXTOID, htup, Anum_pg_statistic_ext_stxkind);
		arr = DatumGetArrayTypeP(datum);
		kinds = (char *) ARR_DATA_PTR(arr);
		nkinds = ArrayGetNItems(ARR_NDIM(arr), ARR_DIMS(arr));

		for (i = 0; i < nkinds; i++)
		{
			if (kinds[i] == STATS_EXT_JOIN_MCV)
			{
				has_join_mcv = true;
				break;
			}
		}

		if (!has_join_mcv)
			continue;

		/* Check stxjoinkeys matches */
		datum = SysCacheGetAttr(STATEXTOID, htup, Anum_pg_statistic_ext_stxjoinkeys, &isnull);
		if (isnull)
			continue;

		joinkeys = (int2vector *) DatumGetPointer(datum);
		if (joinkeys->dim1 != 2 ||
			joinkeys->values[0] != expected_joinkeys[0] ||
			joinkeys->values[1] != expected_joinkeys[1])
			continue;

		/* Check filter columns match (stxkeys) */
		datum = SysCacheGetAttrNotNull(STATEXTOID, htup, Anum_pg_statistic_ext_stxkeys);
		stxkeys = (int2vector *) DatumGetPointer(datum);

		if (filter_attnums != NIL)
		{
			/*
			 * Check if the stat contains ALL the queried filter columns. For
			 * marginalization, we allow the stat to have more columns than
			 * the query (subset matching), but the query columns must all be
			 * present in the stat.
			 *
			 * Example: Query filters on phonetic_code (col 3), stat has
			 * (keyword, phonetic_code) = {2, 3} -> match!
			 */
			ListCell   *lc;

			foreach(lc, filter_attnums)
			{
				AttrNumber	attnum = lfirst_int(lc);
				bool		found = false;

				for (j = 0; j < stxkeys->dim1; j++)
				{
					if (attnum == stxkeys->values[j])
					{
						found = true;
						break;
					}
				}
				if (!found)
				{
					match = false;
					break;
				}
			}

			if (!match)
				continue;
		}

		/*
		 * Found a matching stats object! Now load the join MCV data.
		 */
		data_htup = SearchSysCache2(STATEXTDATASTXOID,
									ObjectIdGetDatum(st->oid),
									BoolGetDatum(false));

		if (HeapTupleIsValid(data_htup))
		{
			datum = SysCacheGetAttr(STATEXTDATASTXOID, data_htup,
									Anum_pg_statistic_ext_data_stxdjoinmcv,
									&isnull);

			if (!isnull)
			{
				/* Deserialize the MCV list */
				mcvlist = statext_join_mcv_deserialize(DatumGetByteaP(datum));
				ReleaseSysCache(data_htup);
				break;			/* Found it! */
			}

			ReleaseSysCache(data_htup);
		}
	}

	systable_endscan(scan);
	table_close(statext_data_rel, AccessShareLock);
	table_close(statext_rel, AccessShareLock);

	return mcvlist;
}

/*
 * join_mcv_clauselist_selectivity
 *		Apply join MCV statistics to estimate selectivity
 *
 * Given a JoinMCVList and filter values, compute the selectivity by
 * summing the frequencies of MCV items that match the filter criteria.
 *
 * For single-column queries on multi-column stats, we compute the
 * marginal distribution by summing frequencies across non-queried
 * dimensions.
 *
 * For multi-column queries, we match ALL queried columns with their
 * corresponding dimensions and find MCV items where all dimensions match.
 */
Selectivity
join_mcv_clauselist_selectivity(JoinMCVList * mcvlist,
								List *filter_values,
								List *filter_attnums,
								Oid collation)
{
	int			item_idx;
	Selectivity total_sel;
	ListCell   *lc;
	ListCell   *lc_attnum;
	int			nqcols;
	int			qcol;
	int		   *qcol_dims;
	FmgrInfo   *eq_funcs;
	FunctionCallInfo *fcinfo_arr;

	if (!mcvlist || mcvlist->nitems == 0 || filter_values == NIL || filter_attnums == NIL)
		return 0.0;

	/*
	 * Map queried columns to stat dimensions.
	 *
	 * For single-column queries on multi-column stats, we compute the
	 * marginal distribution by summing frequencies across non-queried
	 * dimensions.
	 *
	 * For multi-column queries, we match ALL queried columns with their
	 * corresponding dimensions and find MCV items where all dimensions match.
	 */
	nqcols = list_length(filter_attnums);

	if (nqcols > STATS_MAX_DIMENSIONS)
	{
		elog(DEBUG1, "join_mcv_clauselist_selectivity: too many query columns: %d", nqcols);
		return 0.0;
	}
	qcol_dims = (int *) palloc(nqcols * sizeof(int));
	qcol = 0;

	/* Map each queried column to its dimension in the stat */
	foreach(lc_attnum, filter_attnums)
	{
		AttrNumber	qattnum = lfirst_int(lc_attnum);
		bool		found = false;

		for (int d = 0; d < mcvlist->ndimensions; d++)
		{
			if (mcvlist->filter_attnums[d] == qattnum)
			{
				qcol_dims[qcol] = d;
				found = true;
				break;
			}
		}

		if (!found)
		{
			elog(DEBUG1, "join_mcv_clauselist_selectivity: query attnum %d not found in stat", qattnum);
			return 0.0;
		}
		qcol++;
	}

	elog(DEBUG1, "join_mcv_clauselist_selectivity: matched %d query columns to stat dimensions (ndimensions=%d)",
		 nqcols, mcvlist->ndimensions);

	/* Setup equality functions for each queried dimension */
	eq_funcs = (FmgrInfo *) palloc(nqcols * sizeof(FmgrInfo));
	fcinfo_arr = (FunctionCallInfo *) palloc(nqcols * sizeof(FunctionCallInfo));

	for (qcol = 0; qcol < nqcols; qcol++)
	{
		int			dim = qcol_dims[qcol];
		Oid			qtype = mcvlist->filter_types[dim];
		TypeCacheEntry *typentry;
		Oid			eq_func_oid;

		typentry = lookup_type_cache(qtype, TYPECACHE_EQ_OPR);
		if (!OidIsValid(typentry->eq_opr))
			return 0.0;

		eq_func_oid = get_opcode(typentry->eq_opr);
		if (!OidIsValid(eq_func_oid))
			return 0.0;

		fmgr_info(eq_func_oid, &eq_funcs[qcol]);

		/* Allocate fcinfo for this dimension */
		fcinfo_arr[qcol] = (FunctionCallInfo) palloc(SizeForFunctionCallInfo(2));
		InitFunctionCallInfoData(*fcinfo_arr[qcol], &eq_funcs[qcol], 2, collation, NULL, NULL);
	}

	total_sel = 0.0;

	elog(DEBUG1, "join_mcv_clauselist_selectivity: searching %d filter values in %d MCV items",
		 list_length(filter_values), mcvlist->nitems);

	/* For single-column queries: iterate filter values */
	if (nqcols == 1)
	{
		int			dim = qcol_dims[0];
		bool	   *matched_items;

		/*
		 * Track which MCV items have been matched to avoid double-counting
		 * when multiple filter values match the same MCV item.
		 */
		matched_items = (bool *) palloc0(mcvlist->nitems * sizeof(bool));

		foreach(lc, filter_values)
		{
			Datum		filter_value = PointerGetDatum(lfirst(lc));

			fcinfo_arr[0]->args[1].value = filter_value;
			fcinfo_arr[0]->args[1].isnull = false;

			for (item_idx = 0; item_idx < mcvlist->nitems; item_idx++)
			{
				JoinMCVItem *item;
				Datum		fresult;

				if (matched_items[item_idx])
					continue;

				item = &mcvlist->items[item_idx];

				if (item->isnull[dim])
					continue;

				fcinfo_arr[0]->args[0].value = item->values[dim];
				fcinfo_arr[0]->args[0].isnull = false;
				fcinfo_arr[0]->isnull = false;

				fresult = FunctionCallInvoke(fcinfo_arr[0]);

				if (!fcinfo_arr[0]->isnull && DatumGetBool(fresult))
				{
					elog(DEBUG1, "  MATCH at item[%d] dim[%d], frequency=%.6f", item_idx, dim, item->frequency);
					total_sel += item->frequency;
					matched_items[item_idx] = true;

					if (mcvlist->ndimensions == 1)
						break;
				}
			}
		}
	}
	/* For multi-column queries: exact match on all dimensions */
	else
	{
		Datum	   *query_values;

		/*
		 * TODO: Support IN clauses on multiple columns. Currently we only
		 * support exact equality (one value per column) in multi-column
		 * filters.
		 */
		if (list_length(filter_values) != nqcols)
		{
			elog(DEBUG1, "join MCV selectivity: multi-column IN clauses not yet supported (expected %d values, got %d)",
				 nqcols, list_length(filter_values));
			return 0.0;
		}

		/* Extract query values for each dimension */
		query_values = (Datum *) palloc(nqcols * sizeof(Datum));
		qcol = 0;
		foreach(lc, filter_values)
		{
			/* Each element should be a single-element list for equality */
			List	   *val_list = (List *) lfirst(lc);

			if (list_length(val_list) != 1)
			{
				elog(DEBUG1, "join MCV selectivity: multi-value filters not yet supported for multi-column filters");
				return 0.0;
			}
			query_values[qcol] = PointerGetDatum(linitial(val_list));
			qcol++;
		}

		/* Find MCV items that match on ALL queried dimensions */
		for (item_idx = 0; item_idx < mcvlist->nitems; item_idx++)
		{
			JoinMCVItem *item = &mcvlist->items[item_idx];
			bool		all_match = true;

			/* Check each queried dimension */
			for (qcol = 0; qcol < nqcols; qcol++)
			{
				int			dim = qcol_dims[qcol];
				Datum		fresult;

				if (item->isnull[dim])
				{
					all_match = false;
					break;
				}

				fcinfo_arr[qcol]->args[0].value = item->values[dim];
				fcinfo_arr[qcol]->args[0].isnull = false;
				fcinfo_arr[qcol]->args[1].value = query_values[qcol];
				fcinfo_arr[qcol]->args[1].isnull = false;
				fcinfo_arr[qcol]->isnull = false;

				fresult = FunctionCallInvoke(fcinfo_arr[qcol]);

				if (fcinfo_arr[qcol]->isnull || !DatumGetBool(fresult))
				{
					all_match = false;
					break;
				}
			}

			if (all_match)
			{
				elog(DEBUG1, "  MATCH at item[%d] (all %d dimensions), frequency=%.6f", item_idx, nqcols, item->frequency);
				total_sel += item->frequency;
			}
		}
	}

	elog(DEBUG1, "join_mcv_clauselist_selectivity: total_sel=%.6f", total_sel);

	/*
	 * For IN clauses with multiple values, return PER-VALUE selectivity.
	 * PostgreSQL's join size formula multiplies by inner_rows (number of
	 * values in IN list), so returning per-value selectivity gives the
	 * correct result.
	 *
	 * Currently only single-column queries support multiple filter values;
	 * multi-column queries bails out early. When multi-column IN support is
	 * added, this adjustment will apply there too.
	 */
	if (nqcols == 1 && list_length(filter_values) > 1)
	{
		int			num_values = list_length(filter_values);

		elog(DEBUG1, "join_mcv_clauselist_selectivity: IN clause with %d values, returning per-value: %.6f / %d = %.6f",
			 num_values, total_sel, num_values, total_sel / num_values);

		total_sel /= num_values;
	}

	return total_sel;
}

/*
 * extract_filter_info
 *		Extract filter column and constant value(s) from a filter clause
 *
 * Handles two types of filter clauses:
 * 1. OpExpr: col = constant
 * 2. ScalarArrayOpExpr: col IN (const1, const2, ...)
 *
 * Returns true if a valid filter pattern is found, false otherwise.
 * On success, sets *filter_var, *filter_values (list of Datums),
 * *filter_type, *collation, and *is_in_clause.
 */
static bool
extract_filter_info(Node *clause,
					Index expected_relid,
					Var **filter_var,
					List **filter_values,
					Oid *filter_type,
					Oid *collation,
					bool *is_in_clause)
{
	*filter_var = NULL;
	*filter_values = NIL;
	*is_in_clause = false;

	/* Case 1: OpExpr - simple equality (col = const) */
	if (IsA(clause, OpExpr))
	{
		OpExpr	   *opexpr = (OpExpr *) clause;
		Node	   *var_node = NULL;
		Const	   *const_node = NULL;
		bool		expronleft;

		if (list_length(opexpr->args) != 2)
			return false;

		/* Check for pattern: Var = Const or Const = Var */
		if (!examine_opclause_args(opexpr->args, &var_node, &const_node, &expronleft))
			return false;

		if (!var_node || !const_node || !IsA(var_node, Var))
			return false;

		*filter_var = (Var *) var_node;

		/* Verify the Var is from the expected relation */
		if ((*filter_var)->varno != expected_relid)
			return false;

		/* Create single-element list - store Datum as pointer */
		*filter_values = list_make1(DatumGetPointer(const_node->constvalue));
		*filter_type = const_node->consttype;
		*collation = (*filter_var)->varcollid;
		*is_in_clause = false;

		return true;
	}

	/* Case 2: ScalarArrayOpExpr - IN clause (col IN (...)) */
	else if (IsA(clause, ScalarArrayOpExpr))
	{
		ScalarArrayOpExpr *saop = (ScalarArrayOpExpr *) clause;
		Node	   *scalar_node;
		Node	   *array_node;
		Const	   *array_const;
		ArrayType  *arr;
		int			nitems;
		Datum	   *items;
		bool	   *nulls;
		int			i;
		Oid			elmtype;
		int16		elmlen;
		bool		elmbyval;
		char		elmalign;

		/* Only support ANY (IN), not ALL */
		if (!saop->useOr)
			return false;

		if (list_length(saop->args) != 2)
			return false;

		scalar_node = (Node *) linitial(saop->args);
		array_node = (Node *) lsecond(saop->args);

		/* Strip any RelabelType nodes (e.g., varchar cast to text) */
		scalar_node = strip_implicit_coercions(scalar_node);

		/* Scalar must be a Var after stripping coercions */
		if (!IsA(scalar_node, Var))
			return false;

		*filter_var = (Var *) scalar_node;

		/* Verify the Var is from the expected relation */
		if ((*filter_var)->varno != expected_relid)
			return false;

		/* Array must be a Const for us to extract values */
		if (!IsA(array_node, Const))
			return false;

		array_const = (Const *) array_node;

		/* Can't handle NULL arrays */
		if (array_const->constisnull)
			return false;

		/* Deconstruct the array */
		arr = DatumGetArrayTypeP(array_const->constvalue);
		elmtype = ARR_ELEMTYPE(arr);

		/* Get type info for deconstruction */
		get_typlenbyvalalign(elmtype, &elmlen, &elmbyval, &elmalign);

		deconstruct_array(arr, elmtype, elmlen, elmbyval, elmalign,
						  &items, &nulls, &nitems);

		/* Build list of non-NULL Datums */
		*filter_values = NIL;
		for (i = 0; i < nitems; i++)
		{
			if (!nulls[i])
			{
				/*
				 * Store Datum as pointer - safe since Datum and pointer are
				 * same size
				 */
				*filter_values = lappend(*filter_values, DatumGetPointer(items[i]));
			}
		}

		/* If all values were NULL, we can't use this */
		if (*filter_values == NIL)
			return false;

		*filter_type = elmtype;
		*collation = saop->inputcollid;
		*is_in_clause = true;

		return true;
	}

	return false;
}

/*
 * find_join_mcv_opportunity
 *		Detect if a join+filter combination can use join MCV statistics.
 *
 * Looks for two patterns:
 *
 * Pattern 1: outer_rel (referencing) JOIN inner_rel (referenced)
 *            WHERE inner_rel.col = constant [or IN (...)]
 * Pattern 2: outer_rel (referenced) JOIN inner_rel (referencing)
 *            WHERE outer_rel.col = constant [or IN (...)]
 *
 * Returns an allocated JoinMCVOpportunity if pattern is found, NULL otherwise.
 * The caller is responsible for freeing the returned structure.
 */
JoinMCVOpportunity *
find_join_mcv_opportunity(PlannerInfo *root,
						  RelOptInfo *outer_rel,
						  RelOptInfo *inner_rel,
						  List *restrictlist)
{
	ListCell   *lc;
	Var		   *join_var_outer = NULL;
	Var		   *join_var_inner = NULL;
	RestrictInfo *join_rinfo = NULL;
	RelOptInfo *filtered_rel;
	Var		   *filtered_var;
	Var		   *target_var;
	RangeTblEntry *filtered_rte;
	RangeTblEntry *target_rte;
	List	   *filter_attnums_list = NIL;
	List	   *filter_values_list = NIL;
	List	   *filter_types_list = NIL;
	List	   *filter_rinfos_list = NIL;
	Oid			collation = InvalidOid;
	bool		all_filters_valid = true;
	JoinMCVOpportunity *join_opp;

	/* Find join clause: outer_rel.col = inner_rel.col */
	foreach(lc, restrictlist)
	{
		RestrictInfo *rinfo;
		OpExpr	   *opexpr;
		Var		   *left_var;
		Var		   *right_var;
		Node	   *node = lfirst(lc);

		/*
		 * Skip if not a RestrictInfo. During index path costing, restrictlist
		 * can contain raw expression nodes (OpExpr, ScalarArrayOpExpr, etc.)
		 * from index predicates, not just RestrictInfo wrappers.
		 */
		if (!IsA(node, RestrictInfo))
			continue;

		rinfo = (RestrictInfo *) node;
		if (!IsA(rinfo->clause, OpExpr))
			continue;

		opexpr = (OpExpr *) rinfo->clause;

		if (list_length(opexpr->args) != 2)
			continue;

		/* FIXME: Extract left and right arguments smarter */
		left_var = (Var *) linitial(opexpr->args);
		right_var = (Var *) lsecond(opexpr->args);

		/* Check if this matches our join pattern */
		if (IsA(left_var, Var) && IsA(right_var, Var))
		{
			if (bms_is_member(left_var->varno, outer_rel->relids) &&
				bms_is_member(right_var->varno, inner_rel->relids))
			{
				join_var_outer = left_var;
				join_var_inner = right_var;
				join_rinfo = rinfo;
				break;
			}
			else if (bms_is_member(right_var->varno, outer_rel->relids) &&
					 bms_is_member(left_var->varno, inner_rel->relids))
			{
				join_var_outer = right_var;
				join_var_inner = left_var;
				join_rinfo = rinfo;
				break;
			}
		}
	}

	if (!join_var_outer || !join_var_inner || !join_rinfo)
		return NULL;			/* No join clause found */

	/*
	 * Find filter clauses: other_rel.col = constant [or IN (...)]
	 *
	 * Determine which relation has filter conditions. We look for a base
	 * relation (singleton) with baserestrictinfo clauses.
	 */
	if (bms_membership(inner_rel->relids) == BMS_SINGLETON &&
		inner_rel->baserestrictinfo != NIL)
	{
		/* Pattern 1: inner has filters, outer is target */
		filtered_rel = inner_rel;
		filtered_var = join_var_inner;
		target_var = join_var_outer;
	}
	else if (bms_membership(outer_rel->relids) == BMS_SINGLETON &&
			 outer_rel->baserestrictinfo != NIL)
	{
		/* Pattern 2: outer has filters, inner is target */
		filtered_rel = outer_rel;
		filtered_var = join_var_outer;
		target_var = join_var_inner;
	}
	else
	{
		/* No base relation with filters found */
		return NULL;
	}

	/* Try to extract filter info from ALL baserestrictinfo clauses */
	foreach(lc, filtered_rel->baserestrictinfo)
	{
		RestrictInfo *rinfo = lfirst_node(RestrictInfo, lc);
		Var		   *filter_var;
		List	   *filter_values;
		Oid			filter_type;
		Oid			filter_collation;
		bool		filter_is_in;

		if (extract_filter_info((Node *) rinfo->clause, filtered_rel->relid,
								&filter_var, &filter_values, &filter_type,
								&filter_collation, &filter_is_in))
		{
			filter_attnums_list = lappend_int(filter_attnums_list, filter_var->varattno);
			filter_values_list = lappend(filter_values_list, filter_values);
			filter_types_list = lappend_oid(filter_types_list, filter_type);
			filter_rinfos_list = lappend(filter_rinfos_list, rinfo);

			/* Use first filter's collation (should be consistent) */
			if (!OidIsValid(collation))
				collation = filter_collation;
		}
		else
		{
			/* This filter clause doesn't match our pattern */
			all_filters_valid = false;
			break;
		}
	}

	/* If all filters were successfully extracted, create the match */
	if (!all_filters_valid || filter_attnums_list == NIL)
		return NULL;

	/* Build the JoinMCVOpportunity result */
	join_opp = palloc(sizeof(JoinMCVOpportunity));

	/* Use Var's varno to get the actual table RTEs, not the join relid */
	target_rte = root->simple_rte_array[target_var->varno];
	filtered_rte = root->simple_rte_array[filtered_var->varno];

	join_opp->target_rel = target_rte->relid;
	join_opp->target_joinkey = target_var->varattno;
	join_opp->other_rel = filtered_rte->relid;
	join_opp->other_joinkey = filtered_var->varattno;
	join_opp->filter_attnums = filter_attnums_list;
	join_opp->filter_values = list_length(filter_values_list) == 1 ?
		linitial(filter_values_list) : filter_values_list;
	join_opp->collation = collation;

	/* Track which clauses were used */
	join_opp->join_rinfos = list_make1(join_rinfo);
	join_opp->filter_rinfos = filter_rinfos_list;

	return join_opp;
}

/*
 * find_join_mcv_opportunity_in_clauses
 *		Detect join MCV opportunity from a list of clauses
 *
 * Examines the clause list to identify if exactly two base relations are involved,
 * then calls find_join_mcv_opportunity() with those relations.
 *
 * Returns NULL if no join mcv stats would possibly be applicable.
 */
JoinMCVOpportunity *
find_join_mcv_opportunity_in_clauses(PlannerInfo *root, List *clauses)
{
	Relids		clause_relids = NULL;
	ListCell   *lc;
	int			relid1 = -1;
	int			relid2 = -1;
	RelOptInfo *rel1;
	RelOptInfo *rel2;
	JoinMCVOpportunity *join_opp;

	/* Collect all relids mentioned in clauses */
	foreach(lc, clauses)
	{
		RestrictInfo *rinfo;

		if (!IsA(lfirst(lc), RestrictInfo))
			continue;

		rinfo = (RestrictInfo *) lfirst(lc);
		clause_relids = bms_union(clause_relids, rinfo->clause_relids);
	}

	if (clause_relids == NULL)
		return NULL;

	/* Extract exactly two base relids */
	relid1 = bms_next_member(clause_relids, -1);
	if (relid1 < 0)
		return NULL;

	relid2 = bms_next_member(clause_relids, relid1);
	if (relid2 < 0)
		return NULL;			/* Only one relation */

	if (bms_next_member(clause_relids, relid2) >= 0)
		return NULL;			/* More than two relations */

	/* Get RelOptInfo for both relations (skip if not base relations) */
	rel1 = find_base_rel_ignore_join(root, relid1);
	rel2 = find_base_rel_ignore_join(root, relid2);

	if (!rel1 || !rel2)
		return NULL;			/* One or both are join relations, not base
								 * tables */

	/* Call the main detection function - try both orders */
	join_opp = find_join_mcv_opportunity(root, rel1, rel2, clauses);
	if (join_opp)
		return join_opp;

	return find_join_mcv_opportunity(root, rel2, rel1, clauses);
}

/*
 * pg_join_mcv_list_items
 *		Returns a set of rows with information about join MCV items.
 *
 * For the lean structure, we only return filter column values (no join values).
 * Returns tuples with:
 * - index (int)
 * - values (text[]) - filter column values as text array
 * - nulls (bool[]) - NULL flags for filter columns
 * - frequency (float8)
 */
Datum
pg_join_mcv_list_items(PG_FUNCTION_ARGS)
{
	FuncCallContext *funcctx;

	if (SRF_IS_FIRSTCALL())
	{
		MemoryContext oldcontext;
		JoinMCVList *mcvlist;
		TupleDesc	tupdesc;

		funcctx = SRF_FIRSTCALL_INIT();
		oldcontext = MemoryContextSwitchTo(funcctx->multi_call_memory_ctx);

		mcvlist = statext_join_mcv_deserialize(PG_GETARG_BYTEA_P(0));
		funcctx->user_fctx = mcvlist;

		funcctx->max_calls = 0;
		if (mcvlist != NULL)
			funcctx->max_calls = mcvlist->nitems;

		if (get_call_result_type(fcinfo, NULL, &tupdesc) != TYPEFUNC_COMPOSITE)
			ereport(ERROR,
					(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
					 errmsg("function returning record called in context that cannot accept type record")));

		funcctx->tuple_desc = BlessTupleDesc(tupdesc);
		MemoryContextSwitchTo(oldcontext);
	}

	funcctx = SRF_PERCALL_SETUP();

	if (funcctx->call_cntr < funcctx->max_calls)
	{
		Datum		values[4];
		bool		nulls[4];
		HeapTuple	tuple;
		JoinMCVList *mcvlist;
		JoinMCVItem *item;
		int			i;
		int			dims[1];
		int			lbs[1];
		Datum	   *text_values;
		bool	   *text_nulls;
		ArrayType  *text_array;
		ArrayType  *nulls_array;

		mcvlist = (JoinMCVList *) funcctx->user_fctx;
		item = &mcvlist->items[funcctx->call_cntr];

		if (mcvlist->ndimensions <= 0 || mcvlist->ndimensions > STATS_MAX_DIMENSIONS)
			elog(ERROR, "pg_join_mcv_list_items: corrupted mcvlist->ndimensions=%d (magic=%u, nitems=%u)",
				 mcvlist->ndimensions, mcvlist->magic, mcvlist->nitems);

		values[0] = Int32GetDatum(funcctx->call_cntr);
		nulls[0] = false;

		/* values[] - convert filter Datums to text array */
		text_values = (Datum *) palloc(mcvlist->ndimensions * sizeof(Datum));
		text_nulls = (bool *) palloc(mcvlist->ndimensions * sizeof(bool));

		for (i = 0; i < mcvlist->ndimensions; i++)
		{
			if (item->isnull[i])
			{
				text_values[i] = (Datum) 0;
				text_nulls[i] = true;
			}
			else
			{
				Oid			outfunc;
				bool		isvarlena;

				getTypeOutputInfo(mcvlist->filter_types[i], &outfunc, &isvarlena);
				text_values[i] = PointerGetDatum(cstring_to_text(
																 OidOutputFunctionCall(outfunc, item->values[i])));
				text_nulls[i] = false;
			}
		}
		dims[0] = mcvlist->ndimensions;
		lbs[0] = 1;				/* Arrays are 1-indexed */

		text_array = construct_md_array(text_values, text_nulls, 1, dims, lbs, TEXTOID, -1, false, TYPALIGN_INT);
		values[1] = PointerGetDatum(text_array);
		nulls[1] = false;

		/* Convert bool array to Datum array */
		{
			Datum	   *bool_datums = (Datum *) palloc(mcvlist->ndimensions * sizeof(Datum));

			for (i = 0; i < mcvlist->ndimensions; i++)
				bool_datums[i] = BoolGetDatum(item->isnull[i]);

			nulls_array = construct_array(bool_datums, mcvlist->ndimensions, BOOLOID,
										  sizeof(bool), true, TYPALIGN_CHAR);
			pfree(bool_datums);
		}
		values[2] = PointerGetDatum(nulls_array);
		nulls[2] = false;

		/* frequency */
		values[3] = Float8GetDatum(item->frequency);
		nulls[3] = false;

		tuple = heap_form_tuple(funcctx->tuple_desc, values, nulls);
		SRF_RETURN_NEXT(funcctx, HeapTupleGetDatum(tuple));
	}

	SRF_RETURN_DONE(funcctx);
}

/*
 * pg_join_mcv_list_in - input routine for type pg_join_mcv_list.
 *
 * pg_join_mcv_list stores data in binary form and parsing text input
 * is not needed, so disallow this.
 */
Datum
pg_join_mcv_list_in(PG_FUNCTION_ARGS)
{
	ereport(ERROR,
			(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
			 errmsg("cannot accept a value of type %s", "pg_join_mcv_list")));

	PG_RETURN_VOID();			/* keep compiler quiet */
}

/*
 * pg_join_mcv_list_out - output routine for type pg_join_mcv_list.
 *
 * Join MCV lists are serialized into a bytea value, so we simply call
 * byteaout() to serialize the value into text.
 */
Datum
pg_join_mcv_list_out(PG_FUNCTION_ARGS)
{
	return byteaout(fcinfo);
}

/*
 * pg_join_mcv_list_recv - binary input routine for type pg_join_mcv_list.
 */
Datum
pg_join_mcv_list_recv(PG_FUNCTION_ARGS)
{
	ereport(ERROR,
			(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
			 errmsg("cannot accept a value of type %s", "pg_join_mcv_list")));

	PG_RETURN_VOID();			/* keep compiler quiet */
}

/*
 * pg_join_mcv_list_send - binary output routine for type pg_join_mcv_list.
 */
Datum
pg_join_mcv_list_send(PG_FUNCTION_ARGS)
{
	return byteasend(fcinfo);
}
