/*-------------------------------------------------------------------------
 *
 * statscmds.c
 *	  Commands for creating and altering extended statistics objects
 *
 * Portions Copyright (c) 1996-2026, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/commands/statscmds.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/genam.h"
#include "access/htup_details.h"
#include "access/relation.h"
#include "access/table.h"
#include "catalog/catalog.h"
#include "catalog/dependency.h"
#include "catalog/indexing.h"
#include "catalog/namespace.h"
#include "catalog/objectaccess.h"
#include "catalog/pg_namespace.h"
#include "catalog/pg_statistic_ext.h"
#include "catalog/pg_statistic_ext_data.h"
#include "commands/comment.h"
#include "commands/defrem.h"
#include "miscadmin.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "optimizer/optimizer.h"
#include "statistics/extended_stats_internal.h"
#include "statistics/statistics.h"
#include "utils/acl.h"
#include "utils/builtins.h"
#include "utils/inval.h"
#include "utils/lsyscache.h"
#include "utils/rel.h"
#include "utils/syscache.h"
#include "utils/typcache.h"


static char *ChooseExtendedStatisticName(const char *name1, const char *name2,
										 const char *label, Oid namespaceid);
static char *ChooseExtendedStatisticNameAddition(List *exprs);


/* qsort comparator for the attnums in CreateStatistics */
static int
compare_int16(const void *a, const void *b)
{
	int			av = *(const int16 *) a;
	int			bv = *(const int16 *) b;

	/* this can't overflow if int is wider than int16 */
	return (av - bv);
}

/*
 *		CREATE STATISTICS
 */
ObjectAddress
CreateStatistics(CreateStatsStmt *stmt, bool check_rights)
{
	int16		attnums[STATS_MAX_DIMENSIONS];
	int			nattnums = 0;
	int			numcols;
	char	   *namestr;
	NameData	stxname;
	Oid			statoid;
	Oid			namespaceId;
	Oid			stxowner = GetUserId();
	HeapTuple	htup;
	Datum		values[Natts_pg_statistic_ext];
	bool		nulls[Natts_pg_statistic_ext];
	int2vector *stxkeys;
	List	   *stxexprs = NIL;
	Datum		exprsDatum;
	Relation	statrel;
	Relation	rel = NULL;
	Oid			relid = InvalidOid;
	ObjectAddress parentobject,
				myself;
	Datum		types[4];		/* one for each possible type of statistic */
	int			ntypes;
	ArrayType  *stxkind;
	bool		build_ndistinct;
	bool		build_dependencies;
	bool		build_mcv;
	bool		build_expressions;
	bool		requested_type = false;
	int			i;
	ListCell   *cell;
	ListCell   *cell2;
	ListCell   *lc;
	Node	   *rln;
	bool		isjoin = false;
	List	   *other_rels = NIL;
	int		   *key_varnos = NULL;	/* stats key's varnos, for joins */
	List	   *join_idx_oids = NIL;

	Assert(IsA(stmt, CreateStatsStmt));

	/*
	 * Examine the FROM clause. We support either: 1. Single RangeVar for
	 * single-table statistics 2. JoinExpr for join statistics
	 */
	if (list_length(stmt->relations) != 1)
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("only a single relation or JOIN is allowed in CREATE STATISTICS")));

	rln = (Node *) linitial(stmt->relations);

	if (IsA(rln, RangeVar))
	{
		/*
		 * CREATE STATISTICS will influence future execution plans but does
		 * not interfere with currently executing plans.  So it should be
		 * enough to take only ShareUpdateExclusiveLock on relation,
		 * conflicting with ANALYZE and other DDL that sets statistical
		 * information, but not with normal queries.
		 */
		rel = relation_openrv((RangeVar *) rln, ShareUpdateExclusiveLock);

		/* Restrict to allowed relation types */
		if (rel->rd_rel->relkind != RELKIND_RELATION &&
			rel->rd_rel->relkind != RELKIND_MATVIEW &&
			rel->rd_rel->relkind != RELKIND_FOREIGN_TABLE &&
			rel->rd_rel->relkind != RELKIND_PARTITIONED_TABLE)
			ereport(ERROR,
					(errcode(ERRCODE_WRONG_OBJECT_TYPE),
					 errmsg("cannot define statistics for relation \"%s\"",
							RelationGetRelationName(rel)),
					 errdetail_relkind_not_supported(rel->rd_rel->relkind)));

		/*
		 * You must own the relation to create stats on it.
		 *
		 * NB: Concurrent changes could cause this function's lookup to find a
		 * different relation than a previous lookup by the caller, so we must
		 * perform this check even when check_rights == false.
		 */
		if (!object_ownercheck(RelationRelationId, RelationGetRelid(rel), stxowner))
			aclcheck_error(ACLCHECK_NOT_OWNER, get_relkind_objtype(rel->rd_rel->relkind),
						   RelationGetRelationName(rel));

		/* Creating statistics on system catalogs is not allowed */
		if (!allowSystemTableMods && IsSystemRelation(rel))
			ereport(ERROR,
					(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
					 errmsg("permission denied: \"%s\" is a system catalog",
							RelationGetRelationName(rel))));

		relid = RelationGetRelid(rel);
	}
	else if (IsA(rln, JoinExpr))
	{
		Assert(stmt->transformed);
		isjoin = true;
		relid = stmt->stxrelid;
	}
	else
	{
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("only a single relation or JOIN is allowed in CREATE STATISTICS")));
	}

	/*
	 * Make sure no more than STATS_MAX_DIMENSIONS columns are used. There
	 * might be duplicates and so on, but we'll deal with those later.
	 */
	numcols = list_length(stmt->exprs);
	if (numcols > STATS_MAX_DIMENSIONS)
		ereport(ERROR,
				(errcode(ERRCODE_TOO_MANY_COLUMNS),
				 errmsg("cannot have more than %d columns in statistics",
						STATS_MAX_DIMENSIONS)));

	/*
	 * Convert the expression list to a simple array of attnums, but also keep
	 * a list of more complex expressions.  While at it, enforce some
	 * constraints - we don't allow extended statistics on system attributes,
	 * and we require the data type to have a less-than operator, if we're
	 * building multivariate statistics.
	 *
	 * There are many ways to "mask" a simple attribute reference as an
	 * expression, for example "(a+0)" etc. We can't possibly detect all of
	 * them, but we handle at least the simple case with the attribute in
	 * parens. There'll always be a way around this, if the user is determined
	 * (like the "(a+0)" example), but this makes it somewhat consistent with
	 * how indexes treat attributes/expressions.
	 */
	foreach(cell, stmt->exprs)
	{
		StatsElem  *selem = lfirst_node(StatsElem, cell);

		if (selem->name)		/* column reference */
		{
			char	   *attname;
			HeapTuple	atttuple;
			Form_pg_attribute attForm;
			TypeCacheEntry *type;

			/* Join stats require table-qualified column names */
			if (isjoin)
				ereport(ERROR,
						(errcode(ERRCODE_INVALID_COLUMN_REFERENCE),
						 errmsg("join statistics require table-qualified column names")));

			attname = selem->name;

			atttuple = SearchSysCacheAttName(relid, attname);
			if (!HeapTupleIsValid(atttuple))
				ereport(ERROR,
						(errcode(ERRCODE_UNDEFINED_COLUMN),
						 errmsg("column \"%s\" does not exist",
								attname)));
			attForm = (Form_pg_attribute) GETSTRUCT(atttuple);

			/* Disallow use of system attributes in extended stats */
			if (attForm->attnum <= 0)
				ereport(ERROR,
						(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
						 errmsg("statistics creation on system columns is not supported")));

			/*
			 * Disallow data types without a less-than operator in
			 * multivariate statistics.
			 */
			if (numcols > 1)
			{
				type = lookup_type_cache(attForm->atttypid, TYPECACHE_LT_OPR);
				if (type->lt_opr == InvalidOid)
					ereport(ERROR,
							(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
							 errmsg("cannot create multivariate statistics on column \"%s\"",
									attname),
							 errdetail("The type %s has no default btree operator class.",
									   format_type_be(attForm->atttypid))));
			}

			/* Treat virtual generated columns as expressions */
			if (attForm->attgenerated == ATTRIBUTE_GENERATED_VIRTUAL)
			{
				Node	   *expr;

				expr = (Node *) makeVar(1,
										attForm->attnum,
										attForm->atttypid,
										attForm->atttypmod,
										attForm->attcollation,
										0);
				stxexprs = lappend(stxexprs, expr);
			}
			else
			{
				attnums[nattnums] = attForm->attnum;
				nattnums++;
			}
			ReleaseSysCache(atttuple);
		}
		else if (IsA(selem->expr, Var)) /* column reference in parens */
		{
			Var		   *var = (Var *) selem->expr;
			TypeCacheEntry *type;

			/* Disallow use of system attributes in extended stats */
			if (var->varattno <= 0)
				ereport(ERROR,
						(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
						 errmsg("statistics creation on system columns is not supported")));

			/* For join stats, record which table each column comes from. */
			if (isjoin)
			{
				type = lookup_type_cache(var->vartype, TYPECACHE_LT_OPR);
				if (type->lt_opr == InvalidOid)
					ereport(ERROR,
							(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
							 errmsg("cannot create multivariate statistics on column \"%s\"",
									get_attname(relid, var->varattno, false)),
							 errdetail("The type %s has no default btree operator class.",
									   format_type_be(var->vartype))));

				/* Allocate key_varnos on first use */
				if (key_varnos == NULL)
					key_varnos = palloc0(STATS_MAX_DIMENSIONS * sizeof(int));

				key_varnos[nattnums] = var->varno;
				attnums[nattnums] = var->varattno;
				nattnums++;
			}
			else
			{
				/*
				 * Disallow data types without a less-than operator in
				 * multivariate statistics.
				 */
				if (numcols > 1)
				{
					type = lookup_type_cache(var->vartype, TYPECACHE_LT_OPR);
					if (type->lt_opr == InvalidOid)
						ereport(ERROR,
								(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
								 errmsg("column \"%s\" cannot be used in multivariate statistics because its type %s has no default btree operator class",
										get_attname(relid, var->varattno, false), format_type_be(var->vartype))));
				}

				/* Treat virtual generated columns as expressions */
				if (get_attgenerated(relid, var->varattno) == ATTRIBUTE_GENERATED_VIRTUAL)
				{
					stxexprs = lappend(stxexprs, (Node *) var);
				}
				else
				{
					attnums[nattnums] = var->varattno;
					nattnums++;
				}
			}
		}
		else					/* expression */
		{
			Node	   *expr = selem->expr;
			Oid			atttype;
			TypeCacheEntry *type;
			Bitmapset  *attnums = NULL;
			int			k;

			Assert(expr != NULL);

			/* Join stats only support simple column references */
			if (isjoin)
				ereport(ERROR,
						(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
						 errmsg("expressions are not supported in join statistics")));

			pull_varattnos(expr, 1, &attnums);

			k = -1;
			while ((k = bms_next_member(attnums, k)) >= 0)
			{
				AttrNumber	attnum = k + FirstLowInvalidHeapAttributeNumber;

				/* Disallow expressions referencing system attributes. */
				if (attnum <= 0)
					ereport(ERROR,
							(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
							 errmsg("statistics creation on system columns is not supported")));
			}

			/*
			 * Disallow data types without a less-than operator in
			 * multivariate statistics.
			 */
			if (numcols > 1)
			{
				atttype = exprType(expr);
				type = lookup_type_cache(atttype, TYPECACHE_LT_OPR);
				if (type->lt_opr == InvalidOid)
					ereport(ERROR,
							(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
							 errmsg("cannot create multivariate statistics on this expression"),
							 errdetail("The type %s has no default btree operator class.",
									   format_type_be(atttype))));
			}

			stxexprs = lappend(stxexprs, expr);
		}
	}

	/*
	 * For join statistics, open and validate all participating relations. The
	 * join info (stxrelid, stxjoinrels, stxjoinconds) was already resolved
	 * and validated by transformStatsStmt().
	 */
	if (isjoin)
	{
		/* Open anchor relation and validate */
		rel = relation_open(relid, NoLock);

		if (rel->rd_rel->relkind != RELKIND_RELATION &&
			rel->rd_rel->relkind != RELKIND_MATVIEW &&
			rel->rd_rel->relkind != RELKIND_FOREIGN_TABLE &&
			rel->rd_rel->relkind != RELKIND_PARTITIONED_TABLE)
			ereport(ERROR,
					(errcode(ERRCODE_WRONG_OBJECT_TYPE),
					 errmsg("cannot define statistics for relation \"%s\"",
							RelationGetRelationName(rel)),
					 errdetail_relkind_not_supported(rel->rd_rel->relkind)));
		if (!object_ownercheck(RelationRelationId, relid, stxowner))
			aclcheck_error(ACLCHECK_NOT_OWNER,
						   get_relkind_objtype(rel->rd_rel->relkind),
						   RelationGetRelationName(rel));
		if (!allowSystemTableMods && IsSystemRelation(rel))
			ereport(ERROR,
					(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
					 errmsg("permission denied: \"%s\" is a system catalog",
							RelationGetRelationName(rel))));

		/* Open all join relations and validate */
		foreach(lc, stmt->stxjoinrels)
		{
			Relation	jrel = relation_open(lfirst_oid(lc), NoLock);

			if (jrel->rd_rel->relkind != RELKIND_RELATION &&
				jrel->rd_rel->relkind != RELKIND_MATVIEW &&
				jrel->rd_rel->relkind != RELKIND_FOREIGN_TABLE &&
				jrel->rd_rel->relkind != RELKIND_PARTITIONED_TABLE)
				ereport(ERROR,
						(errcode(ERRCODE_WRONG_OBJECT_TYPE),
						 errmsg("cannot define statistics for relation \"%s\"",
								RelationGetRelationName(jrel)),
						 errdetail_relkind_not_supported(jrel->rd_rel->relkind)));
			if (!object_ownercheck(RelationRelationId,
								   RelationGetRelid(jrel), stxowner))
				aclcheck_error(ACLCHECK_NOT_OWNER,
							   get_relkind_objtype(jrel->rd_rel->relkind),
							   RelationGetRelationName(jrel));
			if (!allowSystemTableMods && IsSystemRelation(jrel))
				ereport(ERROR,
						(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
						 errmsg("permission denied: \"%s\" is a system catalog",
								RelationGetRelationName(jrel))));

			other_rels = lappend(other_rels, jrel);
		}

		/*
		 * Validate that a suitable index exists for each join condition.
		 *
		 * Index-based sampling starts from the anchor table (varno 1) and
		 * probes the non-anchor side of each condition via index lookup,
		 * following the user-declared FROM clause order.  The index must
		 * exist on the non-anchor side's join column.
		 */
		foreach(lc, stmt->stxjoinconds)
		{
			OpExpr	   *opexpr = (OpExpr *) lfirst(lc);
			Var		   *lvar = (Var *) linitial(opexpr->args);
			Var		   *rvar = (Var *) lsecond(opexpr->args);
			Var		   *indexed_var;
			Relation	indexed_rel;
			Oid			idx_oid;

			/*
			 * Sampling probes the table with the higher varno (the one being
			 * joined into the growing sample) via index lookup. That side
			 * must have a suitable index.
			 */
			indexed_var = (lvar->varno > rvar->varno) ? lvar : rvar;
			Assert(indexed_var->varno > 1);
			indexed_rel = (Relation) list_nth(other_rels,
											  indexed_var->varno - 2);

			idx_oid = find_index_for_operator(indexed_rel,
											  indexed_var->varattno,
											  opexpr->opno);
			if (!OidIsValid(idx_oid))
				ereport(ERROR,
						(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
						 errmsg("no suitable index on \"%s\" column \"%s\" for join statistics",
								RelationGetRelationName(indexed_rel),
								get_attname(RelationGetRelid(indexed_rel),
											indexed_var->varattno, false)),
						 errhint("Create an index on the join column to enable index-based join sampling.")));

			join_idx_oids = lappend_oid(join_idx_oids, idx_oid);
		}

		/*
		 * Validate statistics columns.  Each column's relation is determined
		 * by its parser varno: 1 = stxrelid, 2 = stxjoinrels[0], etc.
		 */
		for (i = 0; i < nattnums; i++)
		{
			TypeCacheEntry *type;
			int			varno = key_varnos[i];
			Oid			key_relid;
			Oid			atttype;

			if (varno == 1)
				key_relid = relid;
			else
				key_relid = list_nth_oid(stmt->stxjoinrels, varno - 2);

			if (get_attgenerated(key_relid, attnums[i]) == ATTRIBUTE_GENERATED_VIRTUAL)
				ereport(ERROR,
						(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
						 errmsg("statistics creation on virtual generated columns is not supported")));

			atttype = get_atttype(key_relid, attnums[i]);
			type = lookup_type_cache(atttype, TYPECACHE_LT_OPR);
			if (type->lt_opr == InvalidOid)
				ereport(ERROR,
						(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
						 errmsg("column \"%s\" cannot be used in statistics because its type %s has no default btree operator class",
								get_attname(key_relid, attnums[i], false),
								format_type_be(atttype))));
		}
	}

	/*
	 * Now determine namespace and name. Use rel (anchor table for joins).
	 */
	if (stmt->defnames)
		namespaceId = QualifiedNameGetCreationNamespace(stmt->defnames,
														&namestr);
	else
	{
		namespaceId = RelationGetNamespace(rel);
		namestr = ChooseExtendedStatisticName(RelationGetRelationName(rel),
											  ChooseExtendedStatisticNameAddition(stmt->exprs),
											  "stat",
											  namespaceId);
	}
	namestrcpy(&stxname, namestr);

	/*
	 * Check we have creation rights in target namespace.  Skip check if
	 * caller doesn't want it.
	 */
	if (check_rights)
	{
		AclResult	aclresult;

		aclresult = object_aclcheck(NamespaceRelationId, namespaceId,
									GetUserId(), ACL_CREATE);
		if (aclresult != ACLCHECK_OK)
			aclcheck_error(aclresult, OBJECT_SCHEMA,
						   get_namespace_name(namespaceId));
	}

	/*
	 * Deal with the possibility that the statistics object already exists.
	 */
	if (SearchSysCacheExists2(STATEXTNAMENSP,
							  CStringGetDatum(namestr),
							  ObjectIdGetDatum(namespaceId)))
	{
		if (stmt->if_not_exists)
		{
			/*
			 * Since stats objects aren't members of extensions (see comments
			 * below), no need for checkMembershipInCurrentExtension here.
			 */
			ereport(NOTICE,
					(errcode(ERRCODE_DUPLICATE_OBJECT),
					 errmsg("statistics object \"%s\" already exists, skipping",
							namestr)));
			/* Close relations */
			relation_close(rel, NoLock);
			foreach(lc, other_rels)
				relation_close((Relation) lfirst(lc), NoLock);
			return InvalidObjectAddress;
		}

		ereport(ERROR,
				(errcode(ERRCODE_DUPLICATE_OBJECT),
				 errmsg("statistics object \"%s\" already exists", namestr)));
	}

	/*
	 * Check that at least two columns were specified in the statement, or
	 * that we're building statistics on a single expression (or virtual
	 * generated column).  Join statistics are exempt since single-column
	 * MCV over a join captures cross-relation frequency data.
	 */
	if (numcols < 2 && list_length(stxexprs) != 1 && other_rels == NIL)
		ereport(ERROR,
				errcode(ERRCODE_INVALID_OBJECT_DEFINITION),
				errmsg("cannot create extended statistics on a single non-virtual column"),
				errdetail("Univariate statistics are already built for each individual non-virtual table column."));

	/*
	 * Parse the statistics kinds (not allowed when building univariate
	 * statistics).
	 */
	if (numcols == 1 && stmt->stat_types != NIL && other_rels == NIL)
		ereport(ERROR,
				errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				errmsg("cannot specify statistics kinds when building univariate statistics"));

	build_ndistinct = false;
	build_dependencies = false;
	build_mcv = false;
	foreach(cell, stmt->stat_types)
	{
		char	   *type = strVal(lfirst(cell));

		if (strcmp(type, "ndistinct") == 0)
		{
			build_ndistinct = true;
			requested_type = true;
		}
		else if (strcmp(type, "dependencies") == 0)
		{
			build_dependencies = true;
			requested_type = true;
		}
		else if (strcmp(type, "mcv") == 0)
		{
			build_mcv = true;
			requested_type = true;
		}
		else
			ereport(ERROR,
					(errcode(ERRCODE_SYNTAX_ERROR),
					 errmsg("unrecognized statistics kind \"%s\"",
							type)));
	}

	/*
	 * If no statistic type was specified, build them all (but only when the
	 * statistics is defined on more than one column/expression).
	 */
	if ((!requested_type) && (numcols >= 2))
	{
		build_ndistinct = true;
		build_dependencies = true;
		build_mcv = true;
	}

	/*
	 * When there are non-trivial expressions, build the expression stats
	 * automatically. This allows calculating good estimates for stats that
	 * consider per-clause estimates (e.g. functional dependencies).
	 */
	build_expressions = (stxexprs != NIL);

	/*
	 * Check column count requirements.
	 */
	if (isjoin)
	{
		/* Join stats need at least 1 column (join adds implicit correlation) */
		if (numcols < 1)
			ereport(ERROR,
					(errcode(ERRCODE_INVALID_OBJECT_DEFINITION),
					 errmsg("extended join statistics require at least one column")));
	}
	else
	{
		/* Single-table stats need at least 2 columns or 1 expression */
		if (numcols < 2 && list_length(stxexprs) != 1)
			ereport(ERROR,
					(errcode(ERRCODE_INVALID_OBJECT_DEFINITION),
					 errmsg("extended statistics require at least 2 columns")));
	}

	/*
	 * Sort the attnums, which makes detecting duplicates somewhat easier, and
	 * it does not hurt (it does not matter for the contents, unlike for
	 * indexes, for example).
	 *
	 * For join stats, preserve user-declared column order and check for
	 * duplicate (varno, attnum) pairs.
	 */
	if (isjoin)
	{
		int			j;

		for (i = 0; i < nattnums; i++)
		{
			for (j = i + 1; j < nattnums; j++)
			{
				if (attnums[i] == attnums[j] &&
					key_varnos[i] == key_varnos[j])
					ereport(ERROR,
							(errcode(ERRCODE_DUPLICATE_COLUMN),
							 errmsg("duplicate column name in statistics definition")));
			}
		}
	}
	else
	{
		qsort(attnums, nattnums, sizeof(int16), compare_int16);

		for (i = 1; i < nattnums; i++)
		{
			if (attnums[i] == attnums[i - 1])
				ereport(ERROR,
						(errcode(ERRCODE_DUPLICATE_COLUMN),
						 errmsg("duplicate column name in statistics definition")));
		}
	}

	/*
	 * Check for duplicate expressions. We do two loops, counting the
	 * occurrences of each expression. This is O(N^2) but we only allow small
	 * number of expressions and it's not executed often.
	 *
	 * XXX We don't cross-check attributes and expressions, because it does
	 * not seem worth it. In principle we could check that expressions don't
	 * contain trivial attribute references like "(a)", but the reasoning is
	 * similar to why we don't bother with extracting columns from
	 * expressions. It's either expensive or very easy to defeat for
	 * determined user, and there's no risk if we allow such statistics (the
	 * statistics is useless, but harmless).
	 */
	foreach(cell, stxexprs)
	{
		Node	   *expr1 = (Node *) lfirst(cell);
		int			cnt = 0;

		foreach(cell2, stxexprs)
		{
			Node	   *expr2 = (Node *) lfirst(cell2);

			if (equal(expr1, expr2))
				cnt += 1;
		}

		/* every expression should find at least itself */
		Assert(cnt >= 1);

		if (cnt > 1)
			ereport(ERROR,
					(errcode(ERRCODE_DUPLICATE_COLUMN),
					 errmsg("duplicate expression in statistics definition")));
	}

	/* Form an int2vector representation of the sorted column list */
	stxkeys = buildint2vector(attnums, nattnums);

	/*
	 * For join statistics, only MCV is currently supported.
	 */
	if (isjoin && (build_ndistinct || build_dependencies || build_expressions))
		ereport(ERROR,
				(errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
				 errmsg("only MCV statistics are supported for join statistics"),
				 errhint("ndistinct, dependencies, and expression statistics require a single table.")));

	/* construct the char array of enabled statistic types */
	ntypes = 0;
	if (build_ndistinct)
		types[ntypes++] = CharGetDatum(STATS_EXT_NDISTINCT);
	if (build_dependencies)
		types[ntypes++] = CharGetDatum(STATS_EXT_DEPENDENCIES);
	if (build_mcv)
		types[ntypes++] = CharGetDatum(STATS_EXT_MCV);
	if (build_expressions)
		types[ntypes++] = CharGetDatum(STATS_EXT_EXPRESSIONS);
	Assert(ntypes > 0 && ntypes <= lengthof(types));
	stxkind = construct_array_builtin(types, ntypes, CHAROID);

	/* convert the expressions (if any) to a text datum */
	if (stxexprs != NIL)
	{
		char	   *exprsString;

		exprsString = nodeToString(stxexprs);
		exprsDatum = CStringGetTextDatum(exprsString);
		pfree(exprsString);
	}
	else
		exprsDatum = (Datum) 0;

	statrel = table_open(StatisticExtRelationId, RowExclusiveLock);

	/*
	 * Everything seems fine, so let's build the pg_statistic_ext tuple.
	 */
	memset(values, 0, sizeof(values));
	memset(nulls, false, sizeof(nulls));

	statoid = GetNewOidWithIndex(statrel, StatisticExtOidIndexId,
								 Anum_pg_statistic_ext_oid);
	values[Anum_pg_statistic_ext_oid - 1] = ObjectIdGetDatum(statoid);
	values[Anum_pg_statistic_ext_stxrelid - 1] = ObjectIdGetDatum(relid);
	values[Anum_pg_statistic_ext_stxname - 1] = NameGetDatum(&stxname);
	values[Anum_pg_statistic_ext_stxnamespace - 1] = ObjectIdGetDatum(namespaceId);
	values[Anum_pg_statistic_ext_stxowner - 1] = ObjectIdGetDatum(stxowner);
	values[Anum_pg_statistic_ext_stxkeys - 1] = PointerGetDatum(stxkeys);
	nulls[Anum_pg_statistic_ext_stxstattarget - 1] = true;
	values[Anum_pg_statistic_ext_stxkind - 1] = PointerGetDatum(stxkind);

	values[Anum_pg_statistic_ext_stxexprs - 1] = exprsDatum;
	if (exprsDatum == (Datum) 0)
		nulls[Anum_pg_statistic_ext_stxexprs - 1] = true;

	/*
	 * For join statistics, populate stxjoinrels, stxkeyrefs, and
	 * stxjoinconds. For single-table statistics, these fields are NULL.
	 */
	if (isjoin)
	{
		int2vector *stxkeyrefs;
		int16		keyrefs[STATS_MAX_DIMENSIONS];
		int			nkeys = stxkeys->dim1;
		int			njoinrels = list_length(stmt->stxjoinrels);
		Oid		   *joinrel_arr;
		int			idx;

		/* stxjoinrels: array of other relation OIDs */
		joinrel_arr = palloc(njoinrels * sizeof(Oid));
		idx = 0;
		foreach(lc, stmt->stxjoinrels)
			joinrel_arr[idx++] = lfirst_oid(lc);
		values[Anum_pg_statistic_ext_stxjoinrels - 1] =
			PointerGetDatum(buildoidvector(joinrel_arr, njoinrels));

		/* stxkeyrefs: parser varno of each column's source relation */
		for (i = 0; i < nkeys; i++)
			keyrefs[i] = key_varnos[i];
		stxkeyrefs = buildint2vector(keyrefs, nkeys);
		values[Anum_pg_statistic_ext_stxkeyrefs - 1] =
			PointerGetDatum(stxkeyrefs);

		/* stxjoinconds: serialize the join conditions */
		values[Anum_pg_statistic_ext_stxjoinconds - 1] =
			CStringGetTextDatum(nodeToString(stmt->stxjoinconds));
	}
	else
	{
		/* Join fields are NULL for single-table statistics */
		nulls[Anum_pg_statistic_ext_stxjoinrels - 1] = true;
		nulls[Anum_pg_statistic_ext_stxkeyrefs - 1] = true;
		nulls[Anum_pg_statistic_ext_stxjoinconds - 1] = true;
	}

	/* insert it into pg_statistic_ext */
	htup = heap_form_tuple(statrel->rd_att, values, nulls);
	CatalogTupleInsert(statrel, htup);
	heap_freetuple(htup);

	relation_close(statrel, RowExclusiveLock);

	/*
	 * We used to create the pg_statistic_ext_data tuple too, but it's not
	 * clear what value should the stxdinherit flag have (it depends on
	 * whether the rel is partitioned, contains data, etc.)
	 */

	InvokeObjectPostCreateHook(StatisticExtRelationId, statoid, 0);

	/*
	 * Invalidate relcache so that others see the new statistics object. Only
	 * the anchor relation needs invalidation -- it's the one whose statlist
	 * is used to find this stats object during planning.
	 */
	CacheInvalidateRelcache(rel);

	/* Close relations */
	relation_close(rel, NoLock);
	foreach(lc, other_rels)
		relation_close((Relation) lfirst(lc), NoLock);

	/*
	 * Add an AUTO dependency on each column used in the stats, so that the
	 * stats object goes away if any or all of them get dropped.
	 */
	ObjectAddressSet(myself, StatisticExtRelationId, statoid);

	/* add dependencies for plain column references */
	for (i = 0; i < nattnums; i++)
	{
		Oid			key_relid;

		if (isjoin)
		{
			int			varno = key_varnos[i];

			if (varno == 1)
				key_relid = relid;
			else
				key_relid = list_nth_oid(stmt->stxjoinrels, varno - 2);
		}
		else
			key_relid = relid;

		ObjectAddressSubSet(parentobject, RelationRelationId, key_relid, attnums[i]);
		recordDependencyOn(&myself, &parentobject, DEPENDENCY_AUTO);
	}

	/* For join stats, add dependencies on join columns */
	if (isjoin)
	{
		ListCell   *lc;
		Oid			all_rels[STATS_MAX_DIMENSIONS + 1];
		int			nrels;

		/* Build relation OID array: [stxrelid, joinrels...] */
		all_rels[0] = relid;
		nrels = 1;
		foreach(lc, stmt->stxjoinrels)
			all_rels[nrels++] = lfirst_oid(lc);

		/* Record dependencies on columns referenced by join conditions */
		foreach(lc, stmt->stxjoinconds)
		{
			OpExpr	   *op = (OpExpr *) lfirst(lc);
			ListCell   *lc2;

			foreach(lc2, op->args)
			{
				Node	   *arg = (Node *) lfirst(lc2);

				if (IsA(arg, Var))
				{
					Var		   *var = (Var *) arg;

					/* varno is 1-based; all_rels is 0-based */
					Assert(var->varno >= 1 && var->varno <= nrels);
					ObjectAddressSubSet(parentobject, RelationRelationId,
										all_rels[var->varno - 1],
										var->varattno);
					recordDependencyOn(&myself, &parentobject,
									   DEPENDENCY_AUTO);
				}
			}
		}

		/* Record dependencies on indexes required for join sampling */
		foreach(lc, join_idx_oids)
		{
			ObjectAddressSet(parentobject, RelationRelationId,
							 lfirst_oid(lc));
			recordDependencyOn(&myself, &parentobject, DEPENDENCY_NORMAL);
		}
	}

	/*
	 * If there are no dependencies on a column, give the statistics object an
	 * auto dependency on the whole table.  In most cases, this will be
	 * redundant, but it might not be if the statistics expressions contain no
	 * Vars (which might seem strange but possible). This is consistent with
	 * what we do for indexes in index_create.
	 *
	 * XXX We intentionally don't consider the expressions before adding this
	 * dependency, because recordDependencyOnSingleRelExpr may not create any
	 * dependencies for whole-row Vars.
	 *
	 * Join stats are excluded because they span two tables (no single "whole
	 * table" exists).
	 */
	if (!isjoin && !nattnums)
	{
		ObjectAddressSet(parentobject, RelationRelationId, relid);
		recordDependencyOn(&myself, &parentobject, DEPENDENCY_AUTO);
	}

	/*
	 * Store dependencies on anything mentioned in statistics expressions,
	 * just like we do for index expressions.
	 */
	if (stxexprs)
		recordDependencyOnSingleRelExpr(&myself,
										(Node *) stxexprs,
										relid,
										DEPENDENCY_NORMAL,
										DEPENDENCY_AUTO, false);

	/*
	 * Also add dependencies on namespace and owner.  These are required
	 * because the stats object might have a different namespace and/or owner
	 * than the underlying table(s).
	 */
	ObjectAddressSet(parentobject, NamespaceRelationId, namespaceId);
	recordDependencyOn(&myself, &parentobject, DEPENDENCY_NORMAL);

	recordDependencyOnOwner(StatisticExtRelationId, statoid, stxowner);

	/*
	 * XXX probably there should be a recordDependencyOnCurrentExtension call
	 * here too, but we'd have to add support for ALTER EXTENSION ADD/DROP
	 * STATISTICS, which is more work than it seems worth.
	 */

	/* Add any requested comment */
	if (stmt->stxcomment != NULL)
		CreateComments(statoid, StatisticExtRelationId, 0,
					   stmt->stxcomment);

	/* Return stats object's address */
	return myself;
}

/*
 *		ALTER STATISTICS
 */
ObjectAddress
AlterStatistics(AlterStatsStmt *stmt)
{
	Relation	rel;
	Oid			stxoid;
	HeapTuple	oldtup;
	HeapTuple	newtup;
	Datum		repl_val[Natts_pg_statistic_ext];
	bool		repl_null[Natts_pg_statistic_ext];
	bool		repl_repl[Natts_pg_statistic_ext];
	ObjectAddress address;
	int			newtarget = 0;
	bool		newtarget_default;

	/* -1 was used in previous versions for the default setting */
	if (stmt->stxstattarget && intVal(stmt->stxstattarget) != -1)
	{
		newtarget = intVal(stmt->stxstattarget);
		newtarget_default = false;
	}
	else
		newtarget_default = true;

	if (!newtarget_default)
	{
		/* Limit statistics target to a sane range */
		if (newtarget < 0)
		{
			ereport(ERROR,
					(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
					 errmsg("statistics target %d is too low",
							newtarget)));
		}
		else if (newtarget > MAX_STATISTICS_TARGET)
		{
			newtarget = MAX_STATISTICS_TARGET;
			ereport(WARNING,
					(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
					 errmsg("lowering statistics target to %d",
							newtarget)));
		}
	}

	/* lookup OID of the statistics object */
	stxoid = get_statistics_object_oid(stmt->defnames, stmt->missing_ok);

	/*
	 * If we got here and the OID is not valid, it means the statistics object
	 * does not exist, but the command specified IF EXISTS. So report this as
	 * a simple NOTICE and we're done.
	 */
	if (!OidIsValid(stxoid))
	{
		char	   *schemaname;
		char	   *statname;

		Assert(stmt->missing_ok);

		DeconstructQualifiedName(stmt->defnames, &schemaname, &statname);

		if (schemaname)
			ereport(NOTICE,
					(errmsg("statistics object \"%s.%s\" does not exist, skipping",
							schemaname, statname)));
		else
			ereport(NOTICE,
					(errmsg("statistics object \"%s\" does not exist, skipping",
							statname)));

		return InvalidObjectAddress;
	}

	/* Search pg_statistic_ext */
	rel = table_open(StatisticExtRelationId, RowExclusiveLock);

	oldtup = SearchSysCache1(STATEXTOID, ObjectIdGetDatum(stxoid));
	if (!HeapTupleIsValid(oldtup))
		elog(ERROR, "cache lookup failed for extended statistics object %u", stxoid);

	/* Must be owner of the existing statistics object */
	if (!object_ownercheck(StatisticExtRelationId, stxoid, GetUserId()))
		aclcheck_error(ACLCHECK_NOT_OWNER, OBJECT_STATISTIC_EXT,
					   NameListToString(stmt->defnames));

	/* Build new tuple. */
	memset(repl_val, 0, sizeof(repl_val));
	memset(repl_null, false, sizeof(repl_null));
	memset(repl_repl, false, sizeof(repl_repl));

	/* replace the stxstattarget column */
	repl_repl[Anum_pg_statistic_ext_stxstattarget - 1] = true;
	if (!newtarget_default)
		repl_val[Anum_pg_statistic_ext_stxstattarget - 1] = Int16GetDatum(newtarget);
	else
		repl_null[Anum_pg_statistic_ext_stxstattarget - 1] = true;

	newtup = heap_modify_tuple(oldtup, RelationGetDescr(rel),
							   repl_val, repl_null, repl_repl);

	/* Update system catalog. */
	CatalogTupleUpdate(rel, &newtup->t_self, newtup);

	InvokeObjectPostAlterHook(StatisticExtRelationId, stxoid, 0);

	ObjectAddressSet(address, StatisticExtRelationId, stxoid);

	/*
	 * NOTE: because we only support altering the statistics target, not the
	 * other fields, there is no need to update dependencies.
	 */

	heap_freetuple(newtup);
	ReleaseSysCache(oldtup);

	table_close(rel, RowExclusiveLock);

	return address;
}

/*
 * Delete entry in pg_statistic_ext_data catalog. We don't know if the row
 * exists, so don't error out.
 */
void
RemoveStatisticsDataById(Oid statsOid, bool inh)
{
	Relation	relation;
	HeapTuple	tup;

	relation = table_open(StatisticExtDataRelationId, RowExclusiveLock);

	tup = SearchSysCache2(STATEXTDATASTXOID, ObjectIdGetDatum(statsOid),
						  BoolGetDatum(inh));

	/* We don't know if the data row for inh value exists. */
	if (HeapTupleIsValid(tup))
	{
		CatalogTupleDelete(relation, &tup->t_self);

		ReleaseSysCache(tup);
	}

	table_close(relation, RowExclusiveLock);
}

/*
 * Guts of statistics object deletion.
 */
void
RemoveStatisticsById(Oid statsOid)
{
	Relation	relation;
	Relation	rel;
	HeapTuple	tup;
	Form_pg_statistic_ext statext;
	Oid			relid;

	/*
	 * Delete the pg_statistic_ext tuple.  Also send out a cache inval on the
	 * associated table, so that dependent plans will be rebuilt.
	 */
	relation = table_open(StatisticExtRelationId, RowExclusiveLock);

	tup = SearchSysCache1(STATEXTOID, ObjectIdGetDatum(statsOid));

	if (!HeapTupleIsValid(tup)) /* should not happen */
		elog(ERROR, "cache lookup failed for statistics object %u", statsOid);

	statext = (Form_pg_statistic_ext) GETSTRUCT(tup);
	relid = statext->stxrelid;

	/*
	 * Delete the pg_statistic_ext_data tuples holding the actual statistical
	 * data. There might be data with/without inheritance, so attempt deleting
	 * both. We lock the user table first, to prevent other processes (e.g.
	 * DROP STATISTICS) from removing the row concurrently.
	 */
	rel = table_open(relid, ShareUpdateExclusiveLock);

	RemoveStatisticsDataById(statsOid, true);
	RemoveStatisticsDataById(statsOid, false);

	CacheInvalidateRelcacheByRelid(relid);

	CatalogTupleDelete(relation, &tup->t_self);

	ReleaseSysCache(tup);

	/* Keep lock until the end of the transaction. */
	table_close(rel, NoLock);

	table_close(relation, RowExclusiveLock);
}

/*
 * Select a nonconflicting name for a new statistics object.
 *
 * name1, name2, and label are used the same way as for makeObjectName(),
 * except that the label can't be NULL; digits will be appended to the label
 * if needed to create a name that is unique within the specified namespace.
 *
 * Returns a palloc'd string.
 *
 * Note: it is theoretically possible to get a collision anyway, if someone
 * else chooses the same name concurrently.  This is fairly unlikely to be
 * a problem in practice, especially if one is holding a share update
 * exclusive lock on the relation identified by name1.  However, if choosing
 * multiple names within a single command, you'd better create the new object
 * and do CommandCounterIncrement before choosing the next one!
 */
static char *
ChooseExtendedStatisticName(const char *name1, const char *name2,
							const char *label, Oid namespaceid)
{
	int			pass = 0;
	char	   *stxname = NULL;
	char		modlabel[NAMEDATALEN];

	/* try the unmodified label first */
	strlcpy(modlabel, label, sizeof(modlabel));

	for (;;)
	{
		Oid			existingstats;

		stxname = makeObjectName(name1, name2, modlabel);

		existingstats = GetSysCacheOid2(STATEXTNAMENSP, Anum_pg_statistic_ext_oid,
										PointerGetDatum(stxname),
										ObjectIdGetDatum(namespaceid));
		if (!OidIsValid(existingstats))
			break;

		/* found a conflict, so try a new name component */
		pfree(stxname);
		snprintf(modlabel, sizeof(modlabel), "%s%d", label, ++pass);
	}

	return stxname;
}

/*
 * Generate "name2" for a new statistics object given the list of column
 * names for it.  This will be passed to ChooseExtendedStatisticName along
 * with the parent table name and a suitable label.
 *
 * We know that less than NAMEDATALEN characters will actually be used,
 * so we can truncate the result once we've generated that many.
 *
 * XXX see also ChooseForeignKeyConstraintNameAddition and
 * ChooseIndexNameAddition.
 */
static char *
ChooseExtendedStatisticNameAddition(List *exprs)
{
	char		buf[NAMEDATALEN * 2];
	int			buflen = 0;
	ListCell   *lc;

	buf[0] = '\0';
	foreach(lc, exprs)
	{
		StatsElem  *selem = (StatsElem *) lfirst(lc);
		const char *name;

		/* It should be one of these, but just skip if it happens not to be */
		if (!IsA(selem, StatsElem))
			continue;

		name = selem->name;

		if (buflen > 0)
			buf[buflen++] = '_';	/* insert _ between names */

		/*
		 * We use fixed 'expr' for expressions, which have empty column names.
		 * For indexes this is handled in ChooseIndexColumnNames, but we have
		 * no such function for stats and it does not seem worth adding. If a
		 * better name is needed, the user can specify it explicitly.
		 */
		if (!name)
			name = "expr";

		/*
		 * At this point we have buflen <= NAMEDATALEN.  name should be less
		 * than NAMEDATALEN already, but use strlcpy for paranoia.
		 */
		strlcpy(buf + buflen, name, NAMEDATALEN);
		buflen += strlen(buf + buflen);
		if (buflen >= NAMEDATALEN)
			break;
	}
	return pstrdup(buf);
}

/*
 * StatisticsGetRelation: given a statistics object's OID, get the OID of
 * the relation it is defined on.  Uses the system cache.
 */
Oid
StatisticsGetRelation(Oid statId, bool missing_ok)
{
	HeapTuple	tuple;
	Form_pg_statistic_ext stx;
	Oid			result;

	tuple = SearchSysCache1(STATEXTOID, ObjectIdGetDatum(statId));
	if (!HeapTupleIsValid(tuple))
	{
		if (missing_ok)
			return InvalidOid;
		elog(ERROR, "cache lookup failed for statistics object %u", statId);
	}
	stx = (Form_pg_statistic_ext) GETSTRUCT(tuple);
	Assert(stx->oid == statId);

	result = stx->stxrelid;
	ReleaseSysCache(tuple);
	return result;
}
