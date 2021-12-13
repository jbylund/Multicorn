/*
 * The Multicorn Foreign Data Wrapper allows you to fetch foreign data in
 * Python in your PostgreSQL server
 *
 * This software is released under the postgresql licence
 *
 * author: Kozea
 */
#include "multicorn.h"
#include "optimizer/paths.h"
#include "optimizer/pathnode.h"
#include "optimizer/planmain.h"
#include "optimizer/restrictinfo.h"
#include "optimizer/clauses.h"
#include "optimizer/optimizer.h"
#include "optimizer/tlist.h"
#if PG_VERSION_NUM < 120000
#include "optimizer/var.h"
#include "dynloader.h"
#endif
#include "access/reloptions.h"
#include "access/relscan.h"
#include "access/relation.h"
#include "access/tableam.h"
#include "access/sysattr.h"
#include "access/xact.h"
#include "rewrite/rewriteManip.h"
#include "nodes/makefuncs.h"
#include "catalog/pg_type.h"
#include "catalog/namespace.h"
#include "utils/memutils.h"
#include "utils/varlena.h"
#include "utils/snapmgr.h"
#include "miscadmin.h"
#include "utils/lsyscache.h"
#include "utils/rel.h"
#include "parser/parsetree.h"
#include "fmgr.h"
#include "executor/spi.h"
#include "nodes/print.h"
#include "tcop/pquery.h"

#include "cstore_fdw.h"


PG_MODULE_MAGIC;


extern Datum multicorn_handler(PG_FUNCTION_ARGS);
extern Datum multicorn_validator(PG_FUNCTION_ARGS);


PG_FUNCTION_INFO_V1(multicorn_handler);
PG_FUNCTION_INFO_V1(multicorn_validator);


void		_PG_init(void);
void		_PG_fini(void);

/*
 * FDW functions declarations
 */

static void multicornGetForeignRelSize(PlannerInfo *root,
						   RelOptInfo *baserel,
						   Oid foreigntableid);
static void multicornGetForeignPaths(PlannerInfo *root,
						 RelOptInfo *baserel,
						 Oid foreigntableid);
static ForeignScan *multicornGetForeignPlan(PlannerInfo *root,
						RelOptInfo *baserel,
						Oid foreigntableid,
						ForeignPath *best_path,
						List *tlist,
						List *scan_clauses
#if PG_VERSION_NUM >= 90500
						, Plan *outer_plan
#endif
		);
static void multicornExplainForeignScan(ForeignScanState *node, ExplainState *es);
static void multicornBeginForeignScan(ForeignScanState *node, int eflags);
static TupleTableSlot *multicornIterateForeignScan(ForeignScanState *node);
static void multicornReScanForeignScan(ForeignScanState *node);
static void multicornEndForeignScan(ForeignScanState *node);

#if PG_VERSION_NUM >= 90300
static void multicornAddForeignUpdateTargets(Query *parsetree,
								 RangeTblEntry *target_rte,
								 Relation target_relation);

static List *multicornPlanForeignModify(PlannerInfo *root,
						   ModifyTable *plan,
						   Index resultRelation,
						   int subplan_index);
static void multicornBeginForeignModify(ModifyTableState *mtstate,
							ResultRelInfo *resultRelInfo,
							List *fdw_private,
							int subplan_index,
							int eflags);
static TupleTableSlot *multicornExecForeignInsert(EState *estate, ResultRelInfo *resultRelInfo,
						   TupleTableSlot *slot,
						   TupleTableSlot *planslot);
static TupleTableSlot *multicornExecForeignDelete(EState *estate, ResultRelInfo *resultRelInfo,
						   TupleTableSlot *slot, TupleTableSlot *planSlot);
static TupleTableSlot *multicornExecForeignUpdate(EState *estate, ResultRelInfo *resultRelInfo,
						   TupleTableSlot *slot, TupleTableSlot *planSlot);
static void multicornEndForeignModify(EState *estate, ResultRelInfo *resultRelInfo);

static void multicorn_subxact_callback(SubXactEvent event, SubTransactionId mySubid,
						   SubTransactionId parentSubid, void *arg);
#endif

static void multicornGetForeignUpperPaths(PlannerInfo *root, UpperRelationKind stage,
						      RelOptInfo *input_rel, RelOptInfo *output_rel, void *extra
        );

#if PG_VERSION_NUM >= 90500
static List *multicornImportForeignSchema(ImportForeignSchemaStmt * stmt,
							 Oid serverOid);
static bool multicornIsForeignScanParallelSafe(PlannerInfo *root, RelOptInfo *rel,
											RangeTblEntry *rte);
#endif

static void multicorn_xact_callback(XactEvent event, void *arg);

/* Functions relating to aggregation/grouping pushdown */
static bool multicorn_foreign_grouping_ok(PlannerInfo *root, RelOptInfo *grouped_rel,
                                          Node *havingQual);
static void multicorn_add_foreign_grouping_paths(PlannerInfo *root,
											  RelOptInfo *input_rel,
											  RelOptInfo *grouped_rel,
											  GroupPathExtraData *extra
);

/* Functions relating to scanning through subrelations */
static bool subscanReadRow(TupleTableSlot *slot, Relation subscanRel, void *subscanState);
static void subscanEnd(ForeignScanState *node);

/*	Helpers functions */
static AttrNumber *buildConvertMapIfNeeded(TupleDesc indesc, TupleDesc outDesc);
static List *buildCStoreColumnList(TupleDesc desc, List* target_list, Index relid);
static List *buildCStoreQualList(AttrNumber *attrMap, int map_length, List *quals, Index relid);
void	   *serializePlanState(MulticornPlanState * planstate);
MulticornExecState *initializeExecState(void *internal_plan_state);

/* Hash table mapping oid to fdw instances */
HTAB	   *InstancesHash;

DestReceiver *CreateMulticornDestReceiver(MulticornExecState *execstate);

#ifdef DEBUG
#define DEBUG_TEST 1
#else
#define DEBUG_TEST 0
#endif
#define debug_elog(fmt, ...) \
	do { if (DEBUG_TEST) elog(WARNING, fmt, ##__VA_ARGS__); } while (0)


void
_PG_init()
{
	HASHCTL		ctl;
	MemoryContext oldctx = MemoryContextSwitchTo(CacheMemoryContext);
	bool need_import_plpy = false;

#if PY_MAJOR_VERSION >= 3
	/* Try to load plpython3 with its own module */
	PG_TRY();
	{
	void * PyInit_plpy = load_external_function("plpython3", "PyInit_plpy", true, NULL);
	PyImport_AppendInittab("plpy", PyInit_plpy);
	need_import_plpy = true;
	}
	PG_CATCH();
	{
		need_import_plpy = false;
	}
	PG_END_TRY();
#endif
	Py_Initialize();
	if (need_import_plpy)
		PyImport_ImportModule("plpy");
	RegisterXactCallback(multicorn_xact_callback, NULL);
#if PG_VERSION_NUM >= 90300
	RegisterSubXactCallback(multicorn_subxact_callback, NULL);
#endif
	/* Initialize the global oid -> python instances hash */
	MemSet(&ctl, 0, sizeof(ctl));
	ctl.keysize = sizeof(Oid);
	ctl.entrysize = sizeof(CacheEntry);
	ctl.hash = oid_hash;
	ctl.hcxt = CacheMemoryContext;
	InstancesHash = hash_create("multicorn instances", 32,
								&ctl,
								HASH_ELEM | HASH_FUNCTION);
	MemoryContextSwitchTo(oldctx);
}

void
_PG_fini()
{
	Py_Finalize();
}


Datum
multicorn_handler(PG_FUNCTION_ARGS)
{
	FdwRoutine *fdw_routine = makeNode(FdwRoutine);

	/* Plan phase */
	fdw_routine->GetForeignRelSize = multicornGetForeignRelSize;
	fdw_routine->GetForeignPaths = multicornGetForeignPaths;
	fdw_routine->GetForeignPlan = multicornGetForeignPlan;
	fdw_routine->ExplainForeignScan = multicornExplainForeignScan;

	/* Scan phase */
	fdw_routine->BeginForeignScan = multicornBeginForeignScan;
	fdw_routine->IterateForeignScan = multicornIterateForeignScan;
	fdw_routine->ReScanForeignScan = multicornReScanForeignScan;
	fdw_routine->EndForeignScan = multicornEndForeignScan;

#if PG_VERSION_NUM >= 90300
	/* Code for 9.3 */
	fdw_routine->AddForeignUpdateTargets = multicornAddForeignUpdateTargets;
	/* Writable API */
	fdw_routine->PlanForeignModify = multicornPlanForeignModify;
	fdw_routine->BeginForeignModify = multicornBeginForeignModify;
	fdw_routine->ExecForeignInsert = multicornExecForeignInsert;
	fdw_routine->ExecForeignDelete = multicornExecForeignDelete;
	fdw_routine->ExecForeignUpdate = multicornExecForeignUpdate;
	fdw_routine->EndForeignModify = multicornEndForeignModify;
#endif

#if PG_VERSION_NUM >= 90500
	fdw_routine->ImportForeignSchema = multicornImportForeignSchema;
	fdw_routine->IsForeignScanParallelSafe = multicornIsForeignScanParallelSafe;
#endif

    /* Support functions for upper relation push-down */
	fdw_routine->GetForeignUpperPaths = multicornGetForeignUpperPaths;

	PG_RETURN_POINTER(fdw_routine);
}

Datum
multicorn_validator(PG_FUNCTION_ARGS)
{
	List	   *options_list = untransformRelOptions(PG_GETARG_DATUM(0));
	Oid			catalog = PG_GETARG_OID(1);
	char	   *className = NULL;
	ListCell   *cell;
	PyObject   *p_class;

	foreach(cell, options_list)
	{
		DefElem    *def = (DefElem *) lfirst(cell);

		if (strcmp(def->defname, "wrapper") == 0)
		{
			/* Only at server creation can we set the wrapper,	*/
			/* for security issues. */
			if (catalog == ForeignTableRelationId)
			{
				ereport(ERROR, (errmsg("%s", "Cannot set the wrapper class on the table"),
								errhint("%s", "Set it on the server")));
			}
			else
			{
				className = (char *) defGetString(def);
			}
		}
	}
	if (catalog == ForeignServerRelationId)
	{
		if (className == NULL)
		{
			ereport(ERROR, (errmsg("%s", "The wrapper parameter is mandatory, specify a valid class name")));
		}
		/* Try to import the class. */
		p_class = getClassString(className);
		errorCheck();
		Py_DECREF(p_class);
	}
	PG_RETURN_VOID();
}


/*
 * multicornGetForeignRelSize
 *		Obtain relation size estimates for a foreign table.
 *		This is done by calling the
 */
static void
multicornGetForeignRelSize(PlannerInfo *root,
						   RelOptInfo *baserel,
						   Oid foreigntableid)
{
	MulticornPlanState *planstate = palloc0(sizeof(MulticornPlanState));
	ForeignTable *ftable = GetForeignTable(foreigntableid);
	ListCell   *lc;
	bool		needWholeRow = false;
	TupleDesc	desc;

	baserel->fdw_private = planstate;

    /* Base foreign tables need to be push down always. */
	planstate->pushdown_safe = true;
    planstate->groupby_supported = false;
    planstate->agg_functions = NULL;

	planstate->fdw_instance = getInstance(foreigntableid);
	planstate->foreigntableid = foreigntableid;
	/* Initialize the conversion info array */
	{
		Relation	rel = RelationIdGetRelation(ftable->relid);
		AttInMetadata *attinmeta;

		desc = RelationGetDescr(rel);
		attinmeta = TupleDescGetAttInMetadata(desc);
		planstate->numattrs = RelationGetNumberOfAttributes(rel);

		planstate->cinfos = palloc0(sizeof(ConversionInfo *) *
									planstate->numattrs);
		initConversioninfo(planstate->cinfos, attinmeta, NULL);
		/*
		 * needWholeRow = rel->trigdesc && rel->trigdesc->trig_insert_after_row;
		 *
		 * Multicorn seems to use this for some reason -- fetch the whole row if there's a
		 * trigger on the table. Looks like this is for writing only (return the written
		 * row after write for the trigger?) but no other FDW does this. Also, this forces
		 * Multicorn to ask for all columns in all cases, which means that we force
		 * CStore to read more data (since CStore data is arranged column-first,
		 * this is a big slowdown). Disabling this doesn't seem to break things yet
		 * and brings us within 10-20ms of scanning through an equivalent big CStore table.
		 *
		 * If this does start to break, uncomment this.
		 */
		needWholeRow = false;
		RelationClose(rel);
	}
	if (needWholeRow)
	{
		int			i;

		for (i = 0; i < desc->natts; i++)
		{
			Form_pg_attribute att = TupleDescAttr(desc, i);

			if (!att->attisdropped)
			{
				planstate->target_list = lappend(planstate->target_list, makeString(NameStr(att->attname)));
			}
		}
	}
	else
	{
		/*
         * Pull "var" clauses to build an appropriate target list
         *
         * baserel->reltarget->exprs can be used to determine which columns need
         * to be fetched; but note that it only lists columns that have to be
         * emitted by the ForeignScan plan node, not columns that are used in
         * qual evaluation but not output by the query.
         *
         * baserel->baserestrictinfo is particularly interesting, as it contains
         * restriction quals (WHERE clauses) that should be used to filter the
         * rows to be fetched. (The FDW itself is not required to enforce these
         * quals, as the core executor can check them instead.)
         *
         * For more details see: https://www.postgresql.org/docs/12/fdw-planning.html
         */
#if PG_VERSION_NUM >= 90600
		foreach(lc, extractColumns(baserel->reltarget->exprs, baserel->baserestrictinfo))
#else
		foreach(lc, extractColumns(baserel->reltargetlist, baserel->baserestrictinfo))
#endif
		{
			Var		   *var = (Var *) lfirst(lc);
			Value	   *colname;

			/*
			 * Store only a Value node containing the string name of the
			 * column.
			 */
			colname = colnameFromVar(var, root);
			if (colname != NULL && strVal(colname) != NULL)
			{
				planstate->target_list = lappend(planstate->target_list, colname);
			}
		}
	}

	/* Extract the restrictions from the plan. */
	foreach(lc, baserel->baserestrictinfo)
	{
		extractRestrictions(baserel->relids, ((RestrictInfo *) lfirst(lc))->clause,
							&planstate->qual_list);

	}

    /*
	 * Identify which baserestrictinfo clauses can be sent to the remote
	 * server and which can't.
     * TODO: for now all WHERE clauses will be classified as local conditions
     * since multicorn_foreign_expr_walker lacks T_OpExpr and T_Const cases,
     * thus preventing pushdown. When adding support for this make sure to align
     * the code in multicorn_extract_upper_rel_info as well.
	 */
	multicorn_classify_conditions(root, baserel, baserel->baserestrictinfo,
					              &planstate->remote_conds, &planstate->local_conds);

	/* Inject the "rows" and "width" attribute into the baserel */
#if PG_VERSION_NUM >= 90600
	getRelSize(planstate, root, &baserel->rows, &baserel->reltarget->width);
	planstate->width = baserel->reltarget->width;
#else
	getRelSize(planstate, root, &baserel->rows, &baserel->width);
#endif
}

/*
 * multicornGetForeignPaths
 *		Create possible access paths for a scan on the foreign table.
 *		This is done by calling the "get_path_keys method on the python side,
 *		and parsing its result to build parameterized paths according to the
 *		equivalence classes found in the plan.
 */
static void
multicornGetForeignPaths(PlannerInfo *root,
						 RelOptInfo *baserel,
						 Oid foreigntableid)
{
	List				*pathes; /* List of ForeignPath */
	MulticornPlanState	*planstate = baserel->fdw_private;
	ListCell		    *lc;

	/* These lists are used to handle sort pushdown */
	List				*apply_pathkeys = NULL;
	List				*deparsed_pathkeys = NULL;

	/* Extract a friendly version of the pathkeys. */
	List	   *possiblePaths = pathKeys(planstate);

	/* Try to find parameterized paths */
	pathes = findPaths(root, baserel, possiblePaths, planstate->startupCost,
			planstate, apply_pathkeys, deparsed_pathkeys);

	/* Add a simple default path */
	pathes = lappend(pathes, create_foreignscan_path(root, baserel,
#if PG_VERSION_NUM >= 90600
													  NULL,  /* default pathtarget */
#endif
			baserel->rows,
			planstate->startupCost,
#if PG_VERSION_NUM >= 90600
			baserel->rows * baserel->reltarget->width,
#else
			baserel->rows * baserel->width,
#endif
			NIL,		/* no pathkeys */
			NULL,
#if PG_VERSION_NUM >= 90500
			NULL,
#endif
			NULL));

	/* Handle sort pushdown */
	if (root->query_pathkeys)
	{
		List		*deparsed = deparse_sortgroup(root, foreigntableid, baserel);

		if (deparsed)
		{
			/* Update the sort_*_pathkeys lists if needed */
			computeDeparsedSortGroup(deparsed, planstate, &apply_pathkeys,
					&deparsed_pathkeys);
		}
	}

	/* Add each ForeignPath previously found */
	foreach(lc, pathes)
	{
		ForeignPath *path = (ForeignPath *) lfirst(lc);

		/* Add the path without modification */
		add_path(baserel, (Path *) path);

		/* Add the path with sort pusdown if possible */
		if (apply_pathkeys && deparsed_pathkeys)
		{
			ForeignPath *newpath;

			newpath = create_foreignscan_path(root, baserel,
#if PG_VERSION_NUM >= 90600
													  NULL,  /* default pathtarget */
#endif
					path->path.rows,
					path->path.startup_cost, path->path.total_cost,
					apply_pathkeys, NULL,
#if PG_VERSION_NUM >= 90500
					NULL,
#endif
					(void *) deparsed_pathkeys);

			newpath->path.param_info = path->path.param_info;
			add_path(baserel, (Path *) newpath);
		}
	}
	errorCheck();
}

/*
 * multicornGetForeignPlan
 *		Create a ForeignScan plan node for scanning the foreign table
 */
static ForeignScan *
multicornGetForeignPlan(PlannerInfo *root,
						RelOptInfo *foreignrel,
						Oid foreigntableid,
						ForeignPath *best_path,
						List *tlist,
						List *scan_clauses
#if PG_VERSION_NUM >= 90500
						, Plan *outer_plan
#endif
		)
{
    MulticornPlanState *planstate = (MulticornPlanState *) foreignrel->fdw_private;
    Index		scan_relid;
	List	   *fdw_scan_tlist = NIL;
    ListCell   *lc;

#if PG_VERSION_NUM >= 90600
	best_path->path.pathtarget->width = planstate->width;
#endif

    if (IS_SIMPLE_REL(foreignrel))
	{
		/*
		 * For base relations, set scan_relid as the relid of the relation.
		 */
		scan_relid = foreignrel->relid;
	}
	else
	{
		/*
		 * Join relation or upper relation - set scan_relid to 0.
		 */
		scan_relid = 0;

		/*
		 * For a join rel, baserestrictinfo is NIL and we are not considering
		 * parameterization right now, so there should be no scan_clauses for
		 * a joinrel or an upper rel either.
		 */
		Assert(!scan_clauses);

		/* Build the list of columns to be fetched from the foreign server. */
		fdw_scan_tlist = multicorn_build_tlist_to_deparse(foreignrel);
	}

    best_path->path.pathtarget->width = planstate->width;
    planstate->pathkeys = (List *) best_path->fdw_private;

    scan_clauses = extract_actual_clauses(scan_clauses, false);
	/* Extract the quals coming from a parameterized path, if any */
	if (best_path->path.param_info)
	{

		foreach(lc, scan_clauses)
		{
			extractRestrictions(foreignrel->relids, (Expr *) lfirst(lc),
								&planstate->qual_list);
		}
	}

    /* Extract data needed for aggregations on the Python side */
    if (IS_UPPER_REL(foreignrel))
    {
        multicorn_extract_upper_rel_info(root, fdw_scan_tlist, planstate);
    }

	return make_foreignscan(tlist,
							scan_clauses,
							scan_relid,
							scan_clauses,
							serializePlanState(planstate)
#if PG_VERSION_NUM >= 90500
							, fdw_scan_tlist
							, NIL
							, outer_plan
#endif
							);
}

/*
 * multicornExplainForeignScan
 *		Placeholder for additional "EXPLAIN" information.
 *		This should (at least) output the python class name, as well
 *		as information that was taken into account for the choice of a path.
 */
static void
multicornExplainForeignScan(ForeignScanState *node, ExplainState *es)
{
	PyObject *p_iterable = execute(node, es),
			 *p_item,
			 *p_str;
	Py_INCREF(p_iterable);
	while((p_item = PyIter_Next(p_iterable))){
		p_str = PyObject_Str(p_item);
		ExplainPropertyText("Multicorn", PyString_AsString(p_str), es);
		Py_DECREF(p_str);
	}
	Py_DECREF(p_iterable);
	errorCheck();
}

/*
 *	multicornBeginForeignScan
 *		Initialize the foreign scan.
 *		This (primarily) involves :
 *			- retrieving cached info from the plan phase
 *			- initializing various buffers
 */
static void
multicornBeginForeignScan(ForeignScanState *node, int eflags)
{
	ForeignScan *fscan = (ForeignScan *) node->ss.ps.plan;
	MulticornExecState *execstate;
	ListCell   *lc;

    execstate = initializeExecState(fscan->fdw_private);

    /*
	 * Get info we'll need for converting data fetched from the foreign server
	 * into local representation and error reporting during that process.
	 */
	if (fscan->scan.scanrelid > 0)
	{
		execstate->rel = node->ss.ss_currentRelation;
		execstate->tupdesc = RelationGetDescr(execstate->rel);
        initConversioninfo(execstate->cinfos, TupleDescGetAttInMetadata(execstate->tupdesc), NULL);
	}
	else
	{
		execstate->rel = NULL;
#if (PG_VERSION_NUM >= 140000)
		execstate->tupdesc = multicorn_get_tupdesc_for_join_scan_tuples(node);
#else
		execstate->tupdesc = node->ss.ss_ScanTupleSlot->tts_tupleDescriptor;
#endif
        initConversioninfo(execstate->cinfos, TupleDescGetAttInMetadata(execstate->tupdesc), execstate->upper_rel_targets);
	}

	execstate->values = palloc(sizeof(Datum) * execstate->tupdesc->natts);
	execstate->nulls = palloc(sizeof(bool) * execstate->tupdesc->natts);
	execstate->qual_list = NULL;
	foreach(lc, fscan->fdw_exprs)
	{
		extractRestrictions(bms_make_singleton(fscan->scan.scanrelid),
							((Expr *) lfirst(lc)),
							&execstate->qual_list);
	}

	execstate->subscanCxt = AllocSetContextCreate(
		node->ss.ps.state->es_query_cxt,
		"Multicorn subscan data",
		ALLOCSET_DEFAULT_SIZES);

	node->fdw_state = execstate;
}

/*
 * Wrapper around convert_tuples_by_name_map that returns NULL if the
 * CStore table/temporary materialization and our table are compatible.
 * We have a looser definition of compatibility than convert_tuples_by_name_map_if_req,
 * since we only need the indesc descriptor to start with the same columns in the same positions
 * (we request a set of columns from CStore and want them in the same positions in its
 * tuple slot as our tuple slot -- so if the CStore table has extra columns like
 * SG_UD_FLAG, we don't care.
 */
static AttrNumber *buildConvertMapIfNeeded(TupleDesc indesc, TupleDesc outdesc)
{
	AttrNumber *attrMap = convert_tuples_by_name_map(indesc, outdesc, "Error building subrelation attribute map");
	bool same = true;

	if (outdesc->natts <= indesc->natts)
	{
		for (int i = 0; i < outdesc->natts; i++)
		{
			Form_pg_attribute inatt = TupleDescAttr(indesc, i);
			Form_pg_attribute outatt = TupleDescAttr(outdesc, i);

			/*
			 * If the input column has a missing attribute, we need a
			 * conversion.
			 */
			if (inatt->atthasmissing)
			{
				same = false;
				break;
			}

			if (attrMap[i] == (i + 1))
				continue;

			/*
			 * If it's a dropped column and the corresponding input column is
			 * also dropped, we needn't convert.  However, attlen and attalign
			 * must agree.
			 */
			if (attrMap[i] == 0 &&
				inatt->attisdropped &&
				inatt->attlen == outatt->attlen &&
				inatt->attalign == outatt->attalign)
				continue;

			same = false;
			break;
		}
	} else
		same = false;

	if (same)
	{
		/* Runtime conversion is not needed */
		debug_elog("Runtime conversion is not needed");
		pfree(attrMap);
		return NULL;
	}
	else
		return attrMap;
}

/*
 * Generate a list of columns we need from CStore.
 *
 * Normally, the CStore file has the same schema as our own foreign table,
 * with the update-delete flag at the end. This means that we can build a
 * list of variables once, from our own schema, and CStore can use it
 * to compute a mask of which columns it needs from its file. But this
 * can backfire if the CStore file has swapped columns, so, to make
 * this more robust, we use the CStore's schema and grab variables
 * from that by matching up their names and the names that we need.
 */
static List *buildCStoreColumnList(TupleDesc desc, List* target_list, Index relid)
{
	List *result = NULL;
	ListCell *lc;

	foreach(lc, target_list)
	{
		for (int i = 0; i < desc->natts; i++)
		{
			Form_pg_attribute att = TupleDescAttr(desc, i);

			if (!att->attisdropped &&
				strcmp(NameStr(att->attname), strVal(lfirst(lc))) == 0)
			{
				debug_elog("CStore scan: need column %s (%d, attnum %d)", strVal(lfirst(lc)), i, att->attnum);
				result = lappend(result,
								 makeVar(relid, att->attnum, att->atttypid,
										 att->atttypmod, att->attcollation, 0));
				break;
			}
		}
	}
#ifdef DEBUG
	pprint(result);
#endif
	return result;
}

static void print_map(AttrNumber *attrMap, int map_length)
{
	for (int i = 0; i < map_length; i++)
	{
		printf("%d -> %d\n", i, attrMap[i]);
	}
}

static List *buildCStoreQualList(AttrNumber *attrMap, int map_length, List *quals, Index relid)
{
	List *result = NULL;
	ListCell *lc;
	bool whole_row;

	if (!attrMap) return quals;

#ifdef DEBUG
	print_map(attrMap, map_length);
#endif

	foreach(lc, quals)
	{
		/* map_variable_attnos replaces varattno n with attrMap[n-1] */
		Node *lqQual = lfirst(lc);
		Node *qual = map_variable_attnos(lqQual, relid, 0, attrMap, map_length, InvalidOid, &whole_row);
		if (whole_row)
		{
			ereport(ERROR, (errmsg("Error remapping LQFDW -> CStore qualifiers (whole row needs to be converted)")));
		}
#ifdef DEBUG
		printf("LQ QUAL\n");
		pprint(lqQual);
		printf("CStore QUAL\n");
		pprint(qual);
#endif
		result = lappend(result, qual);
	}

	return result;
}

/*
 * Debug functions to print TupleDesc structs (stolen from private PG),
 * not currently used anywhere.
 */
static void
printatt(unsigned attributeId,
		Form_pg_attribute attributeP)
{
	printf("\t%2d: %s\t(typeid = %u, len = %d, typmod = %d, byval = %c)\n",
			attributeId,
			NameStr(attributeP->attname),
			(unsigned int) (attributeP->atttypid),
			attributeP->attlen,
			attributeP->atttypmod,
			attributeP->attbyval ? 't' : 'f');
}

static void print_desc(TupleDesc desc)
{
	int         i;
	for (i = 0; i < desc->natts; ++i)
	{
		printatt((unsigned) i + 1, TupleDescAttr(desc, i));
	}
}

/*
 * End reading from a CStore/temporarily materialized table
 * and close the relation.
 */
static void subscanEnd(ForeignScanState *node)
{
	MulticornExecState *execstate = node->fdw_state;

	if (execstate->subscanRel != NULL) {
		if (execstate->subscanRel->rd_rel->relkind == RELKIND_FOREIGN_TABLE)
		{
			debug_elog("Closing CStore table");
			if (execstate->subscanState) CStoreEndRead((TableReadState *)(execstate->subscanState));
		}
		else
		{
			debug_elog("Closing temporarily materialized table");
			if (execstate->subscanState) table_endscan((TableScanDesc)(execstate->subscanState));
		}
		debug_elog("Read %ld tuple(s)", execstate->tuplesRead);
		execstate->subscanState = NULL;
		relation_close(execstate->subscanRel, AccessShareLock);
		execstate->subscanRel = NULL;
	}
	if (execstate->subscanSlot && execstate->subscanSlot != node->ss.ss_ScanTupleSlot)
	{
		ExecDropSingleTupleTableSlot(execstate->subscanSlot);
		execstate->subscanSlot = NULL;
	}
	MemoryContextReset(execstate->subscanCxt);
}

/*
 * Read a single row from the subscan relation
 */
static bool subscanReadRow(TupleTableSlot *slot, Relation subscanRel, void *subscanState)
{
	ExecClearTuple(slot);
	if (subscanRel->rd_rel->relkind == RELKIND_FOREIGN_TABLE)
	{
		TupleDesc tupleDescriptor = slot->tts_tupleDescriptor;

		/* Code partially copied from CStoreIterateForeignScan */
		memset(slot->tts_values, 0, tupleDescriptor->natts * sizeof(Datum));
		memset(slot->tts_isnull, true, tupleDescriptor->natts * sizeof(bool));

		if (CStoreReadNextRow((TableReadState *)subscanState,
							  slot->tts_values,
							  slot->tts_isnull)) {

			ExecStoreVirtualTuple(slot);
			return true;
		}
	}
	else
	{
		return (table_scan_getnextslot((TableScanDesc)subscanState,
							   ForwardScanDirection,
							   slot));
	}
	return false;
}


/*
* multicornIterateForeignScan
*		Retrieve next row from the result set, or clear tuple slot to indicate
*		EOF.
*
*		This is done by iterating over the result from the "execute" python
*		method.
*/
static TupleTableSlot *
multicornIterateForeignScan(ForeignScanState *node)
{
	TupleTableSlot *slot = node->ss.ss_ScanTupleSlot;
	MulticornExecState *execstate = node->fdw_state;
	PyObject   *p_value;
	MemoryContext oldcontext;

	/* The data flow here is kind of complex: we treat strings returned by
	 * Python as relation names to read data from directly instead of getting Python
	 * to return it to us.
	 *
	 * To read from those relations, we use a mixture of morally dubious meddling
	 * with CStore and heap internals, mimicking what a scan through these
	 * subrelations actually does.
	 *
	 * This is made more difficult by the fact that PG query planning machinery
	 * expects the relations to actually exist at query plan time -- for example,
	 * CStore's read planner needs the table's RangeTblEntry to be present in the
	 * planner's simple_rte_array, which we don't want to modify at query execution time.
	 *
	 */

	ExecClearTuple(slot);
	while (1)
	{
		if (execstate->subscanRel != NULL) {
			oldcontext = MemoryContextSwitchTo(execstate->subscanCxt);
			if (subscanReadRow(execstate->subscanSlot, execstate->subscanRel, execstate->subscanState))
			{
				if (execstate->subscanAttrMap)
				{
					/* Project the tuple into our own slot if the two tables are incompatible.
					 * This should only happen if the CStore fragment has the updated-deleted flag
					 * as its first column (which doesn't happen in the default Splitgraph configuration).
					 * Skipping this step if the tables are compatible speeds big scans by about 10-20%.
					 *
					 * If the two tables are compatible, execstate->subscanSlot maps to the same slot as the
					 * slot for the foreign scan itself.
					 */
					execute_attr_map_slot(execstate->subscanAttrMap,
										  execstate->subscanSlot,
										  slot);
				}
				else if (execstate->subscanRel->rd_rel->relkind != RELKIND_FOREIGN_TABLE)
				{
					/* For temporarily materialized tables, return the slot that
					 * they were writing into.
					 */
					MemoryContextSwitchTo(oldcontext);
					return execstate->subscanSlot;
				}
				MemoryContextSwitchTo(oldcontext);
				return slot;

//#ifdef DEBUG
//					print_desc(subscanSlot->tts_tupleDescriptor);
//					print_slot(subscanSlot);
//					fflush(stdout);
//#endif
			}
			else
			{
				subscanEnd(node);
			}
			MemoryContextSwitchTo(oldcontext);
		}
		// Get the next item from the iterator
		if (execstate->p_iterator == NULL)
		{
			execute(node, NULL);
		}
		if (execstate->p_iterator == Py_None)
		{
			/* No iterator returned from get_iterator */
			Py_DECREF(execstate->p_iterator);
			return slot;
		}
		p_value = PyIter_Next(execstate->p_iterator);
		errorCheck();
		/* A none value results in an empty slot. */
		if (p_value == NULL || p_value == Py_None)
		{
			Py_XDECREF(p_value);
			return slot;
		}

		if (PyBytes_Check(p_value))
		{
			/*
			 * If the iterator is a Bytes object, treat it as a relation
			 * to read data from (a cstore_fdw foreign table or a temporary
			 * table with materialization results);
			 */

			char	   *relation;
			Py_ssize_t	strlength = 0;

			if (PyString_AsStringAndSize(p_value, &relation, &strlength) < 0)
			{
				elog(ERROR, "Could not convert subrelation to string!");
			}

			debug_elog("Will get data from subrelation %s", relation);
			Py_DECREF(p_value);

			RangeVar *rangeVar = makeRangeVarFromNameList(
						textToQualifiedNameList(cstring_to_text(relation)));
			Relation subscanRel = relation_openrv(rangeVar, AccessShareLock);
			debug_elog("Opened relation %s", relation);
			execstate->subscanRel = subscanRel;

			/*
			 * Use a per-query context here that we made at scan start.
			 *
			 * Normally these methods are supposed to be called when the scan begins. In this case we're
			 * in the per-tuple context that gets reset after every tuple, so whatever
			 * CStore/heapam allocated for its query-lived buffers will get nuked, which
			 * we don't want to happen.
			 */
			oldcontext = MemoryContextSwitchTo(execstate->subscanCxt);
			TupleDesc desc = RelationGetDescr(subscanRel);
			execstate->tuplesRead = 0;
			execstate->subscanAttrMap = buildConvertMapIfNeeded(desc, slot->tts_tupleDescriptor);
			if (execstate->subscanAttrMap || subscanRel->rd_rel->relkind != RELKIND_FOREIGN_TABLE)
			{
				/* Allocate a tuple table slot for the subscan if we need conversion
				 * or we're scanning through a temporarily materialized table that needs
				 * a special kind of tuple slot.
				 */
				execstate->subscanSlot = MakeSingleTupleTableSlot(desc,
																  table_slot_callbacks(subscanRel));
			}
			else
			{
				execstate->subscanSlot = slot;
			}

			if (subscanRel->rd_rel->relkind == RELKIND_FOREIGN_TABLE) {
				/*
				 * If we opened a foreign table, use CStore routines to begin the read
				 * Partially copied from CStoreBeginForeignScan
				 */
				CStoreFdwOptions *cStoreFdwOptions = CStoreGetOptions(subscanRel->rd_id);
				ForeignScan *foreignScan = (ForeignScan *) node->ss.ps.plan;
				List *cStoreColumns = buildCStoreColumnList(desc, execstate->target_list,
															foreignScan->scan.scanrelid);
				List *cStoreQuals = buildCStoreQualList(execstate->subscanAttrMap,
														slot->tts_tupleDescriptor->natts,
														foreignScan->scan.plan.qual,
														foreignScan->scan.scanrelid);
				execstate->subscanState = CStoreBeginRead(cStoreFdwOptions->filename, desc,
														  cStoreColumns, cStoreQuals);
			} else {
				/*
				 * Begin the read through a temporarily materialized table.
				 * We use the latest snapshot instead of the current transaction
				 * snapshot. This breaks isolation, but otherwise we can't see
				 * the temporary table that Python wrote into.
				 */
				execstate->subscanState = table_beginscan(subscanRel,
														  GetLatestSnapshot(),
														  0, NULL);
			}
			MemoryContextSwitchTo(oldcontext);
		}
		else
		{
			slot->tts_values = execstate->values;
			slot->tts_isnull = execstate->nulls;
			pythonResultToTuple(p_value, slot, execstate->cinfos, execstate->buffer);
			ExecStoreVirtualTuple(slot);
			Py_DECREF(p_value);
			return slot;
		}
	}
}

/*
* multicornReScanForeignScan
*		Restart the scan
*/
static void
multicornReScanForeignScan(ForeignScanState *node)
{
	MulticornExecState *state = node->fdw_state;

	if (state->p_iterator)
	{
		Py_DECREF(state->p_iterator);
		state->p_iterator = NULL;
	}
	subscanEnd(node);
}

/*
*	multicornEndForeignScan
*		Finish scanning foreign table and dispose objects used for this scan.
*/
static void
multicornEndForeignScan(ForeignScanState *node)
{
	MulticornExecState *state = node->fdw_state;
	PyObject   *result = PyObject_CallMethod(state->fdw_instance, "end_scan", "()");

	errorCheck();
	Py_DECREF(result);
	Py_DECREF(state->fdw_instance);
	Py_XDECREF(state->p_iterator);
	state->p_iterator = NULL;
	subscanEnd(node);

	/* MemoryContexts will be deleted automatically. */
}



#if PG_VERSION_NUM >= 90300
/*
* multicornAddForeigUpdateTargets
*		Add resjunk columns needed for update/delete.
*/
static void
multicornAddForeignUpdateTargets(Query *parsetree,
								RangeTblEntry *target_rte,
								Relation target_relation)
{
	Var		   *var = NULL;
	TargetEntry *tle,
			*returningTle;
	PyObject   *instance = getInstance(target_relation->rd_id);
	const char *attrname = getRowIdColumn(instance);
	TupleDesc	desc = target_relation->rd_att;
	int			i;
	ListCell   *cell;

	foreach(cell, parsetree->returningList)
	{
		returningTle = lfirst(cell);
		tle = copyObject(returningTle);
		tle->resjunk = true;
		parsetree->targetList = lappend(parsetree->targetList, tle);
	}


	for (i = 0; i < desc->natts; i++)
	{
		Form_pg_attribute att = TupleDescAttr(desc, i);

		if (!att->attisdropped)
		{
			if (strcmp(NameStr(att->attname), attrname) == 0)
			{
				var = makeVar(parsetree->resultRelation,
							  att->attnum,
							  att->atttypid,
							  att->atttypmod,
							  att->attcollation,
							  0);
				break;
			}
		}
	}
	if (var == NULL)
	{
		ereport(ERROR, (errmsg("%s", "The rowid attribute does not exist")));
	}
	tle = makeTargetEntry((Expr *) var,
						  list_length(parsetree->targetList) + 1,
						  strdup(attrname),
						  true);
	parsetree->targetList = lappend(parsetree->targetList, tle);
	Py_DECREF(instance);
}


/*
 * multicornPlanForeignModify
 *		Plan a foreign write operation.
 *		This is done by checking the "supported operations" attribute
 *		on the python class.
 */
static List *
multicornPlanForeignModify(PlannerInfo *root,
						   ModifyTable *plan,
						   Index resultRelation,
						   int subplan_index)
{
	return NULL;
}


/*
 * multicornBeginForeignModify
 *		Initialize a foreign write operation.
 */
static void
multicornBeginForeignModify(ModifyTableState *mtstate,
							ResultRelInfo *resultRelInfo,
							List *fdw_private,
							int subplan_index,
							int eflags)
{
	MulticornModifyState *modstate = palloc0(sizeof(MulticornModifyState));
	Relation	rel = resultRelInfo->ri_RelationDesc;
	TupleDesc	desc = RelationGetDescr(rel);
	PlanState  *ps = mtstate->mt_plans[subplan_index];
	Plan	   *subplan = ps->plan;
	MemoryContext oldcontext;
	int			i;

	modstate->cinfos = palloc0(sizeof(ConversionInfo *) *
							   desc->natts);
	modstate->buffer = makeStringInfo();
	modstate->fdw_instance = getInstance(rel->rd_id);
	modstate->rowidAttrName = getRowIdColumn(modstate->fdw_instance);
	initConversioninfo(modstate->cinfos, TupleDescGetAttInMetadata(desc), NULL);
	oldcontext = MemoryContextSwitchTo(TopMemoryContext);
	MemoryContextSwitchTo(oldcontext);
	if (ps->ps_ResultTupleSlot)
	{
		TupleDesc	resultTupleDesc = ps->ps_ResultTupleSlot->tts_tupleDescriptor;

		modstate->resultCinfos = palloc0(sizeof(ConversionInfo *) *
										 resultTupleDesc->natts);
		initConversioninfo(modstate->resultCinfos, TupleDescGetAttInMetadata(resultTupleDesc), NULL);
	}
	for (i = 0; i < desc->natts; i++)
	{
		Form_pg_attribute att = TupleDescAttr(desc, i);

		if (!att->attisdropped)
		{
			if (strcmp(NameStr(att->attname), modstate->rowidAttrName) == 0)
			{
				modstate->rowidCinfo = modstate->cinfos[i];
				break;
			}
		}
	}
	modstate->rowidAttno = ExecFindJunkAttributeInTlist(subplan->targetlist, modstate->rowidAttrName);
	resultRelInfo->ri_FdwState = modstate;
}

/*
 * multicornExecForeignInsert
 *		Execute a foreign insert operation
 *		This is done by calling the python "insert" method.
 */
static TupleTableSlot *
multicornExecForeignInsert(EState *estate, ResultRelInfo *resultRelInfo,
						   TupleTableSlot *slot, TupleTableSlot *planSlot)
{
	MulticornModifyState *modstate = resultRelInfo->ri_FdwState;
	PyObject   *fdw_instance = modstate->fdw_instance;
	PyObject   *values = tupleTableSlotToPyObject(slot, modstate->cinfos);
	PyObject   *p_new_value = PyObject_CallMethod(fdw_instance, "insert", "(O)", values);

	errorCheck();
	if (p_new_value && p_new_value != Py_None)
	{
		ExecClearTuple(slot);
		pythonResultToTuple(p_new_value, slot, modstate->cinfos, modstate->buffer);
		ExecStoreVirtualTuple(slot);
	}
	Py_XDECREF(p_new_value);
	Py_DECREF(values);
	errorCheck();
	return slot;
}

/*
 * multicornExecForeignDelete
 *		Execute a foreign delete operation
 *		This is done by calling the python "delete" method, with the opaque
 *		rowid that was supplied.
 */
static TupleTableSlot *
multicornExecForeignDelete(EState *estate, ResultRelInfo *resultRelInfo,
						   TupleTableSlot *slot, TupleTableSlot *planSlot)
{
	MulticornModifyState *modstate = resultRelInfo->ri_FdwState;
	PyObject   *fdw_instance = modstate->fdw_instance,
			   *p_row_id,
			   *p_new_value;
	bool		is_null;
	ConversionInfo *cinfo = modstate->rowidCinfo;
	Datum		value = ExecGetJunkAttribute(planSlot, modstate->rowidAttno, &is_null);

	p_row_id = datumToPython(value, cinfo->atttypoid, cinfo);
	p_new_value = PyObject_CallMethod(fdw_instance, "delete", "(O)", p_row_id);
	errorCheck();
	if (p_new_value == NULL || p_new_value == Py_None)
	{
		Py_XDECREF(p_new_value);
		p_new_value = tupleTableSlotToPyObject(planSlot, modstate->resultCinfos);
	}
	ExecClearTuple(slot);
	pythonResultToTuple(p_new_value, slot, modstate->cinfos, modstate->buffer);
	ExecStoreVirtualTuple(slot);
	Py_DECREF(p_new_value);
	Py_DECREF(p_row_id);
	errorCheck();
	return slot;
}

/*
 * multicornExecForeignUpdate
 *		Execute a foreign update operation
 *		This is done by calling the python "update" method, with the opaque
 *		rowid that was supplied.
 */
static TupleTableSlot *
multicornExecForeignUpdate(EState *estate, ResultRelInfo *resultRelInfo,
						   TupleTableSlot *slot, TupleTableSlot *planSlot)
{
	MulticornModifyState *modstate = resultRelInfo->ri_FdwState;
	PyObject   *fdw_instance = modstate->fdw_instance,
			   *p_row_id,
			   *p_new_value,
			   *p_value = tupleTableSlotToPyObject(slot, modstate->cinfos);
	bool		is_null;
	ConversionInfo *cinfo = modstate->rowidCinfo;
	Datum		value = ExecGetJunkAttribute(planSlot, modstate->rowidAttno, &is_null);

	p_row_id = datumToPython(value, cinfo->atttypoid, cinfo);
	p_new_value = PyObject_CallMethod(fdw_instance, "update", "(O,O)", p_row_id,
									  p_value);
	errorCheck();
	if (p_new_value != NULL && p_new_value != Py_None)
	{
		ExecClearTuple(slot);
		pythonResultToTuple(p_new_value, slot, modstate->cinfos, modstate->buffer);
		ExecStoreVirtualTuple(slot);
	}
	Py_XDECREF(p_new_value);
	Py_DECREF(p_row_id);
	errorCheck();
	return slot;
}

/*
 * multicornEndForeignModify
 *		Clean internal state after a modify operation.
 */
static void
multicornEndForeignModify(EState *estate, ResultRelInfo *resultRelInfo)

{
	MulticornModifyState *modstate = resultRelInfo->ri_FdwState;
	PyObject   *result = PyObject_CallMethod(modstate->fdw_instance, "end_modify", "()");

	errorCheck();
	Py_DECREF(modstate->fdw_instance);
	Py_DECREF(result);
}

/*
 * Callback used to propagate a subtransaction end.
 */
static void
multicorn_subxact_callback(SubXactEvent event, SubTransactionId mySubid,
						   SubTransactionId parentSubid, void *arg)
{
	PyObject   *instance;
	int			curlevel;
	HASH_SEQ_STATUS status;
	CacheEntry *entry;

	/* Nothing to do after commit or subtransaction start. */
	if (event == SUBXACT_EVENT_COMMIT_SUB || event == SUBXACT_EVENT_START_SUB)
		return;

	curlevel = GetCurrentTransactionNestLevel();

	hash_seq_init(&status, InstancesHash);

	while ((entry = (CacheEntry *) hash_seq_search(&status)) != NULL)
	{
		if (entry->xact_depth < curlevel)
			continue;

		instance = entry->value;
		if (event == SUBXACT_EVENT_PRE_COMMIT_SUB)
		{
			PyObject_CallMethod(instance, "sub_commit", "(i)", curlevel);
		}
		else
		{
			PyObject_CallMethod(instance, "sub_rollback", "(i)", curlevel);
		}
		errorCheck();
		entry->xact_depth--;
	}
}
#endif

/*
 * Callback used to propagate pre-commit / commit / rollback.
 */
static void
multicorn_xact_callback(XactEvent event, void *arg)
{
	PyObject   *instance;
	HASH_SEQ_STATUS status;
	CacheEntry *entry;

	hash_seq_init(&status, InstancesHash);
	while ((entry = (CacheEntry *) hash_seq_search(&status)) != NULL)
	{
		instance = entry->value;
		if (entry->xact_depth == 0)
			continue;

		switch (event)
		{
#if PG_VERSION_NUM >= 90300
			case XACT_EVENT_PRE_COMMIT:
				PyObject_CallMethod(instance, "pre_commit", "()");
				break;
#endif
			case XACT_EVENT_COMMIT:
				PyObject_CallMethod(instance, "commit", "()");
				entry->xact_depth = 0;
				break;
			case XACT_EVENT_ABORT:
				PyObject_CallMethod(instance, "rollback", "()");
				entry->xact_depth = 0;
				break;
			default:
				break;
		}
		errorCheck();
	}
}

#if PG_VERSION_NUM >= 90500
static List *
multicornImportForeignSchema(ImportForeignSchemaStmt * stmt,
							 Oid serverOid)
{
	List	   *cmds = NULL;
	List	   *options = NULL;
	UserMapping *mapping;
	ForeignServer *f_server;
	char	   *restrict_type = NULL;
	PyObject   *p_class = NULL;
	PyObject   *p_tables,
			   *p_srv_options,
			   *p_options,
			   *p_restrict_list,
			   *p_iter,
			   *p_item;
	ListCell   *lc;

	f_server = GetForeignServer(serverOid);
	foreach(lc, f_server->options)
	{
		DefElem    *option = (DefElem *) lfirst(lc);

		if (strcmp(option->defname, "wrapper") == 0)
		{
			p_class = getClassString(defGetString(option));
			errorCheck();
		}
		else
		{
			options = lappend(options, option);
		}
	}
	mapping = multicorn_GetUserMapping(GetUserId(), serverOid);
	if (mapping)
		options = list_concat(options, mapping->options);

	if (p_class == NULL)
	{
		/*
		 * This should never happen, since we validate the wrapper parameter
		 * at
		 */
		/* object creation time. */
		ereport(ERROR, (errmsg("%s", "The wrapper parameter is mandatory, specify a valid class name")));
	}
	switch (stmt->list_type)
	{
		case FDW_IMPORT_SCHEMA_LIMIT_TO:
			restrict_type = "limit";
			break;
		case FDW_IMPORT_SCHEMA_EXCEPT:
			restrict_type = "except";
			break;
		case FDW_IMPORT_SCHEMA_ALL:
			break;
	}
	p_srv_options = optionsListToPyDict(options);
	p_options = optionsListToPyDict(stmt->options);
	p_restrict_list = PyList_New(0);
	foreach(lc, stmt->table_list)
	{
		RangeVar   *rv = (RangeVar *) lfirst(lc);
		PyObject   *p_tablename = PyUnicode_Decode(
											rv->relname, strlen(rv->relname),
												   getPythonEncodingName(),
												   NULL);

		errorCheck();
		PyList_Append(p_restrict_list, p_tablename);
		Py_DECREF(p_tablename);
	}
	errorCheck();
	p_tables = PyObject_CallMethod(p_class, "import_schema", "(s, O, O, s, O)",
							   stmt->remote_schema, p_srv_options, p_options,
								   restrict_type, p_restrict_list);
	errorCheck();
	Py_DECREF(p_class);
	Py_DECREF(p_options);
	Py_DECREF(p_srv_options);
	Py_DECREF(p_restrict_list);
	errorCheck();
	p_iter = PyObject_GetIter(p_tables);
	while ((p_item = PyIter_Next(p_iter)))
	{
		PyObject   *p_string;
		char	   *value;

		p_string = PyObject_CallMethod(p_item, "to_statement", "(s,s)",
								   stmt->local_schema, f_server->servername);
		errorCheck();
		value = PyString_AsString(p_string);
		errorCheck();
		cmds = lappend(cmds, pstrdup(value));
		Py_DECREF(p_string);
		Py_DECREF(p_item);
	}
	errorCheck();
	Py_DECREF(p_iter);
	Py_DECREF(p_tables);
	return cmds;
}

static bool
multicornIsForeignScanParallelSafe(PlannerInfo *root, RelOptInfo *rel,
								RangeTblEntry *rte)
{
	return true;
}
#endif

/*
 * Merge FDW options from input relations into a new set of options for a join
 * or an upper rel.
 *
 * For a join relation, FDW-specific information about the inner and outer
 * relations is provided using fpinfo_i and fpinfo_o.  For an upper relation,
 * fpinfo_o provides the information for the input relation; fpinfo_i is
 * expected to NULL.
 */
static void
multicorn_merge_fdw_options(MulticornPlanState *fpinfo,
				  const MulticornPlanState *fpinfo_o,
				  const MulticornPlanState *fpinfo_i)
{
	/* We must always have fpinfo_o. */
	Assert(fpinfo_o);

	/* fpinfo_i may be NULL, but if present the servers must both match. */
	Assert(!fpinfo_i ||
		   fpinfo_i->server->serverid == fpinfo_o->server->serverid);

	/*
	 * Copy the server specific FDW options.  (For a join, both relations come
	 * from the same server, so the server options should have the same value
	 * for both relations.)
	 */
	fpinfo->fdw_startup_cost = fpinfo_o->fdw_startup_cost;
	fpinfo->fdw_tuple_cost = fpinfo_o->fdw_tuple_cost;
	fpinfo->shippable_extensions = fpinfo_o->shippable_extensions;
	fpinfo->use_remote_estimate = fpinfo_o->use_remote_estimate;
	fpinfo->fetch_size = fpinfo_o->fetch_size;

    /* Multicorn specific options */
    fpinfo->fdw_instance = fpinfo_o->fdw_instance;
    fpinfo->foreigntableid = fpinfo_o->foreigntableid;
	fpinfo->numattrs = fpinfo_o->numattrs;
    fpinfo->cinfos = fpinfo_o->cinfos;
    fpinfo->pathkeys = fpinfo_o->pathkeys;
    fpinfo->target_list = fpinfo_o->target_list;
    fpinfo->qual_list = fpinfo_o->qual_list;
    fpinfo->pathkeys = fpinfo_o->pathkeys;

	/* Merge the table level options from either side of the join. */
	if (fpinfo_i)
	{
		/*
		 * We'll prefer to use remote estimates for this join if any table
		 * from either side of the join is using remote estimates.  This is
		 * most likely going to be preferred since they're already willing to
		 * pay the price of a round trip to get the remote EXPLAIN.  In any
		 * case it's not entirely clear how we might otherwise handle this
		 * best.
		 */
		fpinfo->use_remote_estimate = fpinfo_o->use_remote_estimate ||
			fpinfo_i->use_remote_estimate;

		/*
		 * Set fetch size to maximum of the joining sides, since we are
		 * expecting the rows returned by the join to be proportional to the
		 * relation sizes.
		 */
		fpinfo->fetch_size = Max(fpinfo_o->fetch_size, fpinfo_i->fetch_size);
	}
}

/*
 * Assess whether the aggregation, grouping and having operations can be pushed
 * down to the foreign server.  As a side effect, save information we obtain in
 * this function to MulticornPlanState of the input relation.
 */
static bool
multicorn_foreign_grouping_ok(PlannerInfo *root, RelOptInfo *grouped_rel,
                              Node *havingQual)
{
	Query	   *query = root->parse;
	MulticornPlanState *fpinfo = (MulticornPlanState *) grouped_rel->fdw_private;
    PathTarget *grouping_target = grouped_rel->reltarget;
    // Q: Or perhaps like in SQLite FDW `PathTarget *grouping_target = root->upper_targets[UPPERREL_GROUP_AGG];`?
    // A: It appears they are the same thing; see also GridDBs sortgrouprefs explanation
	MulticornPlanState *ofpinfo;
	ListCell   *lc;
	int			i;
	List	   *tlist = NIL;

	/* We currently don't support pushing Grouping Sets. */
	if (query->groupingSets)
		return false;

	/* Get the fpinfo of the underlying scan relation. */
	ofpinfo = (MulticornPlanState *) fpinfo->outerrel->fdw_private;

	/*
	 * If underlying scan relation has any local conditions, those conditions
	 * are required to be applied before performing aggregation.  Hence the
	 * aggregate cannot be pushed down.
	 */
	if (ofpinfo->local_conds)
		return false;

    /*
	 * Examine grouping expressions, as well as other expressions we'd need to
	 * compute, and check whether they are safe to push down to the foreign
	 * server.  All GROUP BY expressions will be part of the grouping target
	 * and thus there is no need to search for them separately.  Add grouping
	 * expressions into target list which will be passed to foreign server.
     *
     * A tricky fine point is that we must not put any expression into the
	 * target list that is just a foreign param (that is, something that
	 * deparse.c would conclude has to be sent to the foreign server).  If we
	 * do, the expression will also appear in the fdw_exprs list of the plan
	 * node, and setrefs.c will get confused and decide that the fdw_exprs
	 * entry is actually a reference to the fdw_scan_tlist entry, resulting in
	 * a broken plan.  Somewhat oddly, it's OK if the expression contains such
	 * a node, as long as it's not at top level; then no match is possible.
	 */
	i = 0;
	foreach(lc, grouping_target->exprs)
	{
		Expr	   *expr = (Expr *) lfirst(lc);
		Index		sgref = get_pathtarget_sortgroupref(grouping_target, i);
		ListCell   *l;

		/* Check whether this expression is part of GROUP BY clause */
		if (sgref && get_sortgroupref_clause_noerr(sgref, query->groupClause))
		{
			TargetEntry *tle;

            /*
			 * Ensure GROUP BY clauses are shippable at all by the corresponding
             * Python FDW instance.
			 */
            if (!fpinfo->groupby_supported)
                return false;

			/*
			 * If any GROUP BY expression is not shippable, then we cannot
			 * push down aggregation to the foreign server.
			 */
			if (!multicorn_is_foreign_expr(root, grouped_rel, expr))
				return false;

			/*
			 * If it would be a foreign param, we can't put it into the tlist,
			 * so we have to fail.
			 */
			if (multicorn_is_foreign_param(root, grouped_rel, expr))
				return false;

			/*
			 * Pushable, so add to tlist.  We need to create a TLE for this
			 * expression and apply the sortgroupref to it.  We cannot use
			 * add_to_flat_tlist() here because that avoids making duplicate
			 * entries in the tlist.  If there are duplicate entries with
			 * distinct sortgrouprefs, we have to duplicate that situation in
			 * the output tlist.
			 */
			tle = makeTargetEntry(expr, list_length(tlist) + 1, NULL, false);
			tle->ressortgroupref = sgref;
			tlist = lappend(tlist, tle);
		}
		else
		{
            /*
			 * Ensure aggregation functions are shippable at all by the corresponding
             * Python FDW instance.
			 */
            if (!fpinfo->agg_functions)
                return false;

			/*
			 * Non-grouping expression we need to compute.  Can we ship it
			 * as-is to the foreign server?
			 */
			if (multicorn_is_foreign_expr(root, grouped_rel, expr) &&
				!multicorn_is_foreign_param(root, grouped_rel, expr))
			{
				/* Yes, so add to tlist as-is; OK to suppress duplicates */
				tlist = add_to_flat_tlist(tlist, list_make1(expr));
			}
			else
			{
				/* Not pushable as a whole; extract its Vars and aggregates */
                List	   *aggvars;

				aggvars = pull_var_clause((Node *) expr,
										  PVC_INCLUDE_AGGREGATES);

                /*
				 * If any aggregate expression is not shippable, then we
				 * cannot push down aggregation to the foreign server.  (We
				 * don't have to check is_foreign_param, since that certainly
				 * won't return true for any such expression.)
				 */
				if (!multicorn_is_foreign_expr(root, grouped_rel, (Expr *) aggvars))
					return false;

				/*
				 * Add aggregates, if any, into the targetlist.  Plain Vars
				 * outside an aggregate can be ignored, because they should be
				 * either same as some GROUP BY column or part of some GROUP
				 * BY expression.  In either case, they are already part of
				 * the targetlist and thus no need to add them again.  In fact
				 * including plain Vars in the tlist when they do not match a
				 * GROUP BY column would cause the foreign server to complain
				 * that the shipped query is invalid.
				 */
				foreach(l, aggvars)
				{
					Expr	   *expr = (Expr *) lfirst(l);

					if (IsA(expr, Aggref))
						tlist = add_to_flat_tlist(tlist, list_make1(expr));
				}
			}
		}

		i++;
	}

	/*
     * TODO: Enable HAVING clause pushdowns.
     * Note that certain simple HAVING clauses get transformed to WHERE clauses
     * internally, so those will be supported. Example is a HAVING clause on a
     * column that is also a part of the GROUP BY clause, in which case WHERE
     * clause effectively achieves the same thing.
	 */
	if (havingQual)
	{
		return false;
	}

	/* Store generated targetlist */
	fpinfo->grouped_tlist = tlist;

	/* Safe to pushdown */
	fpinfo->pushdown_safe = true;

	/*
	 * If user is willing to estimate cost for a scan using EXPLAIN, he
	 * intends to estimate scans on that relation more accurately. Then, it
	 * makes sense to estimate the cost of the grouping on that relation more
	 * accurately using EXPLAIN.
	 */
	fpinfo->use_remote_estimate = ofpinfo->use_remote_estimate;

	/* Copy startup and tuple cost as is from underneath input rel's fpinfo */
	fpinfo->fdw_startup_cost = ofpinfo->fdw_startup_cost;
	fpinfo->fdw_tuple_cost = ofpinfo->fdw_tuple_cost;

	/*
	 * Set # of retrieved rows and cached relation costs to some negative
	 * value, so that we can detect when they are set to some sensible values,
	 * during one (usually the first) of the calls to multicorn_estimate_path_cost_size.
	 */
	fpinfo->retrieved_rows = -1;
	fpinfo->rel_startup_cost = -1;
	fpinfo->rel_total_cost = -1;


	/*
	 * Set the string describing this grouped relation to be used in EXPLAIN
	 * output of corresponding ForeignScan.
	 */
    fpinfo->relation_name = NULL;

	return true;
}

/*
 * multicornGetForeignUpperPaths
 *		Add paths for post-join operations like aggregation, grouping etc. if
 *		corresponding operations are safe to push down.
 *
 * Right now, we only support aggregate, grouping and having clause pushdown.
 */
static void
multicornGetForeignUpperPaths(PlannerInfo *root, UpperRelationKind stage,
						      RelOptInfo *input_rel, RelOptInfo *output_rel, void *extra
)
{
	MulticornPlanState *fpinfo;

	/*
	 * If input rel is not safe to pushdown, then simply return as we cannot
	 * perform any post-join operations on the foreign server.
	 */
	if (!input_rel->fdw_private ||
		!((MulticornPlanState *) input_rel->fdw_private)->pushdown_safe)
		return;

	/* Ignore stages we don't support; and skip any duplicate calls. */
	if (stage != UPPERREL_GROUP_AGG || output_rel->fdw_private)
		return;

    /* Check with the Python FDW instance whether it supports pushdown at all */
    if (!canPushdownUpperrel((MulticornPlanState *) input_rel->fdw_private))
    {
        return;
    }

	fpinfo = (MulticornPlanState *) palloc0(sizeof(MulticornPlanState));
	fpinfo->pushdown_safe = false;
	fpinfo->stage = stage;
	output_rel->fdw_private = fpinfo;

	switch (stage)
	{
		case UPPERREL_GROUP_AGG:
			multicorn_add_foreign_grouping_paths(root, input_rel, output_rel, (GroupPathExtraData *) extra);
			break;
		default:
			elog(ERROR, "unexpected upper relation: %d", (int) stage);
			break;
	}
}

/*
 * multicorn_add_foreign_grouping_paths
 *		Add foreign path for grouping and/or aggregation.
 *
 * Given input_rel represents the underlying scan.  The paths are added to the
 * given grouped_rel.
 */
static void
multicorn_add_foreign_grouping_paths(PlannerInfo *root, RelOptInfo *input_rel,
								     RelOptInfo *grouped_rel,
                                     GroupPathExtraData *extra
)
{
	Query	   *parse = root->parse;
	MulticornPlanState *ifpinfo = input_rel->fdw_private;
	MulticornPlanState *fpinfo = grouped_rel->fdw_private;
	ForeignPath *grouppath;
	double		rows;
	int			width;
	Cost		startup_cost;
	Cost		total_cost;

	/* Nothing to be done, if there is no grouping or aggregation required. */
	if (!parse->groupClause && !parse->groupingSets && !parse->hasAggs &&
		!root->hasHavingQual)
		return;

	Assert(extra->patype == PARTITIONWISE_AGGREGATE_NONE ||
		   extra->patype == PARTITIONWISE_AGGREGATE_FULL);

	/* save the input_rel as outerrel in fpinfo */
	fpinfo->outerrel = input_rel;

	/*
	 * Copy foreign table, foreign server, user mapping, shippable extensions
	 * etc. details from the input relation's fpinfo.
	 */
    fpinfo->table = ifpinfo->table;
	fpinfo->server = ifpinfo->server;
	fpinfo->user = ifpinfo->user;
    fpinfo->groupby_supported = ifpinfo->groupby_supported;
	fpinfo->agg_functions = ifpinfo->agg_functions;
    multicorn_merge_fdw_options(fpinfo, ifpinfo, NULL);

    /*
	 * Assess if it is safe to push down aggregation and grouping.
	 *
	 * Use HAVING qual from extra. In case of child partition, it will have
	 * translated Vars.
	 */
	if (!multicorn_foreign_grouping_ok(root, grouped_rel, extra->havingQual))
    	return;

	/* Use small cost to push down aggregate always */
	rows = width = startup_cost = total_cost = 1;
	/* Now update this information in the fpinfo */
	fpinfo->rows = rows;
	fpinfo->width = width;
	fpinfo->startup_cost = startup_cost;
	fpinfo->total_cost = total_cost;

	/* Create and add foreign path to the grouping relation. */
	grouppath = create_foreign_upper_path(root,
										  grouped_rel,
										  grouped_rel->reltarget,
										  rows,
										  startup_cost,
										  total_cost,
										  NIL,	/* no pathkeys */
										  NULL,
										  NIL); /* no fdw_private */

	/* Add generated path into grouped_rel by add_path(). */
	add_path(grouped_rel, (Path *) grouppath);
}

/*
 *	"Serialize" a MulticornPlanState, so that it is safe to be carried
 *	between the plan and the execution safe.
 */
void *
serializePlanState(MulticornPlanState * state)
{
	List	   *result = NULL;

	result = lappend(result, makeConst(INT4OID,
						  -1, InvalidOid, 4, Int32GetDatum(state->numattrs), false, true));
	result = lappend(result, makeConst(INT4OID,
					-1, InvalidOid, 4, Int32GetDatum(state->foreigntableid), false, true));
	result = lappend(result, state->target_list);

	result = lappend(result, serializeDeparsedSortGroup(state->pathkeys));

    result = lappend(result, state->upper_rel_targets);

    result = lappend(result, state->aggs);

    result = lappend(result, state->group_clauses);

	return result;
}

/*
 *	"Deserialize" an internal state and inject it in an
 *	MulticornExecState
 */
MulticornExecState *
initializeExecState(void *internalstate)
{
	MulticornExecState *execstate = palloc0(sizeof(MulticornExecState));
	List	   *values = (List *) internalstate;
	AttrNumber	attnum = ((Const *) linitial(values))->constvalue;
	Oid			foreigntableid = ((Const *) lsecond(values))->constvalue;
	List		*pathkeys;

	/* Those list must be copied, because their memory context can become */
	/* invalid during the execution (in particular with the cursor interface) */
	execstate->target_list = copyObject(lthird(values));
	pathkeys = lfourth(values);
	execstate->pathkeys = deserializeDeparsedSortGroup(pathkeys);
	execstate->fdw_instance = getInstance(foreigntableid);
	execstate->buffer = makeStringInfo();
	execstate->cinfos = palloc0(sizeof(ConversionInfo *) * attnum);
	execstate->values = palloc(attnum * sizeof(Datum));
	execstate->nulls = palloc(attnum * sizeof(bool));
	execstate->subscanRel = NULL;
	execstate->subscanState = NULL;
    execstate->upper_rel_targets = list_nth(values, 4);
    execstate->aggs = list_nth(values, 5);
    execstate->group_clauses = list_nth(values, 6);
	return execstate;
}
