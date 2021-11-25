/*-------------------------------------------------------------------------
 *
 * Multicorn Foreign Data Wrapper for PostgreSQL
 *
 * IDENTIFICATION
 *        deparse.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "pgtime.h"
#include "access/heapam.h"
#include "access/htup_details.h"
#include "access/sysattr.h"
#include "catalog/pg_aggregate.h"
#include "catalog/pg_collation.h"
#include "catalog/pg_namespace.h"
#include "catalog/pg_operator.h"
#include "catalog/pg_proc.h"
#include "catalog/pg_type.h"
#include "commands/defrem.h"
#include "nodes/nodeFuncs.h"
#include "nodes/plannodes.h"
#include "optimizer/clauses.h"
#include "optimizer/optimizer.h"
#include "optimizer/tlist.h"
#include "parser/parsetree.h"
#include "utils/builtins.h"
#include "utils/lsyscache.h"
#include "utils/syscache.h"
#include "utils/timestamp.h"
#include "utils/typcache.h"
#include "commands/tablecmds.h"

#include "multicorn.h"


/*
 * Global context for multicorn_foreign_expr_walker's search of an expression tree.
 */
typedef struct foreign_glob_cxt
{
	PlannerInfo *root;			/* global planner state */
	RelOptInfo *foreignrel;		/* the foreign relation we are planning for */

	/*
	 * For join pushdown, only a limited set of operators are allowed to be
	 * pushed.  This flag helps us identify if we are walking through the list
	 * of join conditions. Also true for aggregate relations to restrict
	 * aggregates for specified list.
	 */
	bool		is_remote_cond;	/* true for join or aggregate relations */
	Relids		relids;			/* relids of base relations in the underlying
								 * scan */
} foreign_glob_cxt;

/*
 * Local (per-tree-level) context for multicorn_foreign_expr_walker's search.
 * This is concerned with identifying collations used in the expression.
 */
typedef enum
{
	FDW_COLLATE_NONE,			/* expression is of a noncollatable type */
	FDW_COLLATE_SAFE,			/* collation derives from a foreign Var */
	FDW_COLLATE_UNSAFE			/* collation derives from something else */
} FDWCollateState;

typedef struct foreign_loc_cxt
{
	Oid			collation;		/* OID of current collation, if any */
	FDWCollateState state;		/* state of current collation choice */
} foreign_loc_cxt;

/*
 * Return true if given object is one of PostgreSQL's built-in objects.
 *
 * We use FirstBootstrapObjectId as the cutoff, so that we only consider
 * objects with hand-assigned OIDs to be "built in", not for instance any
 * function or type defined in the information_schema.
 *
 * Our constraints for dealing with types are tighter than they are for
 * functions or operators: we want to accept only types that are in pg_catalog,
 * else format_type might incorrectly fail to schema-qualify their names.
 * (This could be fixed with some changes to format_type, but for now there's
 * no need.)  Thus we must exclude information_schema types.
 *
 * XXX there is a problem with this, which is that the set of built-in
 * objects expands over time.  Something that is built-in to us might not
 * be known to the remote server, if it's of an older version.  But keeping
 * track of that would be a huge exercise.
 */
static bool
multicorn_is_builtin(Oid oid)
{
	return (oid < FirstBootstrapObjectId);
}


static bool
multicorn_is_valid_type(Oid type)
{
	switch (type)
	{
		case INT2OID:
		case INT4OID:
		case INT8OID:
		case OIDOID:
		case FLOAT4OID:
		case FLOAT8OID:
		case NUMERICOID:
		case VARCHAROID:
		case TEXTOID:
		case TIMEOID:
		case TIMESTAMPOID:
		case TIMESTAMPTZOID:
			return true;
	}
	return false;
}


/*
 * Check if expression is safe to execute remotely, and return true if so.
 *
 * In addition, *outer_cxt is updated with collation information.
 *
 * We must check that the expression contains only node types we can deparse,
 * that all types/functions/operators are safe to send (which we approximate
 * as being built-in), and that all collations used in the expression derive
 * from Vars of the foreign table.  Because of the latter, the logic is
 * pretty close to assign_collations_walker() in parse_collate.c, though we
 * can assume here that the given expression is valid.
 */
static bool
multicorn_foreign_expr_walker(Node *node,
						      foreign_glob_cxt *glob_cxt,
						      foreign_loc_cxt *outer_cxt)
{
	bool		check_type = true;
    //MulticornFdwRelationInfo *fpinfo;
	foreign_loc_cxt inner_cxt;
	Oid			collation = InvalidOid;
	FDWCollateState state = FDW_COLLATE_NONE;
	HeapTuple	tuple;
	Form_pg_operator form;

	/* Need do nothing for empty subexpressions */
	if (node == NULL)
		return true;

    /* May need server info from baserel's fdw_private struct */
	//fpinfo = (MulticornFdwRelationInfo *) (glob_cxt->foreignrel->fdw_private);

	/* Set up inner_cxt for possible recursion to child nodes */
	inner_cxt.collation = InvalidOid;
	inner_cxt.state = FDW_COLLATE_NONE;
	switch (nodeTag(node))
	{
		case T_Var:
			{
				Var *var = (Var *) node;

				/*
				 * If the Var is from the foreign table, we consider its
				 * collation (if any) safe to use.  If it is from another
				 * table, we treat its collation the same way as we would a
				 * Param's collation, ie it's not safe for it to have a
				 * non-default collation.
				 */
				if (bms_is_member(var->varno, glob_cxt->relids) &&
					var->varlevelsup == 0)
				{
					/* Var belongs to foreign table */

					/*
					 * System columns (e.g. oid, ctid) should not be sent to
					 * the remote, since we don't make any effort to ensure
					 * that local and remote values match (tableoid, in
					 * particular, almost certainly doesn't match).
					 */
					if (var->varattno < 0)
						return false;

					/* Else check the collation */
					collation = var->varcollid;
					state = OidIsValid(collation) ? FDW_COLLATE_SAFE : FDW_COLLATE_NONE;
				}
				else
				{
					/* Var belongs to some other table */
					collation = var->varcollid;
					if (collation == InvalidOid ||
						collation == DEFAULT_COLLATION_OID)
					{
						/*
						 * It's noncollatable, or it's safe to combine with a
						 * collatable foreign Var, so set state to NONE.
						 */
						state = FDW_COLLATE_NONE;
					}
					else
					{
						/*
						 * Do not fail right away, since the Var might appear
						 * in a collation-insensitive context.
						 */
						state = FDW_COLLATE_UNSAFE;
					}
				}
			}
			break;
		case T_Const:
			{
				Const	   *c = (Const *) node;

				/* TODO: check whether the remote can handle various types */
				if (c->consttype == INTERVALOID ||
					c->consttype == BITOID ||
					c->consttype == VARBITOID)
					return false;

				/*
				 * If the constant has nondefault collation, either it's of a
				 * non-builtin type, or it reflects folding of a CollateExpr;
				 * either way, it's unsafe to send to the remote.
				 */
				if (c->constcollid != InvalidOid &&
					c->constcollid != DEFAULT_COLLATION_OID)
					return false;

				/* Otherwise, we can consider that it doesn't set collation */
				collation = InvalidOid;
				state = FDW_COLLATE_NONE;
			}
			break;
		case T_CaseTestExpr:
			{
				CaseTestExpr *c = (CaseTestExpr *) node;

				/*
				 * If the expr has nondefault collation, either it's of a
				 * non-builtin type, or it reflects folding of a CollateExpr;
				 * either way, it's unsafe to send to the remote.
				 */
				if (c->collation != InvalidOid &&
					c->collation != DEFAULT_COLLATION_OID)
					return false;

				/* Otherwise, we can consider that it doesn't set collation */
				collation = InvalidOid;
				state = FDW_COLLATE_NONE;
			}
			break;
		case T_Param:
			{
				Param	   *p = (Param *) node;

				/*
				 * If it's a MULTIEXPR Param, punt.  We can't tell from here
				 * whether the referenced sublink/subplan contains any remote
				 * Vars; if it does, handling that is too complicated to
				 * consider supporting at present.  Fortunately, MULTIEXPR
				 * Params are not reduced to plain PARAM_EXEC until the end of
				 * planning, so we can easily detect this case.  (Normal
				 * PARAM_EXEC Params are safe to ship because their values
				 * come from somewhere else in the plan tree; but a MULTIEXPR
				 * references a sub-select elsewhere in the same targetlist,
				 * so we'd be on the hook to evaluate it somehow if we wanted
				 * to handle such cases as direct foreign updates.)
				 */
				if (p->paramkind == PARAM_MULTIEXPR)
					return false;

				if (!multicorn_is_valid_type(p->paramtype))
                    /* TODO: we'll probably need to forward this decision to Python */
					return false;

				/*
				 * Collation rule is same as for Consts and non-foreign Vars.
				 */
				collation = p->paramcollid;
				if (collation == InvalidOid ||
					collation == DEFAULT_COLLATION_OID)
					state = FDW_COLLATE_NONE;
				else
					state = FDW_COLLATE_UNSAFE;
			}
			break;
        case T_SubscriptingRef:
			{
				SubscriptingRef *ar = (SubscriptingRef *) node;

				/* Should not be in the join clauses of the Join-pushdown */
				if (glob_cxt->is_remote_cond)
					return false;

				/* Assignment should not be in restrictions. */
				if (ar->refassgnexpr != NULL)
					return false;

				/*
				 * Recurse to remaining subexpressions.  Since the array
				 * subscripts must yield (noncollatable) integers, they won't
				 * affect the inner_cxt state.
				 */
				if (!multicorn_foreign_expr_walker((Node *) ar->refupperindexpr,
										           glob_cxt, &inner_cxt))
					return false;
				if (!multicorn_foreign_expr_walker((Node *) ar->reflowerindexpr,
										           glob_cxt, &inner_cxt))
					return false;
				if (!multicorn_foreign_expr_walker((Node *) ar->refexpr,
										           glob_cxt, &inner_cxt))
					return false;

				/*
				 * Array subscripting should yield same collation as input,
				 * but for safety use same logic as for function nodes.
				 */
				collation = ar->refcollid;
				if (collation == InvalidOid)
					state = FDW_COLLATE_NONE;
				else if (inner_cxt.state == FDW_COLLATE_SAFE &&
						 collation == inner_cxt.collation)
					state = FDW_COLLATE_SAFE;
				else
					state = FDW_COLLATE_UNSAFE;
			}
			break;
		case T_FuncExpr:
			{
				FuncExpr   *func = (FuncExpr *) node;
				char	   *opername = NULL;
				Oid			schema;

				/* get function name and schema */
				tuple = SearchSysCache1(PROCOID, ObjectIdGetDatum(func->funcid));
				if (!HeapTupleIsValid(tuple))
				{
					elog(ERROR, "cache lookup failed for function %u", func->funcid);
				}
				opername = pstrdup(((Form_pg_proc) GETSTRUCT(tuple))->proname.data);
				schema = ((Form_pg_proc) GETSTRUCT(tuple))->pronamespace;
				ReleaseSysCache(tuple);

				/* ignore functions in other than the pg_catalog schema */
				if (schema != PG_CATALOG_NAMESPACE)
					return false;

				/* TODO: forward this decision into Python */
				if (!(func->funcformat == COERCE_IMPLICIT_CAST
					  || strcmp(opername, "abs") == 0
					  || strcmp(opername, "btrim") == 0
					  || strcmp(opername, "length") == 0
					  || strcmp(opername, "ltrim") == 0
					  || strcmp(opername, "replace") == 0
					  || strcmp(opername, "round") == 0
					  || strcmp(opername, "rtrim") == 0
					  || strcmp(opername, "substr") == 0))
				{
					return false;
				}

				if (!multicorn_foreign_expr_walker((Node *) func->args,
												glob_cxt, &inner_cxt))
					return false;


				/*
				 * If function's input collation is not derived from a foreign
				 * Var, it can't be sent to remote.
				 */
				if (func->inputcollid == InvalidOid)
					 /* OK, inputs are all noncollatable */ ;
				else if (inner_cxt.state != FDW_COLLATE_SAFE ||
						 func->inputcollid != inner_cxt.collation)
					return false;

				/*
				 * Detect whether node is introducing a collation not derived
				 * from a foreign Var.  (If so, we just mark it unsafe for now
				 * rather than immediately returning false, since the parent
				 * node might not care.)
				 */
				collation = func->funccollid;
				if (collation == InvalidOid)
					state = FDW_COLLATE_NONE;
				else if (inner_cxt.state == FDW_COLLATE_SAFE &&
						 collation == inner_cxt.collation)
					state = FDW_COLLATE_SAFE;
				else if (collation == DEFAULT_COLLATION_OID)
					state = FDW_COLLATE_NONE;
				else
					state = FDW_COLLATE_UNSAFE;
			}
			break;
		case T_OpExpr:
		case T_DistinctExpr:	/* struct-equivalent to OpExpr */
			{
				OpExpr	   *oe = (OpExpr *) node;
				const char *operatorName = get_opname(oe->opno);

				/*
				 * Join-pushdown allows only a few operators to be pushed down.
                 * TODO: forward this decision into Python
				 */
				if (glob_cxt->is_remote_cond &&
					(!(strcmp(operatorName, "<") == 0 ||
					   strcmp(operatorName, ">") == 0 ||
					   strcmp(operatorName, "<=") == 0 ||
					   strcmp(operatorName, ">=") == 0 ||
					   strcmp(operatorName, "<>") == 0 ||
					   strcmp(operatorName, "=") == 0 ||
					   strcmp(operatorName, "+") == 0 ||
					   strcmp(operatorName, "-") == 0 ||
					   strcmp(operatorName, "*") == 0 ||
					   strcmp(operatorName, "%") == 0 ||
					   strcmp(operatorName, "/") == 0)))
					return false;

				/*
				 * Similarly, only built-in operators can be sent to remote.
				 * (If the operator is, surely its underlying function is
				 * too.)
				 */
				if (!multicorn_is_builtin(oe->opno))
					return false;

				/*
				 * Recurse to input subexpressions.
				 */
				if (!multicorn_foreign_expr_walker((Node *) oe->args,
										           glob_cxt, &inner_cxt))
					return false;

				/*
				 * If operator's input collation is not derived from a foreign
				 * Var, it can't be sent to remote.
				 */
				if (oe->inputcollid == InvalidOid)
					 /* OK, inputs are all noncollatable */ ;
				else if (inner_cxt.state != FDW_COLLATE_SAFE ||
						 oe->inputcollid != inner_cxt.collation)
					return false;

				/* Result-collation handling is same as for functions */
				collation = oe->opcollid;
				if (collation == InvalidOid)
					state = FDW_COLLATE_NONE;
				else if (inner_cxt.state == FDW_COLLATE_SAFE &&
						 collation == inner_cxt.collation)
					state = FDW_COLLATE_SAFE;
				else
					state = FDW_COLLATE_UNSAFE;
			}
			break;
		case T_NullIfExpr:
			{
				char	   *cur_opname = NULL;
				OpExpr	   *oe = (OpExpr *) node;

				/*
				 * Similarly, only built-in operators can be sent to remote.
				 * (If the operator is, surely its underlying function is
				 * too.)
				 */
				if (!multicorn_is_builtin(oe->opno))
					return false;

				tuple = SearchSysCache1(OPEROID, ObjectIdGetDatum(oe->opno));
				if (!HeapTupleIsValid(tuple))
					elog(ERROR, "cache lookup failed for operator %u", oe->opno);
				form = (Form_pg_operator) GETSTRUCT(tuple);

				/* opname is not a SQL identifier, so we should not quote it. */
				cur_opname = pstrdup(NameStr(form->oprname));
				ReleaseSysCache(tuple);

				/* TODO: forward this decision into Python */
				if (strcmp(cur_opname, "!") == 0
					|| strcmp(cur_opname, "^") == 0)
				{
					return false;
				}

				/* TODO: forward this decision into Python */
				if (strcmp(cur_opname, "~~*") == 0 || strcmp(cur_opname, "!~~*") == 0)
				{
					return false;
				}

				/*
				 * Recurse to input subexpressions.
				 */
				if (!multicorn_foreign_expr_walker((Node *) oe->args,
												   glob_cxt, &inner_cxt))
					return false;

				/*
				 * If operator's input collation is not derived from a foreign
				 * Var, it can't be sent to remote.
				 */
				if (oe->inputcollid == InvalidOid)
					 /* OK, inputs are all noncollatable */ ;
				else if (inner_cxt.state != FDW_COLLATE_SAFE ||
						 oe->inputcollid != inner_cxt.collation)
					return false;

				/* Result-collation handling is same as for functions */
				collation = oe->opcollid;
				if (collation == InvalidOid)
					state = FDW_COLLATE_NONE;
				else if (inner_cxt.state == FDW_COLLATE_SAFE &&
						 collation == inner_cxt.collation)
					state = FDW_COLLATE_SAFE;
				else
					state = FDW_COLLATE_UNSAFE;
			}
			break;
		case T_ScalarArrayOpExpr:
			{
				ScalarArrayOpExpr *oe = (ScalarArrayOpExpr *) node;

                /* Should not be in the join clauses of the Join-pushdown */
                /* TODO: not sure about this */
				if (glob_cxt->is_remote_cond)
					return false;

				/*
				 * Again, only built-in operators can be sent to remote.
				 */
				if (!multicorn_is_builtin(oe->opno))
					return false;

				/*
				 * Recurse to input subexpressions.
				 */
				if (!multicorn_foreign_expr_walker((Node *) oe->args,
												   glob_cxt, &inner_cxt))
					return false;

				/*
				 * If operator's input collation is not derived from a foreign
				 * Var, it can't be sent to remote.
				 */
				if (oe->inputcollid == InvalidOid)
					 /* OK, inputs are all noncollatable */ ;
				else if (inner_cxt.state != FDW_COLLATE_SAFE ||
						 oe->inputcollid != inner_cxt.collation)
					return false;

				/* Output is always boolean and so noncollatable. */
				collation = InvalidOid;
				state = FDW_COLLATE_NONE;
			}
			break;
		case T_RelabelType:
			{
				RelabelType *r = (RelabelType *) node;

				/*
				 * Recurse to input subexpression.
				 */
				if (!multicorn_foreign_expr_walker((Node *) r->arg,
												   glob_cxt, &inner_cxt))
					return false;

				/*
				 * RelabelType must not introduce a collation not derived from
				 * an input foreign Var.
				 */
				collation = r->resultcollid;
				if (collation == InvalidOid)
					state = FDW_COLLATE_NONE;
				else if (inner_cxt.state == FDW_COLLATE_SAFE &&
						 collation == inner_cxt.collation)
					state = FDW_COLLATE_SAFE;
				else
					state = FDW_COLLATE_UNSAFE;
			}
			break;
		case T_BoolExpr:
			{
				BoolExpr   *b = (BoolExpr *) node;

				/*
				 * Recurse to input subexpressions.
				 */
				if (!multicorn_foreign_expr_walker((Node *) b->args,
												   glob_cxt, &inner_cxt))
					return false;

				/* Output is always boolean and so noncollatable. */
				collation = InvalidOid;
				state = FDW_COLLATE_NONE;
			}
			break;
		case T_NullTest:
			{
				NullTest   *nt = (NullTest *) node;

				/*
				 * Recurse to input subexpressions.
				 */
				if (!multicorn_foreign_expr_walker((Node *) nt->arg,
												   glob_cxt, &inner_cxt))
					return false;

				/* Output is always boolean and so noncollatable. */
				collation = InvalidOid;
				state = FDW_COLLATE_NONE;
			}
			break;
		case T_List:
			{
				List	   *l = (List *) node;
				ListCell   *lc;

				/*
				 * Recurse to component subexpressions.
				 */
				foreach(lc, l)
				{
					if (!multicorn_foreign_expr_walker((Node *) lfirst(lc),
													   glob_cxt, &inner_cxt))
						return false;
				}

				/*
				 * When processing a list, collation state just bubbles up
				 * from the list elements.
				 */
				collation = inner_cxt.collation;
				state = inner_cxt.state;

				/* Don't apply exprType() to the list. */
				check_type = false;
			}
			break;
		case T_CoalesceExpr:
			{
				CoalesceExpr *coalesce = (CoalesceExpr *) node;
				ListCell   *lc;

				if (list_length(coalesce->args) < 2)
					return false;

				/* Recurse to each argument */
				foreach(lc, coalesce->args)
				{
					if (!multicorn_foreign_expr_walker((Node *) lfirst(lc),
													   glob_cxt, &inner_cxt))
						return false;
				}
			}
			break;
		case T_CaseExpr:
			{
				ListCell   *lc;

				/* Recurse to condition subexpressions. */
				foreach(lc, ((CaseExpr *) node)->args)
				{
					if (!multicorn_foreign_expr_walker((Node *) lfirst(lc),
													   glob_cxt, &inner_cxt))
						return false;
				}
			}
			break;
		case T_CaseWhen:
			{
				CaseWhen   *whenExpr = (CaseWhen *) node;

				/* Recurse to condition expression. */
				if (!multicorn_foreign_expr_walker((Node *) whenExpr->expr,
												   glob_cxt, &inner_cxt))
					return false;
				/* Recurse to result expression. */
				if (!multicorn_foreign_expr_walker((Node *) whenExpr->result,
												   glob_cxt, &inner_cxt))
					return false;
				/* Don't apply exprType() to the case when expr. */
				check_type = false;
			}
			break;
		case T_Aggref:
			{
				Aggref	   *agg = (Aggref *) node;
				ListCell   *lc;
				char	   *opername = NULL;
				Oid			schema;

				/* get function name and schema */
				tuple = SearchSysCache1(PROCOID, ObjectIdGetDatum(agg->aggfnoid));
				if (!HeapTupleIsValid(tuple))
				{
					elog(ERROR, "cache lookup failed for function %u", agg->aggfnoid);
				}
				opername = pstrdup(((Form_pg_proc) GETSTRUCT(tuple))->proname.data);
				schema = ((Form_pg_proc) GETSTRUCT(tuple))->pronamespace;
				ReleaseSysCache(tuple);

				/* ignore functions in other than the pg_catalog schema */
				if (schema != PG_CATALOG_NAMESPACE)
					return false;

				/* TODO: this decision will need to be forwarded to Python */
				if (!(strcmp(opername, "sum") == 0
					  || strcmp(opername, "avg") == 0
					  || strcmp(opername, "max") == 0
					  || strcmp(opername, "min") == 0
					  || strcmp(opername, "count") == 0))
				{
					return false;
				}


				/* Not safe to pushdown when not in grouping context */
				if (!IS_UPPER_REL(glob_cxt->foreignrel))
					return false;

				/* Only non-split aggregates are pushable. */
				if (agg->aggsplit != AGGSPLIT_SIMPLE)
					return false;

				/*
				 * Recurse to input args. aggdirectargs, aggorder and
				 * aggdistinct are all present in args, so no need to check
				 * their shippability explicitly.
				 */
				foreach(lc, agg->args)
				{
					Node	   *n = (Node *) lfirst(lc);

					/* If TargetEntry, extract the expression from it */
					if (IsA(n, TargetEntry))
					{
						TargetEntry *tle = (TargetEntry *) n;

						n = (Node *) tle->expr;
					}

					if (!multicorn_foreign_expr_walker(n, glob_cxt, &inner_cxt))
						return false;
				}

				if (agg->aggorder || agg->aggfilter)
				{
					return false;
				}

				/*
				 * If aggregate's input collation is not derived from a
				 * foreign Var, it can't be sent to remote.
				 */
				if (agg->inputcollid == InvalidOid)
					 /* OK, inputs are all noncollatable */ ;
				else if (inner_cxt.state != FDW_COLLATE_SAFE ||
						 agg->inputcollid != inner_cxt.collation)
					return false;

				/*
				 * Detect whether node is introducing a collation not derived
				 * from a foreign Var.  (If so, we just mark it unsafe for now
				 * rather than immediately returning false, since the parent
				 * node might not care.)
				 */
				collation = agg->aggcollid;
				if (collation == InvalidOid)
					state = FDW_COLLATE_NONE;
				else if (inner_cxt.state == FDW_COLLATE_SAFE &&
						 collation == inner_cxt.collation)
					state = FDW_COLLATE_SAFE;
				else if (collation == DEFAULT_COLLATION_OID)
					state = FDW_COLLATE_NONE;
				else
					state = FDW_COLLATE_UNSAFE;
			}
			break;
		case T_ArrayExpr:
			{
				ArrayExpr  *a = (ArrayExpr *) node;

                /* Should not be in the join clauses of the Join-pushdown */
                /* TODO: not sure about this */
				if (glob_cxt->is_remote_cond)
					return false;

				/*
				 * Recurse to input subexpressions.
				 */
				if (!multicorn_foreign_expr_walker((Node *) a->elements,
												   glob_cxt, &inner_cxt))
					return false;

				/*
				 * ArrayExpr must not introduce a collation not derived from
				 * an input foreign Var (same logic as for a function).
				 */
				collation = a->array_collid;
				if (collation == InvalidOid)
					state = FDW_COLLATE_NONE;
				else if (inner_cxt.state == FDW_COLLATE_SAFE &&
						 collation == inner_cxt.collation)
					state = FDW_COLLATE_SAFE;
				else if (collation == DEFAULT_COLLATION_OID)
					state = FDW_COLLATE_NONE;
				else
					state = FDW_COLLATE_UNSAFE;
			}
			break;
        case T_RowExpr:			/* Allow pushdown RowExpr to support
								 * time-series functions */
		case T_FieldSelect:		/* Allow pushdown FieldSelect to support
								 * accessing value of record of time-series
								 * functions */
			{
				collation = InvalidOid;
				state = FDW_COLLATE_NONE;
				check_type = false;
			}
			break;
		default:

			/*
			 * If it's anything else, assume it's unsafe.  This list can be
			 * expanded later, but don't forget to add deparse support below.
			 */
			return false;
	}

	/*
	 * If result type of given expression is not built-in, it can't be sent to
	 * remote because it might have incompatible semantics on remote side.
	 */
	if (check_type && !multicorn_is_builtin(exprType(node)))
		return false;

	/*
	 * Now, merge my collation information into my parent's state.
	 */
	if (state > outer_cxt->state)
	{
		/* Override previous parent state */
		outer_cxt->collation = collation;
		outer_cxt->state = state;
	}
	else if (state == outer_cxt->state)
	{
		/* Merge, or detect error if there's a collation conflict */
		switch (state)
		{
			case FDW_COLLATE_NONE:
				/* Nothing + nothing is still nothing */
				break;
			case FDW_COLLATE_SAFE:
				if (collation != outer_cxt->collation)
				{
					/*
					 * Non-default collation always beats default.
					 */
					if (outer_cxt->collation == DEFAULT_COLLATION_OID)
					{
						/* Override previous parent state */
						outer_cxt->collation = collation;
					}
					else if (collation != DEFAULT_COLLATION_OID)
					{
						/*
						 * Conflict; show state as indeterminate.  We don't
						 * want to "return false" right away, since parent
						 * node might not care about collation.
						 */
						outer_cxt->state = FDW_COLLATE_UNSAFE;
					}
				}
				break;
			case FDW_COLLATE_UNSAFE:
				/* We're still conflicted ... */
				break;
		}
	}
	/* It looks OK */
	return true;
}

/*
 * Returns true if given expr is safe to evaluate on the foreign server.
 */
bool
multicorn_is_foreign_expr(PlannerInfo *root,
					      RelOptInfo *baserel,
					      Expr *expr)
{
	foreign_glob_cxt glob_cxt;
	foreign_loc_cxt loc_cxt;
	MulticornFdwRelationInfo *fpinfo = (MulticornFdwRelationInfo *) (baserel->fdw_private);

	/*
	 * Check that the expression consists of nodes that are safe to execute
	 * remotely.
	 */
	glob_cxt.root = root;
	glob_cxt.foreignrel = baserel;

	/*
	 * For an upper relation, use relids from its underneath scan relation,
	 * because the upperrel's own relids currently aren't set to anything
	 * meaningful by the core code.  For other relation, use their own relids.
	 */
	if (IS_UPPER_REL(baserel))
		glob_cxt.relids = fpinfo->outerrel->relids;
	else
		glob_cxt.relids = baserel->relids;
	loc_cxt.collation = InvalidOid;
	loc_cxt.state = FDW_COLLATE_NONE;
	if (!multicorn_foreign_expr_walker((Node *) expr, &glob_cxt, &loc_cxt))
		return false;

	/*
	 * If the expression has a valid collation that does not arise from a
	 * foreign var, the expression can not be sent over.
	 */
	if (loc_cxt.state == FDW_COLLATE_UNSAFE)
		return false;

	/*
	 * An expression which includes any mutable functions can't be sent over
	 * because its result is not stable.  For example, sending now() remote
	 * side could cause confusion from clock offsets.  Future versions might
	 * be able to make this choice with more granularity. (We check this last
	 * because it requires a lot of expensive catalog lookups.)
	 */
	if (contain_mutable_functions((Node *) expr))
		return false;

	/* OK to evaluate on the remote server */
	return true;
}


/*
 * Returns true if given expr is something we'd have to send the value of
 * to the foreign server.
 *
 * This should return true when the expression is a shippable node that
 * deparseExpr would add to context->params_list.  Note that we don't care
 * if the expression *contains* such a node, only whether one appears at top
 * level.  We need this to detect cases where setrefs.c would recognize a
 * false match between an fdw_exprs item (which came from the params_list)
 * and an entry in fdw_scan_tlist (which we're considering putting the given
 * expression into).
 */
bool
multicorn_is_foreign_param(PlannerInfo *root,
						   RelOptInfo *baserel,
						   Expr *expr)
{
	if (expr == NULL)
		return false;

	switch (nodeTag(expr))
	{
		case T_Var:
			{
				/* It would have to be sent unless it's a foreign Var */
				Var		   *var = (Var *) expr;
				MulticornFdwRelationInfo *fpinfo = (MulticornFdwRelationInfo *) (baserel->fdw_private);
				Relids		relids;

				if (IS_UPPER_REL(baserel))
					relids = fpinfo->outerrel->relids;
				else
					relids = baserel->relids;

				if (bms_is_member(var->varno, relids) && var->varlevelsup == 0)
					return false;	/* foreign Var, so not a param */
				else
					return true;	/* it'd have to be a param */
				break;
			}
		case T_Param:
			/* Params always have to be sent to the foreign server */
			return true;
		default:
			break;
	}
	return false;
}