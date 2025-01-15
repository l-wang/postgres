/*-------------------------------------------------------------------------
 *
 * parse_expr.h
 *	  handle expressions in parser
 *
 * Portions Copyright (c) 1996-2025, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/include/parser/parse_expr.h
 *
 *-------------------------------------------------------------------------
 */
#ifndef PARSE_EXPR_H
#define PARSE_EXPR_H

#include "parser/parse_node.h"

/* GUC parameters */
extern PGDLLIMPORT bool Transform_null_equals;
extern PGDLLIMPORT bool compat_field_notation;

extern Node *transformExpr(ParseState *pstate, Node *expr, ParseExprKind exprKind);

extern const char *ParseExprKindName(ParseExprKind exprKind);

extern Node *transformIndirection(ParseState *pstate, A_Indirection *ind,
								  bool *trailing_star_expansion);

#endif							/* PARSE_EXPR_H */
