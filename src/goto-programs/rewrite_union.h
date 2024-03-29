/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#ifndef CPROVER_GOTO_PROGRAMS_REWRITE_UNION_H
#define CPROVER_GOTO_PROGRAMS_REWRITE_UNION_H

#include <goto-programs/goto_functions.h>

class exprt;
class goto_modelt;

void rewrite_union(exprt &);
void rewrite_union(goto_functionst::goto_functiont &);
void rewrite_union(goto_functionst &);
void rewrite_union(goto_modelt &);

void restore_union(exprt &, const namespacet &);

#endif // CPROVER_GOTO_PROGRAMS_REWRITE_UNION_H
