/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Coverage Instrumentation for Decisions

#include "cover_instrument.h"

#include <langapi/language_util.h>

#include "cover_util.h"

void cover_decision_instrumentert::instrument(
  const irep_idt &function_id,
  goto_programt &goto_program,
  goto_programt::targett &i_it,
  const cover_blocks_baset &,
  const assertion_factoryt &make_assertion) const
{
  if(is_non_cover_assertion(i_it))
    i_it->turn_into_skip();

  // Decisions are maximal Boolean combinations of conditions.
  if(!i_it->source_location().is_built_in())
  {
    const std::set<exprt> decisions = collect_decisions(i_it);

    source_locationt source_location = i_it->source_location();

    for(const auto &d : decisions)
    {
      const std::string d_string = from_expr(ns, function_id, d);

      const std::string comment_t = "decision '" + d_string + "' true";
      goto_program.insert_before_swap(i_it);
      initialize_source_location(source_location, comment_t, function_id);
      *i_it = make_assertion(d, source_location);

      const std::string comment_f = "decision '" + d_string + "' false";
      goto_program.insert_before_swap(i_it);
      initialize_source_location(source_location, comment_f, function_id);
      *i_it = make_assertion(not_exprt(d), source_location);
    }

    // advance iterator beyond the inserted instructions
    for(std::size_t i = 0; i < decisions.size() * 2; i++)
      i_it++;
  }
}
