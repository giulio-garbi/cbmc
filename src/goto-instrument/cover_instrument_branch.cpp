/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Coverage Instrumentation for Branches

#include "cover_basic_blocks.h"
#include "cover_filter.h"
#include "cover_instrument.h"

void cover_branch_instrumentert::instrument(
  const irep_idt &function_id,
  goto_programt &goto_program,
  goto_programt::targett &i_it,
  const cover_blocks_baset &basic_blocks,
  const assertion_factoryt &make_assertion) const
{
  if(is_non_cover_assertion(i_it))
    i_it->turn_into_skip();

  const bool is_function_entry_point =
    i_it == goto_program.instructions.begin();
  const bool is_conditional_goto =
    i_it->is_goto() && !i_it->condition().is_true();
  if(!is_function_entry_point && !is_conditional_goto)
    return;

  if(!goal_filters(i_it->source_location()))
    return;

  if(is_function_entry_point)
  {
    // we want branch coverage to imply 'entry point of function'
    // coverage
    std::string comment = "entry point";

    source_locationt source_location = i_it->source_location();
    initialize_source_location(source_location, comment, function_id);
    goto_program.insert_before(
      i_it, make_assertion(false_exprt(), source_location));
  }

  if(is_conditional_goto)
  {
    std::string b =
      std::to_string(basic_blocks.block_of(i_it) + 1); // start with 1
    std::string true_comment = "block " + b + " branch true";
    std::string false_comment = "block " + b + " branch false";

    exprt guard = i_it->condition();
    source_locationt source_location = i_it->source_location();

    goto_program.insert_before_swap(i_it);
    initialize_source_location(source_location, true_comment, function_id);
    *i_it = make_assertion(not_exprt(guard), source_location);

    goto_program.insert_before_swap(i_it);
    initialize_source_location(source_location, false_comment, function_id);
    *i_it = make_assertion(guard, source_location);

    std::advance(i_it, 2);
  }
}
