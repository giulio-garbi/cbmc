/*******************************************************************\

Module: Function Inlining

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Function Inlining

#include "goto_inline.h"

#include <util/std_expr.h>

#include "goto_inline_class.h"
#include "goto_model.h"

/// Inline every function call into the entry_point() function.
/// Then delete the bodies of all of the other functions.
/// This is pretty drastic and can result in a very large program.
/// Caller is responsible for calling update(), compute_loop_numbers(), etc.
/// \param goto_model: Source of the symbol table and function map to use.
/// \param message_handler: Message handler used by goto_inlinet.
/// \param adjust_function: Replace location in inlined function with call site.
void goto_inline(
  goto_modelt &goto_model,
  message_handlert &message_handler,
  bool adjust_function)
{
  const namespacet ns(goto_model.symbol_table);
  goto_inline(
    goto_model.goto_functions,
    ns,
    message_handler,
    adjust_function);
}

/// Inline every function call into the entry_point() function.
/// Then delete the bodies of all of the other functions.
/// This is pretty drastic and can result in a very large program.
/// Caller is responsible for calling update(), compute_loop_numbers(), etc.
/// \param goto_functions: The function map to use.
/// \param ns : The namespace to use.
/// \param message_handler: Message handler used by goto_inlinet.
/// \param adjust_function: Replace location in inlined function with call site.
void goto_inline(
  goto_functionst &goto_functions,
  const namespacet &ns,
  message_handlert &message_handler,
  bool adjust_function)
{
  goto_inlinet goto_inline(
    goto_functions,
    ns,
    message_handler,
    adjust_function);

  typedef goto_functionst::goto_functiont goto_functiont;

  // find entry point
  goto_functionst::function_mapt::iterator it=
    goto_functions.function_map.find(goto_functionst::entry_point());

  if(it==goto_functions.function_map.end())
    return;

  goto_functiont &entry_function = it->second;
  DATA_INVARIANT(
    entry_function.body_available(),
    "body of entry point function must be available");

  // gather all calls
  // we use non-transitive inlining to avoid the goto program
  // copying that goto_inlinet would do otherwise
  goto_inlinet::inline_mapt inline_map;

  for(auto &gf_entry : goto_functions.function_map)
  {
    goto_functiont &goto_function = gf_entry.second;

    if(!goto_function.body_available())
      continue;

    goto_inlinet::call_listt &call_list = inline_map[gf_entry.first];

    goto_programt &goto_program=goto_function.body;

    Forall_goto_program_instructions(i_it, goto_program)
    {
      if(!i_it->is_function_call())
        continue;

      call_list.push_back(goto_inlinet::callt(i_it, false));
    }
  }

  goto_inline.goto_inline(
    goto_functionst::entry_point(), entry_function, inline_map, true);

  // clean up
  for(auto &gf_entry : goto_functions.function_map)
  {
    if(gf_entry.first != goto_functionst::entry_point())
    {
      goto_functiont &goto_function = gf_entry.second;
      goto_function.body.clear();
    }
  }
}

/// Inline all function calls to functions either marked as "inlined" or
/// smaller than smallfunc_limit (by instruction count).
/// Unlike the goto_inline functions, this doesn't remove function
/// bodies after inlining.
/// Caller is responsible for calling update(), compute_loop_numbers(), etc.
/// \param goto_model: Source of the symbol table and function map to use.
/// \param message_handler: Message handler used by goto_inlinet.
/// \param smallfunc_limit: The maximum number of instructions in functions to
///   be inlined.
/// \param adjust_function: Replace location in inlined function with call site.
void goto_partial_inline(
  goto_modelt &goto_model,
  message_handlert &message_handler,
  unsigned smallfunc_limit,
  bool adjust_function)
{
  const namespacet ns(goto_model.symbol_table);
  goto_partial_inline(
    goto_model.goto_functions,
    ns,
    message_handler,
    smallfunc_limit,
    adjust_function);
}

/// Inline all function calls to functions either marked as "inlined" or
/// smaller than smallfunc_limit (by instruction count).
/// Unlike the goto_inline functions, this doesn't remove function
/// bodies after inlining.
/// Caller is responsible for calling update(), compute_loop_numbers(), etc.
/// \param goto_functions: The function map to use to find functions containing
///   calls and function bodies.
/// \param ns: Namespace used by goto_inlinet.
/// \param message_handler: Message handler used by goto_inlinet.
/// \param smallfunc_limit: The maximum number of instructions in functions to
///   be inlined.
/// \param adjust_function: Replace location in inlined function with call site.
void goto_partial_inline(
  goto_functionst &goto_functions,
  const namespacet &ns,
  message_handlert &message_handler,
  unsigned smallfunc_limit,
  bool adjust_function)
{
  goto_inlinet goto_inline(
    goto_functions,
    ns,
    message_handler,
    adjust_function);

  typedef goto_functionst::goto_functiont goto_functiont;

  // gather all calls
  goto_inlinet::inline_mapt inline_map;

  for(auto &gf_entry : goto_functions.function_map)
  {
    goto_functiont &goto_function = gf_entry.second;

    if(!goto_function.body_available())
      continue;

    if(gf_entry.first == goto_functions.entry_point())
    {
      // Don't inline any function calls made from the _start function.
      // This is so that the convention of __CPROVER_start
      // calling __CPROVER_initialize is maintained, so these can be
      // augmented / replaced by later passes.
      continue;
    }

    goto_programt &goto_program=goto_function.body;

    goto_inlinet::call_listt &call_list = inline_map[gf_entry.first];

    Forall_goto_program_instructions(i_it, goto_program)
    {
      if(!i_it->is_function_call())
        continue;

      exprt lhs;
      exprt function_expr;
      exprt::operandst arguments;
      goto_inlinet::get_call(i_it, lhs, function_expr, arguments);

      if(function_expr.id()!=ID_symbol)
        // Can't handle pointers to functions
        continue;

      const symbol_exprt &symbol_expr=to_symbol_expr(function_expr);
      const irep_idt id=symbol_expr.get_identifier();

      goto_functionst::function_mapt::const_iterator called_it =
        goto_functions.function_map.find(id);

      if(called_it == goto_functions.function_map.end())
        // Function not loaded, can't check size
        continue;

      // called function
      const goto_functiont &called_function = called_it->second;

      if(!called_function.body_available())
        // The bodies of functions that don't have bodies can't be inlined.
        continue;

      if(
        to_code_type(ns.lookup(id).type).get_inlined() ||
        called_function.body.instructions.size() <= smallfunc_limit)
      {
        PRECONDITION(i_it->is_function_call());

        call_list.push_back(goto_inlinet::callt(i_it, false));
      }
    }
  }

  goto_inline.goto_inline(inline_map, false);
}

/// Transitively inline all function calls made from a particular function.
/// Caller is responsible for calling update(), compute_loop_numbers(), etc.
/// \param goto_model: Source of the symbol table and function map to use.
/// \param function: The function whose calls to inline.
/// \param message_handler: Message handler used by goto_inlinet.
/// \param adjust_function: Replace location in inlined function with call site.
/// \param caching: Tell goto_inlinet to cache.
void goto_function_inline(
  goto_modelt &goto_model,
  const irep_idt function,
  message_handlert &message_handler,
  bool adjust_function,
  bool caching)
{
  const namespacet ns(goto_model.symbol_table);
  goto_function_inline(
    goto_model.goto_functions,
    function,
    ns,
    message_handler,
    adjust_function,
    caching);
}

/// Transitively inline all function calls made from a particular function.
/// Caller is responsible for calling update(), compute_loop_numbers(), etc.
/// \param goto_functions: The function map to use to find function bodies.
/// \param function: The function whose calls to inline.
/// \param ns: Namespace used by goto_inlinet.
/// \param message_handler: Message handler used by goto_inlinet.
/// \param adjust_function: Replace location in inlined function with call site.
/// \param caching: Tell goto_inlinet to cache.
void goto_function_inline(
  goto_functionst &goto_functions,
  const irep_idt function,
  const namespacet &ns,
  message_handlert &message_handler,
  bool adjust_function,
  bool caching)
{
  goto_inlinet goto_inline(
    goto_functions,
    ns,
    message_handler,
    adjust_function,
    caching);

  goto_functionst::function_mapt::iterator f_it=
    goto_functions.function_map.find(function);

  if(f_it==goto_functions.function_map.end())
    return;

  goto_functionst::goto_functiont &goto_function=f_it->second;

  if(!goto_function.body_available())
    return;

  // gather all calls
  goto_inlinet::inline_mapt inline_map;

  goto_inlinet::call_listt &call_list=inline_map[f_it->first];

  goto_programt &goto_program=goto_function.body;

  Forall_goto_program_instructions(i_it, goto_program)
  {
    if(!i_it->is_function_call())
      continue;

    call_list.push_back(goto_inlinet::callt(i_it, true));
  }

  goto_inline.goto_inline(function, goto_function, inline_map, true);
}

jsont goto_function_inline_and_log(
  goto_modelt &goto_model,
  const irep_idt function,
  message_handlert &message_handler,
  bool adjust_function,
  bool caching)
{
  const namespacet ns(goto_model.symbol_table);

  goto_inlinet goto_inline(
    goto_model.goto_functions,
    ns,
    message_handler,
    adjust_function,
    caching);

  goto_functionst::function_mapt::iterator f_it=
    goto_model.goto_functions.function_map.find(function);

  if(f_it==goto_model.goto_functions.function_map.end())
    return jsont();

  goto_functionst::goto_functiont &goto_function=f_it->second;

  if(!goto_function.body_available())
    return jsont();

  // gather all calls
  goto_inlinet::inline_mapt inline_map;

  // create empty call list
  goto_inlinet::call_listt &call_list=inline_map[f_it->first];

  goto_programt &goto_program=goto_function.body;

  Forall_goto_program_instructions(i_it, goto_program)
  {
    if(!i_it->is_function_call())
      continue;

    call_list.push_back(goto_inlinet::callt(i_it, true));
  }

  goto_inline.goto_inline(function, goto_function, inline_map, true);
  goto_model.goto_functions.update();
  goto_model.goto_functions.compute_loop_numbers();

  return goto_inline.output_inline_log_json();
}

/// Transitively inline all function calls found in a particular program.
/// Caller is responsible for calling update(), compute_loop_numbers(), etc.
/// \param goto_functions: The function map to use to find function bodies.
/// \param goto_program: The program whose calls to inline.
/// \param ns: Namespace used by goto_inlinet.
/// \param message_handler: Message handler used by goto_inlinet.
/// \param adjust_function: Replace location in inlined function with call site.
/// \param caching: Tell goto_inlinet to cache.
void goto_program_inline(
  goto_functionst &goto_functions,
  goto_programt &goto_program,
  const namespacet &ns,
  message_handlert &message_handler,
  bool adjust_function,
  bool caching)
{
  goto_inlinet goto_inline(
    goto_functions, ns, message_handler, adjust_function, caching);

  // gather all calls found in the program
  goto_inlinet::call_listt call_list;

  Forall_goto_program_instructions(i_it, goto_program)
  {
    if(!i_it->is_function_call())
      continue;

    call_list.push_back(goto_inlinet::callt(i_it, true));
  }

  goto_inline.goto_inline(call_list, goto_program, true);
}
