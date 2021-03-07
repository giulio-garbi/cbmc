/*******************************************************************\

Module: Symex Shadow Memory Instrumentation

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Symex Shadow Memory Instrumentation

#include "goto_symex.h"

#include "symex_shadow_memory_util.h"

#include <util/arith_tools.h>
#include <util/base_type.h>
#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/expr_initializer.h>
#include <util/find_symbols.h>
#include <util/fresh_symbol.h>
#include <util/invariant.h>
#include <util/message.h>
#include <util/pointer_offset_size.h>
#include <util/pointer_predicates.h>
#include <util/pointer_resolve.h>
#include <util/prefix.h>
#include <util/replace_expr.h>
#include <util/source_location.h>
#include <util/std_expr.h>
#include <util/string_constant.h>

#include <langapi/language_util.h>

#include <goto-programs/goto_model.h>
#include <pointer-analysis/value_set_dereference.h>


void goto_symext::initialize_shadow_memory(
  goto_symex_statet &state,
  const exprt &expr,
  std::map<irep_idt, typet> &fields)
{
  typet type = ns.follow(expr.type());
  for(const auto &field_pair : fields)
  {
    exprt address_expr = expr;
    if(type.id() == ID_array && expr.id() == ID_symbol && !type.get_bool(ID_C_dynamic))
    {
      address_expr.type() = remove_array_type_l2(address_expr.type());
      exprt original_expr = to_ssa_expr(expr).get_original_expr();
      original_expr.type() = remove_array_type_l2(original_expr.type());
      to_ssa_expr(address_expr).set_expression(original_expr);
    }
    if(address_expr.id() == ID_dereference)
    {
      address_expr = to_dereference_expr(address_expr).pointer();
    }
    else
    {
      address_expr = address_of_exprt(address_expr);
    }

    symbol_exprt field = add_field(
      state,
      address_expr,
      field_pair.first,
      type);

    const auto zero_value =
        zero_initializer(type, expr.source_location(), ns);
    CHECK_RETURN(zero_value.has_value());

    symex_assign(state, field, *zero_value);

    log.conditional_output(
      log.debug(),
      [field, this, address_expr](messaget::mstreamt &mstream) {
        mstream << "initialize field " << id2string(field.get_identifier())
                << " for " << from_expr(ns, "", address_expr)
                << messaget::eom;
      });
  }
}

symbol_exprt goto_symext::add_field(
  goto_symex_statet &state,
  const exprt &expr,
  const irep_idt &field_name,
  const typet &field_type)
{
  auto &addresses = state.address_fields[field_name];
  symbolt &new_symbol = get_fresh_aux_symbol(
    field_type,
    id2string(state.source.function_id),
    "SM__" + from_expr(ns, "", expr) + "__" + id2string(field_name),
    state.source.pc->source_location,
    ID_C,
    state.symbol_table);

  addresses.push_back(goto_symex_statet::shadowed_addresst{
    expr, new_symbol.symbol_expr()});
  return new_symbol.symbol_expr();
}

/// returns true if we attempt to set/get a field on a NULL pointer
static bool set_field_check_null(
  const namespacet &ns,
  const messaget &log,
  const std::vector<exprt> &value_set,
  const exprt &expr)
{
  const null_pointer_exprt null_pointer(to_pointer_type(expr.type()));
  if(value_set.size() == 1 && filter_by_value_set(value_set, null_pointer))
  {
    log.conditional_output(
      log.debug(), [ns, null_pointer, expr](messaget::mstreamt &mstream) {
        mstream << "value set match: " << from_expr(ns, "", null_pointer)
                << " <-- " << from_expr(ns, "", expr) << messaget::eom;
        mstream << "ignoring set field on NULL object" << messaget::eom;
      });
    return true;
  }
  return false;
}

static value_set_dereferencet::valuet get_shadow(
  const exprt &shadow,
  const object_descriptor_exprt &matched_base_descriptor,
  const exprt &expr,
  const namespacet &ns,
  const messaget &log)
{
  object_descriptor_exprt shadowed_object = matched_base_descriptor;
  shadowed_object.object() = shadow;
  value_set_dereferencet::valuet shadow_dereference =
      value_set_dereferencet::build_reference_to(shadowed_object, expr, ns);
  //log.debug() << "  shadow-deref: " << from_expr(ns, "", shadow_dereference.value) << messaget::eom;
  return shadow_dereference;
}

static exprt get_cond(
  const exprt &shadowed_address,
  const exprt &dereference_pointer,
  const exprt &matched_base,
  const exprt &expr,
  const namespacet &ns,
  const messaget &log)
{
  exprt cond = simplify_expr(
      and_exprt(
          equal_exprt(
              expr,
              typecast_exprt::conditional_cast(dereference_pointer, expr.type())),
          equal_exprt(
              shadowed_address,
              typecast_exprt::conditional_cast(
                  matched_base, shadowed_address.type()))),
      ns);
  log_cond(ns, log, cond);

  return cond;
}

static optionalt<exprt> set_field(
  const namespacet &ns,
  const messaget &log,
  const std::vector<exprt>  &value_set,
  const goto_symex_statet::shadowed_addresst &shadowed_address,
  const typet &field_type,
  const exprt &expr,
  exprt lhs,
  size_t &mux_size)
{
  bool found = false;
  for(const auto &matched_object : value_set)
  {
    if(matched_object.id() != ID_object_descriptor)
    {
      log.debug() << "VALUE SET CONTAINS UNKNOWN" << messaget::eom;
      continue;
    }

    value_set_dereferencet::valuet dereference =
        value_set_dereferencet::build_reference_to(matched_object, expr, ns);

    const object_descriptor_exprt &matched_base_descriptor =
        to_object_descriptor_expr(matched_object);
    const exprt &matched_base = address_of_exprt(matched_base_descriptor.object());

    // NULL has already been handled in the caller; skip.
    if(matched_base.id() == ID_address_of &&
        to_address_of_expr(matched_base).object().id() == ID_null_object)
    {
      continue;
    }
    const value_set_dereferencet::valuet shadow_dereference =
        get_shadow(shadowed_address.shadow, matched_base_descriptor, expr, ns, log);
    log_value_set_match(
        ns, log, shadowed_address, matched_base, dereference, expr, shadow_dereference);

    const exprt cond = get_cond(
        shadowed_address.address, dereference.pointer, matched_base, expr, ns, log);
    if(cond.is_true())
    {
      return shadow_dereference.pointer;
    }
    else if(!cond.is_false())
    {
      mux_size++;
      found = true;
      if(lhs.is_nil())
        lhs = shadow_dereference.pointer;
      else
        lhs = if_exprt(cond, shadow_dereference.pointer, lhs);
    }
  }
  if(found)
  {
    return lhs;
  }
  return {};
}

static optionalt<exprt> get_field(
  const namespacet &ns,
  const messaget &log,
  const std::vector<exprt>  &value_set,
  const goto_symex_statet::shadowed_addresst &shadowed_address,
  const typet &field_type,
  const exprt &expr,
  exprt rhs,
  const typet &lhs_type,
  size_t &mux_size)
{
  bool found = false;
  for(const auto &matched_object : value_set)
  {
    if(matched_object.id() != ID_object_descriptor)
    {
      log.debug() << "VALUE SET CONTAINS UNKNOWN" << messaget::eom;
      continue;
    }
    const object_descriptor_exprt &matched_base_descriptor =
        to_object_descriptor_expr(matched_object);
    const exprt &matched_base = address_of_exprt(matched_base_descriptor.object());

    // NULL has already been handled in the caller; skip.
    if(matched_base.id() == ID_address_of &&
       to_address_of_expr(matched_base).object().id() == ID_null_object)
    {
      continue;
    }

    value_set_dereferencet::valuet dereference =
      value_set_dereferencet::build_reference_to(matched_object, expr, ns);

    const value_set_dereferencet::valuet shadow_dereference =
        get_shadow(shadowed_address.shadow, matched_base_descriptor, expr, ns, log);
    log_value_set_match(
      ns, log, shadowed_address, matched_base, dereference, expr, shadow_dereference);

    const exprt cond = get_cond(
        shadowed_address.address, dereference.pointer, matched_base, expr, ns, log);
    if(cond.is_true())
    {
      return shadow_dereference.value;
    }
    else if(!cond.is_false())
    {
      mux_size++;
      found = true;
      if(rhs.is_nil())
      {
        rhs = if_exprt(
          cond,
          typecast_exprt::conditional_cast(shadow_dereference.value, lhs_type),
          from_integer(-1, lhs_type));
      }
      else
      {
        rhs = if_exprt(
          cond,
          typecast_exprt::conditional_cast(shadow_dereference.value, lhs_type),
          rhs);
      }
    }
  }
  if (found)
  {
    return rhs;
  }
  return {};
}

// returns an expr if shadowed_address corresponds to resolved_expr
static optionalt<exprt> exact_match(
  const namespacet &ns,
  const messaget &log,
  const goto_symex_statet::shadowed_addresst &shadowed_address,
  const exprt &resolved_expr)
{
  log.debug() << "checking exact match "
              << from_expr(ns, "", shadowed_address.address)
              << " =?= "
              << from_expr(ns, "", resolved_expr)
              << messaget::eom;
  if(shadowed_address.address == resolved_expr)
  {
    log.debug() << "syntactic match" << messaget::eom;
    log_exact_match(ns, log, shadowed_address, resolved_expr);
    return address_of_exprt(shadowed_address.shadow);
  }

  if(
    shadowed_address.address.type().id() == ID_array &&
    resolved_expr.id() == ID_address_of &&
    to_address_of_expr(resolved_expr).object().id() == ID_index)
  {
    log.debug() << "resolved expression is array with index" << messaget::eom;
    const index_exprt &index =
      to_index_expr(to_address_of_expr(resolved_expr).object());
    if(shadowed_address.address == index.array())
    {
      log.debug() << "syntactic array match" << messaget::eom;
      log_exact_match(ns, log, shadowed_address, resolved_expr);
      return
        address_of_exprt(index_exprt(shadowed_address.shadow, index.index()));
    }
  }
  return {};
}

void goto_symext::symex_set_field(
  goto_symex_statet &state,
  const code_function_callt &code_function_call)
{
  // parse set_field call
  INVARIANT(
    code_function_call.arguments().size() == 3,
    CPROVER_PREFIX "set_field requires 3 arguments");
  irep_idt field_name = get_field_name(code_function_call.arguments()[1]);

  exprt expr = code_function_call.arguments()[0];
  typet expr_type = expr.type();
  DATA_INVARIANT(
    expr.type().id() == ID_pointer,
    "shadow memory requires a pointer expression");

  exprt value = code_function_call.arguments()[2];
  log_set_field(ns, log, field_name, expr, value);
  INVARIANT(
    state.address_fields.count(field_name) == 1,
    id2string(field_name) + " should exist");
  const auto &addresses = state.address_fields.at(field_name);
  const typet &field_type = get_field_type(field_name, state);

  // get value set
  std::vector<exprt> value_set = state.value_set.get_value_set(expr, ns);
  log_value_set(ns, log, value_set);
  if(set_field_check_null(ns, log, value_set, expr))
  {
    return;
  }

  // build lhs
  const exprt &rhs = value;
  exprt lhs = nil_exprt();
  size_t mux_size = 0;
  for(const auto &shadowed_address : addresses)
  {
    log_try_shadow_address(ns, log, shadowed_address);

    auto maybe_lhs = set_field(
      ns, log, value_set, shadowed_address, field_type, expr, lhs, mux_size);
    if(maybe_lhs)
    {
      lhs = *maybe_lhs;
      if(lhs.id() == ID_symbol)
        break;
    }
  }

  // add to equation
  if(lhs.is_not_nil())
  {
    log.debug() << "mux size set_field: " << mux_size << messaget::eom;
    lhs = deref_expr(lhs);
    log.debug() << "LHS: " << from_expr(ns, "", lhs) << messaget::eom;
    symex_assign(
      state, lhs, typecast_exprt::conditional_cast(rhs, lhs.type()));
  }
  else
  {
    log.warning() << "cannot set_field for " << from_expr(ns, "", expr)
                  << messaget::eom;
  }
}

void goto_symext::symex_get_field(
  goto_symex_statet &state,
  const code_function_callt &code_function_call)
{
  INVARIANT(
    code_function_call.arguments().size() == 2,
    CPROVER_PREFIX "get_field requires 2 arguments");
  irep_idt field_name = get_field_name(code_function_call.arguments()[1]);

  exprt expr = code_function_call.arguments()[0];
  typet expr_type = expr.type();
  DATA_INVARIANT(
    expr_type.id() == ID_pointer,
    "shadow memory requires a pointer expression");
  log_get_field(ns, log, field_name, expr);

  INVARIANT(
    state.address_fields.count(field_name) == 1,
    id2string(field_name) + " should exist");
  const auto &addresses = state.address_fields.at(field_name);
  // Should actually be fields.at(field_name)
  symbol_exprt lhs(CPROVER_PREFIX "get_field#return_value", signedbv_typet(32));
  const typet &field_type = get_field_type(field_name, state);

  std::vector<exprt> value_set = state.value_set.get_value_set(expr, ns);
  log_value_set(ns, log, value_set);

  exprt rhs = nil_exprt();
  size_t mux_size = 0;
  const null_pointer_exprt null_pointer(to_pointer_type(expr.type()));
  if(filter_by_value_set(value_set, null_pointer))
  {
    log_value_set_match(ns, log, null_pointer, expr);
    rhs = if_exprt(
      equal_exprt(expr, null_pointer),
      from_integer(0, lhs.type()),
      from_integer(-1, lhs.type()));
    mux_size = 1;
  }

  for(const auto &shadow_address : addresses)
  {
    log_try_shadow_address(ns, log, shadow_address);

    auto maybe_rhs = get_field(
      ns, log, value_set, shadow_address, field_type, expr, rhs, lhs.type(), mux_size);
    if(maybe_rhs)
    {
      rhs = *maybe_rhs;
      if(rhs.id() == ID_symbol)
        break;
    }
  }

  if(rhs.is_not_nil())
  {
    log.debug() << "mux size get_field: " << mux_size << messaget::eom;
    log.debug() << "RHS: " << from_expr(ns, "", rhs) << messaget::eom;
    symex_assign(
      state, lhs, typecast_exprt::conditional_cast(rhs, lhs.type()));
  }
  else
  {
    log.warning() << "cannot get_field for " << from_expr(ns, "", expr)
                  << messaget::eom;
    symex_assign(state, lhs, from_integer(0, lhs.type()));
  }
}

void goto_symext::symex_field_static_init(
  goto_symex_statet &state,
  const ssa_exprt &expr)
{
  if(state.source.function_id != CPROVER_PREFIX "initialize")
    return;

  if(expr.get_original_expr().id() != ID_symbol)
    return;

  const irep_idt &identifier =
    to_symbol_expr(expr.get_original_expr()).get_identifier();
  if(has_prefix(id2string(identifier), CPROVER_PREFIX))
    return;

  const symbolt &symbol = ns.lookup(identifier);

  if(symbol.is_auxiliary || !symbol.is_static_lifetime)
    return;
  if(id2string(symbol.name).find("__cs_") != std::string::npos)
    return;

  const typet &type = symbol.type;
  log.debug() << "global memory " << id2string(identifier) << " of type "
              << from_type(ns, "", type) << messaget::eom;

  initialize_shadow_memory(state, expr, state.global_fields);
}

void goto_symext::symex_field_static_init_string_constant(
  goto_symex_statet &state,
  const ssa_exprt &expr,
  const exprt &rhs)
{
  const irep_idt &identifier =
    to_symbol_expr(expr.get_original_expr()).get_identifier();
  if(has_prefix(id2string(identifier), CPROVER_PREFIX))
    return;

  const index_exprt &index_expr =
    to_index_expr(to_address_of_expr(rhs).object());

  const typet &type = index_expr.array().type();
  log.debug() << "global memory "
              << id2string(to_string_constant(index_expr.array()).get_value())
              << " of type " << from_type(ns, "", type) << messaget::eom;

  initialize_shadow_memory(
    state, index_expr.array(), state.global_fields);
}

void goto_symext::symex_field_local_init(
  goto_symex_statet &state,
  const ssa_exprt &expr)
{
  const symbolt &symbol =
    ns.lookup(to_symbol_expr(expr.get_original_expr()).get_identifier());

  if(symbol.is_auxiliary)
    return;
  const std::string symbol_name = id2string(symbol.name);
  if(
    symbol_name.find("malloc::") != std::string::npos &&
      (symbol_name.find("malloc_size") != std::string::npos ||
       symbol_name.find("malloc_res") != std::string::npos ||
       symbol_name.find("record_malloc") != std::string::npos ||
       symbol_name.find("record_may_leak") != std::string::npos))
  {
    return;
  }
  if(
    symbol_name.find("__builtin_alloca::") != std::string::npos &&
      (symbol_name.find("alloca_size") != std::string::npos ||
       symbol_name.find("record_malloc") != std::string::npos ||
       symbol_name.find("record_alloca") != std::string::npos ||
       symbol_name.find("res") != std::string::npos))
  {
    return;
  }
  if(symbol_name.find("__cs_") != std::string::npos)
    return;

  const typet &type = expr.type();
  ssa_exprt expr_l1 = remove_level_2(expr);
  log.debug() << "local memory " << id2string(expr_l1.get_identifier())
              << " of type " << from_type(ns, "", type) << messaget::eom;

  initialize_shadow_memory(state, expr_l1, state.local_fields);
}

void goto_symext::symex_field_dynamic_init(
  goto_symex_statet &state,
  const exprt &expr,
  const side_effect_exprt &code)
{
  log.debug() << "dynamic memory of type " << from_type(ns, "", expr.type())
              << messaget::eom;

  initialize_shadow_memory(state, expr, state.global_fields);
}

std::pair<std::map<irep_idt, typet>, std::map<irep_idt, typet>>
goto_symext::preprocess_field_decl(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  std::map<irep_idt, typet> global_fields;
  std::map<irep_idt, typet> local_fields;
  namespacet ns(goto_model.symbol_table);

  // get declarations
  for(auto &goto_function : goto_model.goto_functions.function_map)
  {
    goto_programt &goto_program = goto_function.second.body;
    Forall_goto_program_instructions(target, goto_program)
    {
      if(!target->is_function_call())
        continue;

      const code_function_callt &code_function_call =
        to_code_function_call(target->get_code());
      const exprt &function = code_function_call.function();

      if(function.id() != ID_symbol)
        continue;

      const irep_idt &identifier = to_symbol_expr(function).get_identifier();

      if(identifier == CPROVER_PREFIX "field_decl_global")
      {
        convert_field_decl(
          ns, message_handler, code_function_call, global_fields);
        target->turn_into_skip();
      }
      else if(identifier == CPROVER_PREFIX "field_decl_local")
      {
        convert_field_decl(
            ns, message_handler, code_function_call, local_fields);
        target->turn_into_skip();
      }
    }
  }
  return std::make_pair(global_fields, local_fields);
}

void goto_symext::convert_field_decl(
  const namespacet &ns,
  message_handlert &message_handler,
  const code_function_callt &code_function_call,
  std::map<irep_idt, typet> &fields)
{
  INVARIANT(
    code_function_call.arguments().size() == 2,
    CPROVER_PREFIX "field_decl requires 2 arguments");
  irep_idt field_name = get_field_name(code_function_call.arguments()[0]);

  exprt expr = code_function_call.arguments()[1];

  messaget log(message_handler);
  log.debug() << "declare " << id2string(field_name) << " of type "
              << from_type(ns, "", expr.type()) << messaget::eom;

  // record field type
  fields[field_name] = expr.type();
}
