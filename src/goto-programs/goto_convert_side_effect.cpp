/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Transformation

#include "goto_convert_class.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/expr_util.h>
#include <util/fresh_symbol.h>
#include <util/mathematical_types.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include <ansi-c/c_expr.h>

#include "byte_operators.h"

bool goto_convertt::has_function_call(const exprt &expr)
{
  for(const auto &op : expr.operands())
  {
    if(has_function_call(op))
      return true;
  }

  if(expr.id()==ID_side_effect &&
     expr.get(ID_statement)==ID_function_call)
    return true;

  return false;
}

void goto_convertt::remove_assignment(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used,
  bool address_taken,
  const irep_idt &mode)
{
  const irep_idt statement=expr.get_statement();

  optionalt<exprt> replacement_expr_opt;

  if(statement==ID_assign)
  {
    auto &old_assignment = to_side_effect_expr_assign(expr);
    exprt new_lhs = skip_typecast(old_assignment.lhs());

    if(
      result_is_used && !address_taken &&
      assignment_lhs_needs_temporary(old_assignment.lhs()))
    {
      if(!old_assignment.rhs().is_constant())
        make_temp_symbol(old_assignment.rhs(), "assign", dest, mode);

      replacement_expr_opt =
        typecast_exprt::conditional_cast(old_assignment.rhs(), new_lhs.type());
    }

    exprt new_rhs =
      typecast_exprt::conditional_cast(old_assignment.rhs(), new_lhs.type());
    code_assignt new_assignment(std::move(new_lhs), std::move(new_rhs));
    new_assignment.add_source_location() = expr.source_location();

    convert_assign(new_assignment, dest, mode);
  }
  else if(statement==ID_assign_plus ||
          statement==ID_assign_minus ||
          statement==ID_assign_mult ||
          statement==ID_assign_div ||
          statement==ID_assign_mod ||
          statement==ID_assign_shl ||
          statement==ID_assign_ashr ||
          statement==ID_assign_lshr ||
          statement==ID_assign_bitand ||
          statement==ID_assign_bitxor ||
          statement==ID_assign_bitor)
  {
    INVARIANT_WITH_DIAGNOSTICS(
      expr.operands().size() == 2,
      id2string(statement) + " expects two arguments",
      expr.find_source_location());

    irep_idt new_id;

    if(statement==ID_assign_plus)
      new_id=ID_plus;
    else if(statement==ID_assign_minus)
      new_id=ID_minus;
    else if(statement==ID_assign_mult)
      new_id=ID_mult;
    else if(statement==ID_assign_div)
      new_id=ID_div;
    else if(statement==ID_assign_mod)
      new_id=ID_mod;
    else if(statement==ID_assign_shl)
      new_id=ID_shl;
    else if(statement==ID_assign_ashr)
      new_id=ID_ashr;
    else if(statement==ID_assign_lshr)
      new_id=ID_lshr;
    else if(statement==ID_assign_bitand)
      new_id=ID_bitand;
    else if(statement==ID_assign_bitxor)
      new_id=ID_bitxor;
    else if(statement==ID_assign_bitor)
      new_id=ID_bitor;
    else
    {
      UNREACHABLE;
    }

    const binary_exprt &binary_expr = to_binary_expr(expr);
    exprt new_lhs = skip_typecast(binary_expr.op0());
    const typet &op0_type = binary_expr.op0().type();

    PRECONDITION(
      op0_type.id() != ID_c_enum_tag && op0_type.id() != ID_c_enum &&
      op0_type.id() != ID_c_bool && op0_type.id() != ID_bool);

    exprt rhs = binary_exprt{binary_expr.op0(), new_id, binary_expr.op1()};
    rhs.add_source_location() = expr.source_location();

    if(
      result_is_used && !address_taken &&
      assignment_lhs_needs_temporary(binary_expr.op0()))
    {
      make_temp_symbol(rhs, "assign", dest, mode);
      replacement_expr_opt =
        typecast_exprt::conditional_cast(rhs, new_lhs.type());
    }

    rhs = typecast_exprt::conditional_cast(rhs, new_lhs.type());
    rhs.add_source_location() = expr.source_location();
    code_assignt assignment(new_lhs, rhs);
    assignment.add_source_location()=expr.source_location();

    convert(assignment, dest, mode);
  }
  else
    UNREACHABLE;

  // revert assignment in the expression to its LHS
  if(replacement_expr_opt.has_value())
  {
    exprt new_lhs =
      typecast_exprt::conditional_cast(*replacement_expr_opt, expr.type());
    expr.swap(new_lhs);
  }
  else if(result_is_used)
  {
    exprt lhs = to_binary_expr(expr).op0();
    // assign_* statements can have an lhs operand with a different type than
    // that of the overall expression, because of integer promotion (which may
    // have introduced casts to the lhs).
    if(expr.type() != lhs.type())
    {
      // Skip over those type casts, but also
      // make sure the resulting expression has the same type as before.
      DATA_INVARIANT(
        lhs.id() == ID_typecast,
        id2string(expr.id()) +
          " expression with different operand type expected to have a "
          "typecast");
      DATA_INVARIANT(
        to_typecast_expr(lhs).op().type() == expr.type(),
        id2string(expr.id()) + " type mismatch in lhs operand");
      lhs = to_typecast_expr(lhs).op();
    }
    expr.swap(lhs);
  }
  else
    expr.make_nil();
}

void goto_convertt::remove_pre(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used,
  bool address_taken,
  const irep_idt &mode)
{
  INVARIANT_WITH_DIAGNOSTICS(
    expr.operands().size() == 1,
    "preincrement/predecrement must have one operand",
    expr.find_source_location());

  const irep_idt statement=expr.get_statement();

  DATA_INVARIANT(
    statement == ID_preincrement || statement == ID_predecrement,
    "expects preincrement or predecrement");

  const auto &op = to_unary_expr(expr).op();
  const typet &op_type = op.type();

  PRECONDITION(
    op_type.id() != ID_c_enum_tag && op_type.id() != ID_c_enum &&
    op_type.id() != ID_c_bool && op_type.id() != ID_bool);

  typet constant_type;

  if(op_type.id() == ID_pointer)
    constant_type = c_index_type();
  else if(is_number(op_type))
    constant_type = op_type;
  else
  {
    UNREACHABLE;
  }

  exprt constant;

  if(constant_type.id() == ID_complex)
  {
    exprt real = from_integer(1, to_complex_type(constant_type).subtype());
    exprt imag = from_integer(0, to_complex_type(constant_type).subtype());
    constant = complex_exprt(real, imag, to_complex_type(constant_type));
  }
  else
    constant = from_integer(1, constant_type);

  exprt rhs = binary_exprt{
    op, statement == ID_preincrement ? ID_plus : ID_minus, std::move(constant)};
  rhs.add_source_location() = expr.source_location();

  // Is there a typecast, e.g., for _Bool? If so, transform
  // t1(op : t2) := op+1  -->  op := t2(op+1)
  exprt lhs;
  if(op.id() == ID_typecast)
  {
    lhs = to_typecast_expr(op).op();
    rhs = typecast_exprt(rhs, lhs.type());
  }
  else
  {
    lhs = op;
  }

  const bool cannot_use_lhs =
    result_is_used && !address_taken && assignment_lhs_needs_temporary(lhs);
  if(cannot_use_lhs)
    make_temp_symbol(rhs, "pre", dest, mode);

  code_assignt assignment(lhs, rhs);
  assignment.add_source_location()=expr.find_source_location();

  convert(assignment, dest, mode);

  if(result_is_used)
  {
    if(cannot_use_lhs)
    {
      auto tmp = typecast_exprt::conditional_cast(rhs, expr.type());
      expr.swap(tmp);
    }
    else
    {
      // revert to argument of pre-inc/pre-dec
      auto tmp = typecast_exprt::conditional_cast(lhs, expr.type());
      expr.swap(tmp);
    }
  }
  else
    expr.make_nil();
}

void goto_convertt::remove_post(
  side_effect_exprt &expr,
  goto_programt &dest,
  const irep_idt &mode,
  bool result_is_used)
{
  goto_programt tmp1, tmp2;

  // we have ...(op++)...

  INVARIANT_WITH_DIAGNOSTICS(
    expr.operands().size() == 1,
    "postincrement/postdecrement must have one operand",
    expr.find_source_location());

  const irep_idt statement=expr.get_statement();

  DATA_INVARIANT(
    statement == ID_postincrement || statement == ID_postdecrement,
    "expects postincrement or postdecrement");

  const auto &op = to_unary_expr(expr).op();
  const typet &op_type = op.type();

  PRECONDITION(
    op_type.id() != ID_c_enum_tag && op_type.id() != ID_c_enum &&
    op_type.id() != ID_c_bool && op_type.id() != ID_bool);

  typet constant_type;

  if(op_type.id() == ID_pointer)
    constant_type = c_index_type();
  else if(is_number(op_type))
    constant_type = op_type;
  else
  {
    UNREACHABLE;
  }

  exprt constant;

  if(constant_type.id() == ID_complex)
  {
    exprt real = from_integer(1, to_complex_type(constant_type).subtype());
    exprt imag = from_integer(0, to_complex_type(constant_type).subtype());
    constant = complex_exprt(real, imag, to_complex_type(constant_type));
  }
  else
    constant = from_integer(1, constant_type);

  binary_exprt rhs{
    op,
    statement == ID_postincrement ? ID_plus : ID_minus,
    std::move(constant)};
  rhs.add_source_location() = expr.source_location();

  code_assignt assignment(op, rhs);
  assignment.add_source_location()=expr.find_source_location();

  convert(assignment, tmp2, mode);

  // fix up the expression, if needed

  if(result_is_used)
  {
    exprt tmp = op;
    std::string suffix = "post";
    if(auto sym_expr = expr_try_dynamic_cast<symbol_exprt>(tmp))
    {
      const irep_idt &base_name = ns.lookup(*sym_expr).base_name;
      suffix += "_" + id2string(base_name);
    }

    make_temp_symbol(tmp, suffix, dest, mode);
    expr.swap(tmp);
  }
  else
    expr.make_nil();

  dest.destructive_append(tmp1);
  dest.destructive_append(tmp2);
}

void goto_convertt::remove_function_call(
  side_effect_expr_function_callt &expr,
  goto_programt &dest,
  const irep_idt &mode,
  bool result_is_used)
{
  if(!result_is_used)
  {
    if(expr.function().id() == ID_symbol &&
       (id2string(to_symbol_expr(expr.function()).get_identifier()) == CPROVER_PREFIX "cut_bits" ||
       id2string(to_symbol_expr(expr.function()).get_identifier()) == CPROVER_PREFIX "nz_bits")){
      clean_expr(expr.arguments()[0], dest, mode, false);
      clean_expr(expr.arguments()[1], dest, mode, false);
    }
    else
    {
      code_function_callt call(expr.function(), expr.arguments());
      call.add_source_location() = expr.source_location();
      convert_function_call(call, dest, mode);
    }
    expr.make_nil();
    return;
  }

  // get name of function, if available
  std::string new_base_name = "return_value";
  irep_idt new_symbol_mode = mode;

  auto return_type = expr.type();
  if(expr.function().id() == ID_symbol)
  {
    const irep_idt &identifier =
      to_symbol_expr(expr.function()).get_identifier();
    const symbolt &symbol = ns.lookup(identifier);

    new_base_name+='_';
    new_base_name+=id2string(symbol.base_name);
    new_symbol_mode = symbol.mode;

    if(id2string(symbol.base_name) == CPROVER_PREFIX "cut_bits"){
      clean_expr(expr.arguments()[0], dest, mode);
      clean_expr(expr.arguments()[1], dest, mode);
      const size_t w = stoi(id2string(to_constant_expr(expr.arguments()[1]).get_value()));
      const auto typeArgOrig = expr.arguments()[0].type();
      if(typeArgOrig.id() == ID_bool){
        expr.swap(expr.arguments()[0]);
      } else if(typeArgOrig.id() == ID_c_bool){
        auto x = extractbit_exprt{
          expr.arguments()[0], 0};
        expr.swap(x);
      } else
      {
        const auto typeArg = to_integer_bitvector_type(typeArgOrig);
        if(typeArg.get_width() <= w)
        {
          expr.swap(expr.arguments()[0]);
        }
        else
        {
          const auto new_type =
            (typeArg.smallest() < 0 ? (integer_bitvector_typet)signedbv_typet{w}
                                    : unsignedbv_typet{w});
          auto x = extractbits_exprt{
            expr.arguments()[0], new_type.get_width() - 1, 0, new_type};
          expr.swap(x);
        }
      }
      return;
    }
    else if(id2string(symbol.base_name) == CPROVER_PREFIX "nz_bits"){
      clean_expr(expr.arguments()[0], dest, mode);
      clean_expr(expr.arguments()[1], dest, mode);
      if(type_try_dynamic_cast<c_bool_typet>(expr.arguments()[0].type())){
        auto nz = typecast_exprt{expr.arguments()[0], bool_typet{}};
        expr.swap(nz);
      }
      else if(type_try_dynamic_cast<bool_typet>(expr.arguments()[0].type())){
        expr.swap(expr.arguments()[0]);
      }
      else
      {
        const size_t w =
          stoi(id2string(to_constant_expr(expr.arguments()[1]).get_value()));
        const auto typeArg =
          to_integer_bitvector_type(expr.arguments()[0].type());
        if(typeArg.get_width() <= w)
        {
          auto nz =
            notequal_exprt{expr.arguments()[0], from_integer(0, typeArg)};
          expr.swap(nz);
        }
        else
        {
          const auto new_type =
            (typeArg.smallest() < 0 ? (integer_bitvector_typet)signedbv_typet{w}
                                    : unsignedbv_typet{w});
          auto nz = notequal_exprt{
            extractbits_exprt{
              expr.arguments()[0], new_type.get_width() - 1, 0, new_type},
            from_integer(0, new_type)};
          expr.swap(nz);
        }
      }
      return;
    }
  }

  const symbolt &new_symbol = get_fresh_aux_symbol(
    return_type,
    tmp_symbol_prefix,
    new_base_name,
    expr.find_source_location(),
    new_symbol_mode,
    symbol_table);

  {
    code_frontend_declt decl(new_symbol.symbol_expr());
    decl.add_source_location()=new_symbol.location;
    convert_frontend_decl(decl, dest, mode);
  }

  {
    goto_programt tmp_program2;
    code_function_callt call(
      new_symbol.symbol_expr(), expr.function(), expr.arguments());
    call.add_source_location()=new_symbol.location;
    convert_function_call(call, dest, mode);
  }

  static_cast<exprt &>(expr)=new_symbol.symbol_expr();
}

void goto_convertt::replace_new_object(
  const exprt &object,
  exprt &dest)
{
  if(dest.id()=="new_object")
    dest=object;
  else
    Forall_operands(it, dest)
      replace_new_object(object, *it);
}

void goto_convertt::remove_cpp_new(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used)
{
  const symbolt &new_symbol = get_fresh_aux_symbol(
    expr.type(),
    tmp_symbol_prefix,
    "new_ptr",
    expr.find_source_location(),
    ID_cpp,
    symbol_table);

  code_frontend_declt decl(new_symbol.symbol_expr());
  decl.add_source_location()=new_symbol.location;
  convert_frontend_decl(decl, dest, ID_cpp);

  const code_assignt call(new_symbol.symbol_expr(), expr);

  if(result_is_used)
    static_cast<exprt &>(expr)=new_symbol.symbol_expr();
  else
    expr.make_nil();

  convert(call, dest, ID_cpp);
}

void goto_convertt::remove_cpp_delete(
  side_effect_exprt &expr,
  goto_programt &dest)
{
  DATA_INVARIANT(expr.operands().size() == 1, "cpp_delete expects one operand");

  codet tmp(expr.get_statement());
  tmp.add_source_location()=expr.source_location();
  tmp.copy_to_operands(to_unary_expr(expr).op());
  tmp.set(ID_destructor, expr.find(ID_destructor));

  convert_cpp_delete(tmp, dest);

  expr.make_nil();
}

void goto_convertt::remove_malloc(
  side_effect_exprt &expr,
  goto_programt &dest,
  const irep_idt &mode,
  bool result_is_used)
{
  if(result_is_used)
  {
    const symbolt &new_symbol = get_fresh_aux_symbol(
      expr.type(),
      tmp_symbol_prefix,
      "malloc_value",
      expr.source_location(),
      mode,
      symbol_table);

    code_frontend_declt decl(new_symbol.symbol_expr());
    decl.add_source_location()=new_symbol.location;
    convert_frontend_decl(decl, dest, mode);

    code_assignt call(new_symbol.symbol_expr(), expr);
    call.add_source_location()=expr.source_location();

    static_cast<exprt &>(expr)=new_symbol.symbol_expr();

    convert(call, dest, mode);
  }
  else
  {
    convert(code_expressiont(std::move(expr)), dest, mode);
  }
}

void goto_convertt::remove_temporary_object(
  side_effect_exprt &expr,
  goto_programt &dest)
{
  const irep_idt &mode = expr.get(ID_mode);
  INVARIANT_WITH_DIAGNOSTICS(
    expr.operands().size() <= 1,
    "temporary_object takes zero or one operands",
    expr.find_source_location());

  symbolt &new_symbol = new_tmp_symbol(
    expr.type(), "obj", dest, expr.find_source_location(), mode);

  if(expr.operands().size()==1)
  {
    const code_assignt assignment(
      new_symbol.symbol_expr(), to_unary_expr(expr).op());

    convert(assignment, dest, mode);
  }

  if(expr.find(ID_initializer).is_not_nil())
  {
    INVARIANT_WITH_DIAGNOSTICS(
      expr.operands().empty(),
      "temporary_object takes zero operands",
      expr.find_source_location());
    exprt initializer=static_cast<const exprt &>(expr.find(ID_initializer));
    replace_new_object(new_symbol.symbol_expr(), initializer);

    convert(to_code(initializer), dest, mode);
  }

  static_cast<exprt &>(expr)=new_symbol.symbol_expr();
}

void goto_convertt::remove_statement_expression(
  side_effect_exprt &expr,
  goto_programt &dest,
  const irep_idt &mode,
  bool result_is_used)
{
  // This is a gcc extension of the form ({ ....; expr; })
  // The value is that of the final expression.
  // The expression is copied into a temporary before the
  // scope is destroyed.

  codet &code = to_side_effect_expr_statement_expression(expr).statement();

  if(!result_is_used)
  {
    convert(code, dest, mode);
    expr.make_nil();
    return;
  }

  INVARIANT_WITH_DIAGNOSTICS(
    code.get_statement() == ID_block,
    "statement_expression takes block as operand",
    code.find_source_location());

  INVARIANT_WITH_DIAGNOSTICS(
    !code.operands().empty(),
    "statement_expression takes non-empty block as operand",
    expr.find_source_location());

  // get last statement from block, following labels
  codet &last=to_code_block(code).find_last_statement();

  source_locationt source_location=last.find_source_location();

  symbolt &new_symbol = new_tmp_symbol(
    expr.type(), "statement_expression", dest, source_location, mode);

  symbol_exprt tmp_symbol_expr(new_symbol.name, new_symbol.type);
  tmp_symbol_expr.add_source_location()=source_location;

  if(last.get(ID_statement)==ID_expression)
  {
    // we turn this into an assignment
    exprt e=to_code_expression(last).expression();
    last=code_assignt(tmp_symbol_expr, e);
    last.add_source_location()=source_location;
  }
  else if(last.get(ID_statement)==ID_assign)
  {
    exprt e=to_code_assign(last).lhs();
    code_assignt assignment(tmp_symbol_expr, e);
    assignment.add_source_location()=source_location;
    code.operands().push_back(assignment);
  }
  else
  {
    UNREACHABLE;
  }

  {
    goto_programt tmp;
    convert(code, tmp, mode);
    dest.destructive_append(tmp);
  }

  static_cast<exprt &>(expr)=tmp_symbol_expr;
}

exprt cast_or_cut(const exprt &expr, const typet& dest_type, std::size_t w){
  unsignedbv_typet uw = unsignedbv_typet{w};
  signedbv_typet sw = signedbv_typet{w};
  if(type_try_dynamic_cast<bool_typet>(expr.type()) || type_try_dynamic_cast<c_bool_typet>(expr.type())){
    if(type_try_dynamic_cast<bool_typet>(dest_type)){
      if(expr.type().id() == ID_bool){
        return expr;
      } else {
        return extractbit_exprt{expr, 0};
      }
    } else if(const auto u = type_try_dynamic_cast<unsignedbv_typet>(dest_type)){
      if(u->get_width() <= w){
        return typecast_exprt{expr, dest_type};
      } else {
        return typecast_exprt{expr, unsignedbv_typet{w}};
      }
    } else if(const auto s = type_try_dynamic_cast<signedbv_typet>(dest_type)){
      if(s->get_width() <= w){
        return typecast_exprt{expr, dest_type};
      } else {
        return typecast_exprt{expr, signedbv_typet{w}};
      }
    } else
      UNHANDLED_CASE;
  } else if(const auto ue = type_try_dynamic_cast<unsignedbv_typet>(expr.type())){
    bool expr_short = ue->get_width() <= w;
    if(type_try_dynamic_cast<bool_typet>(dest_type)){
      if(expr_short){
        return typecast_exprt{expr, dest_type};
      } else {
        return typecast_exprt{extractbits_exprt{expr, w-1, 0, uw}, dest_type};
      }
    } else if(const auto ud = type_try_dynamic_cast<unsignedbv_typet>(dest_type)){
      bool dest_short = ud->get_width() <= w;
      if(!expr_short && !dest_short){
        return extractbits_exprt{expr, w-1, 0, uw};
      } else if(!expr_short && dest_short) {
        return typecast_exprt{extractbits_exprt{expr, w-1, 0, uw}, dest_type};
      } else if(expr_short && !dest_short) {
        return typecast_exprt{expr, uw};
      } else if(ue->get_width() != ud->get_width()){
        return typecast_exprt{expr, dest_type};
      } else {
        return expr;
      }
    } else if(const auto sd = type_try_dynamic_cast<signedbv_typet>(dest_type)){
      bool dest_short = sd->get_width() <= w;
      if(!expr_short && !dest_short){
        return extractbits_exprt{expr, w-1, 0, sw};
      } else if(!expr_short && dest_short) {
        return typecast_exprt{extractbits_exprt{expr, w-1, 0, sw}, dest_type};
      } else if(expr_short && !dest_short) {
        return typecast_exprt{expr, sw};
      } else{
        return typecast_exprt{expr, dest_type};
      }
    } else
      UNHANDLED_CASE;
  } else if(const auto se = type_try_dynamic_cast<signedbv_typet>(expr.type())){
    bool expr_short = se->get_width() <= w;
    if(type_try_dynamic_cast<bool_typet>(dest_type)){
      if(expr_short){
        return typecast_exprt{expr, dest_type};
      } else {
        return typecast_exprt{extractbits_exprt{expr, w-1, 0, sw}, dest_type};
      }
    } else if(const auto ud = type_try_dynamic_cast<unsignedbv_typet>(dest_type)){
      bool dest_short = ud->get_width() <= w;
      if(!expr_short && !dest_short){
        return extractbits_exprt{expr, w-1, 0, uw};
      } else if(!expr_short) {
        return typecast_exprt{extractbits_exprt{expr, w-1, 0, uw}, dest_type};
      } else if(!dest_short) {
        return typecast_exprt{expr, uw};
      } else {
        return typecast_exprt{expr, dest_type};
      }
    } else if(const auto sd = type_try_dynamic_cast<signedbv_typet>(dest_type)){
      bool dest_short = sd->get_width() <= w;
      if(!expr_short && !dest_short){
        return extractbits_exprt{expr, w-1, 0, sw};
      } else if(!expr_short) {
        return typecast_exprt{extractbits_exprt{expr, w-1, 0, sw}, dest_type};
      } else if(!dest_short) {
        return typecast_exprt{expr, sw};
      } else if(se->get_width() != sd->get_width()){
        return typecast_exprt{expr, dest_type};
      } else {
        return expr;
      }
    } else
      UNHANDLED_CASE;
  } else
    UNHANDLED_CASE;
}

code_assignt assignment(const exprt& lhs, const exprt& rhs, const size_t w){
  if(type_try_dynamic_cast<bool_typet>(lhs.type())){
    if(type_try_dynamic_cast<bool_typet>(rhs.type())){
      return code_assignt{lhs, rhs};
    } else if(type_try_dynamic_cast<integer_bitvector_typet>(rhs.type())){
      return code_assignt{lhs,
                          notequal_exprt{rhs, constant_exprt{"0",rhs.type()}}};
    } else
      UNHANDLED_CASE;
  } else if(type_try_dynamic_cast<c_bool_typet>(lhs.type())){
    if(type_try_dynamic_cast<bool_typet>(rhs.type())){
      return code_assignt{lhs, make_byte_update(lhs, constant_exprt{"0",unsignedbv_typet{1}}, typecast_exprt{rhs, unsignedbv_typet{1}})};
    } else if(type_try_dynamic_cast<integer_bitvector_typet>(rhs.type())){
      return code_assignt{lhs,
                          make_byte_update(lhs, constant_exprt{"0",unsignedbv_typet{1}},
                                           typecast_exprt{
                                             notequal_exprt{rhs, constant_exprt{"0",rhs.type()}},
                                             unsignedbv_typet{1}})};
    } else
      UNHANDLED_CASE;
  } else if(const auto lbt = type_try_dynamic_cast<integer_bitvector_typet>(lhs.type())){
    if(lbt->get_width() <= w){
      if(type_try_dynamic_cast<bool_typet>(rhs.type())){
        return code_assignt{lhs,
                            make_byte_update(lhs, constant_exprt{"0",unsignedbv_typet{1}},
                                             typecast_exprt{rhs,*lbt})};
      } else if(const auto rbt = type_try_dynamic_cast<integer_bitvector_typet>(rhs.type())){
        PRECONDITION(lbt->get_width() == rbt->get_width());
        /*if(*lbt == *rbt)
          return code_assignt{lhs, rhs};
        else
          return code_assignt{lhs, typecast_exprt{rhs, *lbt}};*/
        return code_assignt{lhs, make_byte_update(lhs, constant_exprt{"0",unsignedbv_typet{1}},
                                           rhs)};
      } else
        UNHANDLED_CASE;
    } else {
      auto wtype = lbt->smallest() < 0 ? (integer_bitvector_typet) signedbv_typet{w} : unsignedbv_typet{w};
      if(type_try_dynamic_cast<bool_typet>(rhs.type())){
        return code_assignt{lhs,
                            make_byte_update(lhs, constant_exprt{"0",unsignedbv_typet{1}},
                                             typecast_exprt{rhs,wtype})};
      } else if(const auto rbt = type_try_dynamic_cast<integer_bitvector_typet>(rhs.type())){
        PRECONDITION(wtype.get_width() == rbt->get_width());
        return code_assignt{lhs, make_byte_update(lhs, constant_exprt{"0",unsignedbv_typet{1}},
                                                  rhs)};
      } else
        UNHANDLED_CASE;
    }
  } else
    UNHANDLED_CASE;
}

void goto_convertt::binaryop_between_bools(const exprt &a, const irep_idt op, const exprt &b, const optionalt<exprt> &dest_deref, const optionalt<exprt> &of_deref, const size_t w, goto_programt &dest, const irep_idt &mode){
  PRECONDITION(a.type().id() == ID_bool && b.type().id() == ID_bool);
  if(of_deref)
    convert_assign(code_assignt{*of_deref, constant_exprt{"0", of_deref->type()}}, dest, mode);
  if(dest_deref)
  {
    exprt res;
    if(op == ID_plus || op == ID_or || op == ID_bitor)
      res = or_exprt{a,b};
    else if(op == ID_minus || op == ID_notequal || op == ID_xor || op == ID_bitxor)
      res = xor_exprt{a,b};
    else if(op == ID_mult || op == ID_and || op == ID_bitand)
      res = and_exprt{a,b};
    else if(op == ID_div || op == ID_shl)
      res = a;
    else if(op == ID_equal)
      res = equal_exprt{a,b};
    else if(op == ID_lt)
      res = and_exprt{not_exprt{a},b};
    else if(op == ID_gt || op == ID_shr)
      res = and_exprt{not_exprt{b},a};
    else if(op == ID_le)
      res = or_exprt{not_exprt{a},b};
    else if(op == ID_ge)
      res = or_exprt{not_exprt{b},a};
    else if(op == ID_mod)
      res = constant_exprt{"0", bool_typet{}};
    else
      UNREACHABLE;

    exprt rhs;
    if(can_cast_type<bool_typet>(dest_deref->type())){
      rhs = res;
    } else if (can_cast_type<c_bool_typet>(dest_deref->type())){
      rhs = make_byte_update(*dest_deref, constant_exprt{"0", unsignedbv_typet{1}}, res);
    } else if (const auto udt = type_try_dynamic_cast<unsignedbv_typet>(dest_deref->type()))
    {
      if(udt->get_width() <= w)
      {
        rhs = typecast_exprt{res, *udt};
      }
      else
      {
        rhs = make_byte_update(
          *dest_deref,
          constant_exprt{"0", unsignedbv_typet{1}},
          typecast_exprt{res, unsignedbv_typet{w}});
      }
    } else if (const auto sdt = type_try_dynamic_cast<signedbv_typet>(dest_deref->type()))
    {
      if(sdt->get_width() <= w)
      {
        rhs = typecast_exprt{res, *sdt};
      }
      else
      {
        rhs = make_byte_update(
          *dest_deref,
          constant_exprt{"0", unsignedbv_typet{1}},
          typecast_exprt{res, signedbv_typet{w}});
      }
    }
    convert_assign(code_assignt{*dest_deref, rhs}, dest, mode);
  }
}

void goto_convertt::binary_op_with_int(const exprt &a, const irep_idt op, const exprt &b, const optionalt<exprt> &dest_deref, const optionalt<exprt> &of_deref, const size_t w, goto_programt &dest, const irep_idt &mode){
  //todo add locations e.g. overflow_with_result.add_source_location() = expr.source_location();
  //todo expression without of
  const size_t width_a = (a.type().id() == ID_bool || a.type().id() == ID_c_bool) ? 1 : to_integer_bitvector_type(a.type()).get_width();
  const size_t width_b = (b.type().id() == ID_bool || b.type().id() == ID_c_bool) ? 1 : to_integer_bitvector_type(b.type()).get_width();
  const size_t width_dest = !dest_deref? w : ((dest_deref->type().id() == ID_bool || dest_deref->type().id() == ID_c_bool) ? 1 : to_integer_bitvector_type(dest_deref->type()).get_width());
  const bool sign_a = (type_try_dynamic_cast<signedbv_typet>(a.type()));
  const bool sign_b = (type_try_dynamic_cast<signedbv_typet>(b.type()));
  const bool sign_dest =
    !dest_deref ||
    (bool)(type_try_dynamic_cast<signedbv_typet>(dest_deref->type()));
  const bool abstr_dest = width_dest > w;

  const bool has_of_defined = op == ID_plus || op == ID_minus || op == ID_mult || op == ID_shl;
  if(!sign_a && !sign_b){
    const auto wtype = std::max(std::max(width_a, width_b), width_dest);
    const auto type = unsignedbv_typet{wtype};
    if(abstr_dest && has_of_defined){
      exprt overflow_with_result = overflow_result_exprt{
        cast_or_cut(a, type, w), op, cast_or_cut(b, type, w)};
      make_temp_symbol(overflow_with_result, "overflow_result", dest, mode);
      const struct_typet::componentst &result_comps =
        to_struct_type(overflow_with_result.type()).components();
      CHECK_RETURN(result_comps.size() == 2);
      if(dest_deref) convert_assign(assignment(*dest_deref, member_exprt{overflow_with_result, result_comps[0]}, w), dest, mode);
      if(sign_dest)
      {
        if(of_deref) convert_assign(
          assignment(
            *of_deref,
            or_exprt{
              member_exprt{overflow_with_result, result_comps[1]},
              extractbit_exprt{member_exprt{overflow_with_result, result_comps[0]}, w - 1}},
            w),
          dest,
          mode);
      } else
      {
        if(of_deref) convert_assign(
          assignment(
            *of_deref, member_exprt{overflow_with_result, result_comps[1]}, w),
          dest,
          mode);
      }
    } else {
      if(dest_deref) convert_assign(assignment(*dest_deref, cast_or_cut(binary_exprt{cast_or_cut(a, type, w), op, cast_or_cut(b, type, w)}, dest_deref->type(), w), w), dest, mode);
      if(of_deref) convert_assign(assignment(*of_deref, constant_exprt{"0", unsignedbv_typet{1}}, w), dest, mode);
    }
  } if (!(sign_a && sign_b)) {
    const auto wtype = std::max(std::max(std::min(width_a, w) + !sign_a, std::min(width_b, w) + !sign_b), std::min(width_dest, w) + !sign_dest);
    const auto type = signedbv_typet{wtype};
    const auto cast_a = typecast_exprt{cast_or_cut(a, a.type(), w), type};
    const auto cast_b = typecast_exprt{cast_or_cut(b, b.type(), w), type};
    if(abstr_dest && has_of_defined){
      exprt overflow_with_result = overflow_result_exprt{cast_a, op, cast_b};
      make_temp_symbol(overflow_with_result, "overflow_result", dest, mode);
      const struct_typet::componentst &result_comps =
        to_struct_type(overflow_with_result.type()).components();
      CHECK_RETURN(result_comps.size() == 2);
      if(dest_deref) convert_assign(assignment(*dest_deref, cast_or_cut(member_exprt{overflow_with_result, result_comps[0]}, dest_deref->type(), w), w), dest, mode);
      if(sign_dest){
        const auto of_ans = member_exprt{overflow_with_result, result_comps[1]};
        if(type.get_width() > w){
          const auto sign_ans = notequal_exprt{extractbit_exprt{member_exprt{overflow_with_result, result_comps[0]},w},
                                               extractbit_exprt{member_exprt{overflow_with_result, result_comps[0]},w-1}};
          const auto of_total = or_exprt{sign_ans, of_ans};
          if(of_deref) convert_assign(assignment(*of_deref, of_total, w), dest, mode);
        } else {
          if(of_deref) convert_assign(assignment(*of_deref, of_ans, w), dest, mode);
        }
      } else {
        const auto of_ans = member_exprt{overflow_with_result, result_comps[1]};
        if(type.get_width() > w)
        {
          const auto sign_ans = typecast_exprt{
            extractbit_exprt{
              member_exprt{overflow_with_result, result_comps[0]}, w},
            bool_typet{}};
          const auto of_total = or_exprt{sign_ans, of_ans};
          if(of_deref) convert_assign(assignment(*of_deref, of_total, w), dest, mode);
        } else {
          const auto sign_ans = typecast_exprt{
            extractbit_exprt{
              member_exprt{overflow_with_result, result_comps[0]}, w-1},
            bool_typet{}};
          const auto of_total = or_exprt{sign_ans, of_ans};
          if(of_deref) convert_assign(assignment(*of_deref, of_total, w), dest, mode);
        }
      }
    } else {
      if(dest_deref) convert_assign(assignment(*dest_deref, cast_or_cut(binary_exprt{cast_a, op, cast_b}, dest_deref->type(), w), w), dest, mode);
      if(of_deref) convert_assign(assignment(*of_deref, constant_exprt{"0", unsignedbv_typet{1}}, w), dest, mode);
    }
  } else {
    if(abstr_dest && has_of_defined){
      if(sign_dest){
        const auto type = signedbv_typet{w};
        const auto cast_a = typecast_exprt{cast_or_cut(a, a.type(), w), type};
        const auto cast_b = typecast_exprt{cast_or_cut(b, b.type(), w), type};
        exprt overflow_with_result = overflow_result_exprt{cast_a, op, cast_b};
        make_temp_symbol(overflow_with_result, "overflow_result", dest, mode);
        const struct_typet::componentst &result_comps =
          to_struct_type(overflow_with_result.type()).components();
        CHECK_RETURN(result_comps.size() == 2);
        if(dest_deref) convert_assign(assignment(*dest_deref, cast_or_cut(member_exprt{overflow_with_result, result_comps[0]}, dest_deref->type(), w), w), dest, mode);
        if(of_deref) convert_assign(assignment(*of_deref, member_exprt{overflow_with_result, result_comps[1]}, w), dest, mode);
      } else {
        const auto type = signedbv_typet{w+1};
        const auto cast_a = typecast_exprt{cast_or_cut(a, a.type(), w), type};
        const auto cast_b = typecast_exprt{cast_or_cut(b, b.type(), w), type};
        exprt overflow_with_result = overflow_result_exprt{cast_a, op, cast_b};
        make_temp_symbol(overflow_with_result, "overflow_result", dest, mode);
        const struct_typet::componentst &result_comps =
          to_struct_type(overflow_with_result.type()).components();
        CHECK_RETURN(result_comps.size() == 2);
        if(dest_deref) convert_assign(assignment(*dest_deref, cast_or_cut(member_exprt{overflow_with_result, result_comps[0]}, dest_deref->type(), w), w), dest, mode);
        if(of_deref) convert_assign(assignment(*of_deref, or_exprt{member_exprt{overflow_with_result, result_comps[1]}, extractbit_exprt{member_exprt{overflow_with_result, result_comps[0]}, w}}, w), dest, mode);
      }
    } else {
      const auto wtype = std::min(std::max(std::max(width_a, width_b), width_dest), w);
      const auto type = signedbv_typet{wtype};
      const auto cast_a = typecast_exprt{cast_or_cut(a, a.type(), w), type};
      const auto cast_b = typecast_exprt{cast_or_cut(b, b.type(), w), type};
      if(dest_deref) convert_assign(assignment(*dest_deref, cast_or_cut(binary_exprt{cast_a, op, cast_b}, dest_deref->type(), w), w), dest, mode);
      if(of_deref) convert_assign(assignment(*of_deref, constant_exprt{"0", unsignedbv_typet{1}}, w), dest, mode);
    }
  }
}

void goto_convertt::remove_binary_bitwidth_overflow(
  binary_bitwidth_overflowt &expr,
  goto_programt &dest,
  bool result_is_used,
  const irep_idt &mode)
{
  clean_expr(expr.dest(), dest, mode, true);
  clean_expr(expr.of(), dest, mode, true);
  bool read_dest = expr.dest().type().id() == ID_pointer;
  bool read_of = expr.of().type().id() == ID_pointer;
  clean_expr(expr.a(), dest, mode, read_dest || read_of);
  clean_expr(expr.b(), dest, mode, read_dest || read_of);
  if(!read_dest && !read_of){
    expr.make_nil();
  } else {
    const auto type_a = expr.a().type();
    const auto type_b = expr.b().type();
    const auto w = expr.width();
    const optionalt<exprt> dest_deref = read_dest?optionalt<exprt>{dereference_exprt(expr.dest())}:optionalt<exprt>{};
    const optionalt<exprt> of_deref = read_of?optionalt<exprt>{dereference_exprt(expr.of())}:optionalt<exprt>{};

    if((type_a.id() == ID_bool || type_a.id() == ID_c_bool) &&
       (type_b.id() == ID_bool || type_b.id() == ID_c_bool)){
      const auto expr_a = cast_or_cut(expr.a(), bool_typet{}, w);
      const auto expr_b = cast_or_cut(expr.b(), bool_typet{}, w);
      binaryop_between_bools(expr_a, expr.op(), expr_b, dest_deref, of_deref, expr.width(), dest, mode);
      expr.make_nil();
      return;
    } else {
      binary_op_with_int(expr.a(), expr.op(), expr.b(), dest_deref, of_deref, expr.width(), dest, mode);
      expr.make_nil();
      return;
    }
  }
}

void goto_convertt::remove_overflow(
  side_effect_expr_overflowt &expr,
  goto_programt &dest,
  bool result_is_used,
  const irep_idt &mode)
{
  const irep_idt &statement = expr.get_statement();
  const exprt &lhs = expr.lhs();
  const exprt &rhs = expr.rhs();
  const exprt &result = expr.result();

  if(result.type().id() != ID_pointer)
  {
    // result of the arithmetic operation is _not_ used, just evaluate side
    // effects
    exprt tmp = result;
    clean_expr(tmp, dest, mode, false);

    // the is-there-an-overflow result may be used
    if(result_is_used)
    {
      binary_overflow_exprt overflow_check{
        typecast_exprt::conditional_cast(lhs, result.type()),
        statement,
        typecast_exprt::conditional_cast(rhs, result.type())};
      overflow_check.add_source_location() = expr.source_location();
      expr.swap(overflow_check);
    }
    else
      expr.make_nil();
  }
  else
  {
    const typet &arith_type = to_pointer_type(result.type()).base_type();
    irep_idt arithmetic_operation =
      statement == ID_overflow_plus
        ? ID_plus
        : statement == ID_overflow_minus
            ? ID_minus
            : statement == ID_overflow_mult ? ID_mult : ID_nil;
    CHECK_RETURN(arithmetic_operation != ID_nil);
    exprt overflow_with_result = overflow_result_exprt{
      typecast_exprt::conditional_cast(lhs, arith_type),
      arithmetic_operation,
      typecast_exprt::conditional_cast(rhs, arith_type)};
    overflow_with_result.add_source_location() = expr.source_location();

    if(result_is_used)
      make_temp_symbol(overflow_with_result, "overflow_result", dest, mode);

    const struct_typet::componentst &result_comps =
      to_struct_type(overflow_with_result.type()).components();
    CHECK_RETURN(result_comps.size() == 2);
    code_assignt result_assignment{
      dereference_exprt{result},
      typecast_exprt::conditional_cast(
        member_exprt{overflow_with_result, result_comps[0]}, arith_type),
      expr.source_location()};
    convert_assign(result_assignment, dest, mode);

    if(result_is_used)
    {
      member_exprt overflow_check{overflow_with_result, result_comps[1]};
      overflow_check.add_source_location() = expr.source_location();

      expr.swap(overflow_check);
    }
    else
      expr.make_nil();
  }
}

void goto_convertt::remove_side_effect(
  side_effect_exprt &expr,
  goto_programt &dest,
  const irep_idt &mode,
  bool result_is_used,
  bool address_taken)
{
  const irep_idt &statement=expr.get_statement();

  if(statement==ID_function_call)
    remove_function_call(
      to_side_effect_expr_function_call(expr), dest, mode, result_is_used);
  else if(statement==ID_assign ||
          statement==ID_assign_plus ||
          statement==ID_assign_minus ||
          statement==ID_assign_mult ||
          statement==ID_assign_div ||
          statement==ID_assign_bitor ||
          statement==ID_assign_bitxor ||
          statement==ID_assign_bitand ||
          statement==ID_assign_lshr ||
          statement==ID_assign_ashr ||
          statement==ID_assign_shl ||
          statement==ID_assign_mod)
    remove_assignment(expr, dest, result_is_used, address_taken, mode);
  else if(statement==ID_postincrement ||
          statement==ID_postdecrement)
    remove_post(expr, dest, mode, result_is_used);
  else if(statement==ID_preincrement ||
          statement==ID_predecrement)
    remove_pre(expr, dest, result_is_used, address_taken, mode);
  else if(statement==ID_cpp_new ||
          statement==ID_cpp_new_array)
    remove_cpp_new(expr, dest, result_is_used);
  else if(statement==ID_cpp_delete ||
          statement==ID_cpp_delete_array)
    remove_cpp_delete(expr, dest);
  else if(statement==ID_allocate)
    remove_malloc(expr, dest, mode, result_is_used);
  else if(statement==ID_temporary_object)
    remove_temporary_object(expr, dest);
  else if(statement==ID_statement_expression)
    remove_statement_expression(expr, dest, mode, result_is_used);
  else if(statement==ID_nondet)
  {
    // these are fine
  }
  else if(statement==ID_skip)
  {
    expr.make_nil();
  }
  else if(statement==ID_throw)
  {
    codet code = code_expressiont(side_effect_expr_throwt(
      expr.find(ID_exception_list), expr.type(), expr.source_location()));
    code.op0().operands().swap(expr.operands());
    code.add_source_location() = expr.source_location();
    dest.add(goto_programt::instructiont(
      std::move(code), expr.source_location(), THROW, nil_exprt(), {}));

    // the result can't be used, these are void
    expr.make_nil();
  }
  else if(
    statement == ID_overflow_plus || statement == ID_overflow_minus ||
    statement == ID_overflow_mult)
  {
    remove_overflow(
      to_side_effect_expr_overflow(expr), dest, result_is_used, mode);
  }
  else if(statement == ID_binary_bitwidth_overflow)
  {
    remove_binary_bitwidth_overflow(
      to_binary_bitwidth_overflow(expr), dest, result_is_used, mode);
  }
  else
  {
    UNREACHABLE;
  }
}
