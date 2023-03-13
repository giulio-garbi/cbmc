/*******************************************************************\

Module: Symex Operations-With-Overflow Instrumentation

           Author: Giulio Garbi

\*******************************************************************/

/// \file
/// Symex Operations-With-Overflow Instrumentation

#include "arith_tools.h"
#include "bitvector_expr.h"
#include "bitvector_types.h"
#include "byte_operators.h"
#include "c_types.h"
#include "expr_util.h"
#include "fresh_symbol.h"
#include "goto_symex.h"
#include "symex_shadow_memory_util.h"

// Get the new_type.get_width() LSBs of x. If x is shorter, add a cast so as
// there are enough bits.
exprt cut_bit_representation(const exprt& x, const integer_bitvector_typet& new_type){
  PRECONDITION(is_signed_or_unsigned_bitvector(x.type()));
  if(to_bitvector_type(x.type()).get_width() > new_type.get_width()){
    return extractbits_exprt{x, new_type.get_width()-1, 0, new_type};
  } else {
    return typecast_exprt(x, new_type);
  }
}

// Compute the type of the operation a OP b according to C semantics. The
// returned type has width bits.
integer_bitvector_typet compute_binary_op_type(const exprt& a, const exprt& b, const std::size_t width){
  const auto a_type = to_integer_bitvector_type(a.type());
  const auto b_type = to_integer_bitvector_type(b.type());

  // are the types signed?
  const auto a_sign = a_type.smallest().is_negative();
  const auto b_sign = b_type.smallest().is_negative();

  bool c_sign;
  if(a_sign == b_sign) {
    c_sign = a_sign;
  } else if(!a_sign && a_type.get_width() >= b_type.get_width()){
    c_sign = false;
  } else if(!b_sign && b_type.get_width() >= a_type.get_width()){
    c_sign = false;
  } else if(!a_sign && b_type.get_width() >= a_type.get_width()+1){
    c_sign = true;
  } else if(!b_sign && a_type.get_width() >= b_type.get_width()+1){
    c_sign = true;
  } else {
    c_sign = false;
  }

  if(c_sign){
    return signedbv_typet(width);
  } else {
    return unsignedbv_typet(width);
  }
}

void check_destination_ref(const exprt &dest){
  typet dest_type = dest.type();
  DATA_INVARIANT_WITH_DIAGNOSTICS(
    dest.id() == ID_pointer,
    "destination requires a pointer expression",
    irep_pretty_diagnosticst{dest_type});
}

void check_destination_deref(const exprt &c_deref){
  DATA_INVARIANT_WITH_DIAGNOSTICS(
    is_assignable(c_deref),
    "destination requires a pointer to an assignable",
    irep_pretty_diagnosticst{c_deref});
}

void check_overflow_ref(const exprt &of){
  typet of_type = of.type();
  DATA_INVARIANT_WITH_DIAGNOSTICS(
    of_type.id() == ID_pointer,
    "overflow requires a pointer expression",
    irep_pretty_diagnosticst{of_type});
}

void check_overflow_deref(const exprt &o_deref){
  DATA_INVARIANT_WITH_DIAGNOSTICS(
    is_assignable(o_deref),
    "overflow requires a pointer to an assignable",
    irep_pretty_diagnosticst{o_deref});
}

void check_width(const exprt &w){
  DATA_INVARIANT_WITH_DIAGNOSTICS(
    w.id() == ID_constant,
    "bitwidth must be an integer constant",
    irep_pretty_diagnosticst{w});
}

void check_destination_ref_overflow_ref_width
  (const exprt &dest, const exprt &of, const exprt &w){
  check_destination_ref(dest);
  check_overflow_ref(of);
  check_width(w);
}

void goto_symext::symex_binary_op_bits(
  goto_symex_statet &state,
  irep_idt operand,
  const exprt::operandst &arguments)
{
  INVARIANT(
    operand == ID_plus || operand == ID_minus || operand == ID_mult ||
      operand == ID_shl || operand == ID_div,
    "symex_add_sub_mul_shl_bits only supports binary +, -, *, <<, /");

  // parse set_field call
  INVARIANT(
    arguments.size() == 5, CPROVER_PREFIX "this operation requires 5 arguments");

  const exprt& a = arguments[0];
  const exprt& b = arguments[1];
  const exprt& c = arguments[2];
  const exprt& o = arguments[3];
  const exprt& w = arguments[4];

  check_destination_ref_overflow_ref_width(c, o, w);

  mp_integer w_mpint;
  to_integer(to_constant_expr(w), w_mpint);
  std::size_t w_ = w_mpint.to_long();


  // get the symbol to write on
  const auto c_deref = deref_expr(c);
  check_destination_deref(c_deref);

  // get the overflow bit
  const auto o_deref = deref_expr(o);
  check_overflow_deref(o_deref);

  const auto bvtype = compute_binary_op_type(a, b, w_);
  const auto a_bits = cut_bit_representation(a, bvtype);
  const auto b_bits = cut_bit_representation(b, bvtype);
  if(operand == ID_div){

    if(to_integer_bitvector_type(bvtype).smallest() < 0){
      symex_assign(
        state,
        o_deref,
        make_byte_update(
          o_deref,
          from_integer(0, c_index_type()),
          and_exprt{
            equal_exprt{a_bits, from_integer(bvtype.largest(), bvtype)},
            equal_exprt{b_bits, from_integer(-1, bvtype)}
          }),
        false);
    } else {
      symex_assign(
        state,
        o_deref,
        make_byte_update(
          o_deref,
          from_integer(0, c_index_type()),
          from_integer(0, unsignedbv_typet(1))),
        false);
    }
    symex_assign(
      state,
      c_deref,
      make_byte_update(
        c_deref,
        from_integer(0, c_index_type()),
        div_exprt{a_bits, b_bits}),
      false);
  } else {
    exprt overflow_with_result = overflow_result_exprt{a_bits, operand, b_bits};
    overflow_with_result.add_source_location() =
      state.source.pc->source_location();
    const struct_typet::componentst &result_comps =
      to_struct_type(overflow_with_result.type()).components();
    symex_assign(
      state,
      c_deref,
      make_byte_update(
        c_deref,
        from_integer(0, c_index_type()),
        member_exprt{overflow_with_result, result_comps[0]}),
      false);
    symex_assign(
      state,
      o_deref,
      make_byte_update(
        o_deref,
        from_integer(0, c_index_type()),
        member_exprt{overflow_with_result, result_comps[1]}),
      false);
  }
}

void goto_symext::symex_add_bits(
  goto_symex_statet &state,
  const exprt::operandst &arguments)
{
  symex_binary_op_bits(state, ID_plus, arguments);
}

void goto_symext::symex_sub_bits(
  goto_symex_statet &state,
  const exprt::operandst &arguments)
{
  symex_binary_op_bits(state, ID_minus, arguments);
}

void goto_symext::symex_mult_bits(
  goto_symex_statet &state,
  const exprt::operandst &arguments)
{
  symex_binary_op_bits(state, ID_mult, arguments);
}

void goto_symext::symex_shl_bits(
  goto_symex_statet &state,
  const exprt::operandst &arguments)
{
  symex_binary_op_bits(state, ID_shl, arguments);
}

void goto_symext::symex_div_bits(
  goto_symex_statet &state,
  const exprt::operandst &arguments)
{
  symex_binary_op_bits(state, ID_div, arguments);
}

void goto_symext::symex_unary_minus_bits(
  goto_symex_statet &state,
  const exprt::operandst &arguments)
{
  // parse set_field call
  INVARIANT(
    arguments.size() == 4, CPROVER_PREFIX "this operation requires 4 arguments");

  const exprt& a = arguments[0];
  const exprt& c = arguments[1];
  const exprt& o = arguments[2];
  const exprt& w = arguments[3];
  check_destination_ref_overflow_ref_width(c, o, w);

  mp_integer w_mpint;
  to_integer(to_constant_expr(w), w_mpint);
  std::size_t w_ = w_mpint.to_long();

  // get the symbol to write on
  const auto c_deref = deref_expr(c);
  check_destination_deref(c_deref);

  // get the overflow bit
  const auto o_deref = deref_expr(o);
  check_overflow_deref(o_deref);

  const auto a_bits = cut_bit_representation(a, signedbv_typet(w_));
  exprt overflow_with_result = overflow_result_exprt{a_bits, ID_unary_minus};
  overflow_with_result.add_source_location() =
    state.source.pc->source_location();
  const struct_typet::componentst &result_comps =
    to_struct_type(overflow_with_result.type()).components();
  symex_assign(
    state,
    c_deref,
    make_byte_update(
      c_deref,
      from_integer(0, c_index_type()),
      member_exprt{overflow_with_result, result_comps[0]}),
    false);
  symex_assign(
    state,
    o_deref,
    make_byte_update(
      o_deref,
      from_integer(0, c_index_type()),
      member_exprt{overflow_with_result, result_comps[1]}),
    false);
}

void goto_symext::symex_assign_bits(
  goto_symex_statet &state,
  const exprt::operandst &arguments)
{
  // parse set_field call
  INVARIANT(
    arguments.size() == 3, CPROVER_PREFIX "this operation requires 3 arguments");

  const exprt& a = arguments[0];
  const exprt& c = arguments[1];
  const exprt& w = arguments[2];
  check_destination_ref(c);
  check_width(w);

  mp_integer w_mpint;
  to_integer(to_constant_expr(w), w_mpint);
  std::size_t w_ = w_mpint.to_long();

  // get the symbol to write on
  const auto c_deref = deref_expr(c);
  check_destination_deref(c_deref);

  const auto a_bits = cut_bit_representation(a, signedbv_typet(w_));
  symex_assign(
    state,
    c_deref,
    make_byte_update(
      c_deref,
      from_integer(0, c_index_type()),
      a_bits),
    false);
}

void goto_symext::symex_binary_op_bits_no_overflow(
  goto_symex_statet &state,
  irep_idt operand,
  const exprt::operandst &arguments)
{
  // parse set_field call
  INVARIANT(
    arguments.size() == 4, CPROVER_PREFIX "this operation requires 4 arguments");

  const exprt& a = arguments[0];
  const exprt& b = arguments[1];
  const exprt& c = arguments[2];
  const exprt& w = arguments[3];

  check_destination_ref(c);
  check_width(w);

  mp_integer w_mpint;
  to_integer(to_constant_expr(w), w_mpint);
  std::size_t w_ = w_mpint.to_long();


  // get the symbol to write on
  const auto c_deref = deref_expr(c);
  check_destination_deref(c_deref);

  const auto bvtype = compute_binary_op_type(a, b, w_);
  const auto a_bits = cut_bit_representation(a, bvtype);
  const auto b_bits = cut_bit_representation(b, bvtype);
  {
    exprt operation = binary_exprt{a_bits, operand, b_bits};
    symex_assign(
      state,
      c_deref,
      make_byte_update(
        c_deref,
        from_integer(0, c_index_type()),
        binary_exprt{a_bits, operand, b_bits}),
      false);
  }
}