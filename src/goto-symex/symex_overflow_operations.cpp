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
  if(x.type().id() == ID_bool)
    return x;
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

integer_bitvector_typet compute_unary_op_type(const exprt& a, const std::size_t width){
  const auto a_type = to_integer_bitvector_type(a.type());

  // is the type signed?
  const auto a_sign = a_type.smallest().is_negative();

  if(a_sign){
    return signedbv_typet(width);
  } else {
    return unsignedbv_typet(width);
  }
}

void check_destination_ref(const exprt &dest){
  typet dest_type = dest.type();
  DATA_INVARIANT_WITH_DIAGNOSTICS(
    dest_type.id() == ID_pointer || dest_type.id() == ID_address_of,
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
    of_type.id() == ID_pointer || of_type.id() == ID_address_of,
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

void goto_symext::symex_add_sub_with_overflow(goto_symex_statet &state,
  const exprt &a_bits, irep_idt operand, const exprt &b_bits,
  const exprt& c_deref, const exprt& o_deref,
  const integer_bitvector_typet& original_type,
  const integer_bitvector_typet& abstract_type){
  if(abstract_type.get_width() < original_type.get_width())
  {
    exprt overflow_with_result = overflow_result_exprt{a_bits, operand, b_bits};
    overflow_with_result.add_source_location() =
      state.source.pc->source_location();
    const struct_typet::componentst &result_comps =
      to_struct_type(overflow_with_result.type()).components();
    auto const &helper_symbol = get_fresh_aux_symbol(
                                  overflow_with_result.type(),
                                  "symex",
                                  "binary_op_bits_helper",
                                  overflow_with_result.source_location(),
                                  language_mode,
                                  ns,
                                  state.symbol_table)
                                  .symbol_expr();
    symex_assign(state, helper_symbol, overflow_with_result, false);
    symex_assign(
      state,
      c_deref,
      make_byte_update(
        c_deref,
        from_integer(0, c_index_type()),
        member_exprt{helper_symbol, result_comps[0]}),
      false);
    symex_assign(
      state,
      o_deref,
      make_byte_update(
        o_deref,
        from_integer(0, c_index_type()),
        extractbit_exprt{member_exprt{helper_symbol, result_comps[1]}, 0}),
      false);
  } else {
    symex_assign(
      state,
      c_deref,
      binary_exprt{a_bits, operand, b_bits},
      false);
    symex_assign(
      state,
      o_deref,
      from_integer(0, o_deref.type()),
      false);
  }
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

  PRECONDITION(type_try_dynamic_cast<integer_bitvector_typet>(c_deref.type()));
  const auto c_deref_type = to_integer_bitvector_type(c_deref.type());
  const auto bvtype = compute_binary_op_type(a, b, w_);

  if(c_deref_type.get_width() <= w_ || (operand == ID_div && to_integer_bitvector_type(bvtype).smallest() >= 0)){
    symex_binary_op_bits_no_overflow(state, operand, {a,b,c,w});
    symex_assign(
      state,
      o_deref,
      make_byte_update(
        o_deref,
        from_integer(0, c_index_type()),
        from_integer(0, o_deref.type())),
      false);
    return;
  }

  const auto a_bits = cut_bit_representation(a, bvtype);
  const auto b_bits = cut_bit_representation(b, bvtype);
  if(operand == ID_plus || operand == ID_minus){
    symex_add_sub_with_overflow(state, a_bits, operand, b_bits, c_deref, o_deref, c_deref_type, bvtype);
  }
  else if(operand == ID_div){
    symex_assign(
      state,
      o_deref,
      typecast_exprt(
        and_exprt{
          equal_exprt{a_bits, bvtype.smallest_expr()},
          equal_exprt{b_bits, from_integer(-1, bvtype)}
        }, o_deref.type()),
      false);
    symex_assign(
      state,
      c_deref,
      make_byte_update(
        c_deref,
        from_integer(0, c_index_type()),
        div_exprt{a_bits, b_bits}),
      false);
  } else {
    auto overflow_with_result = overflow_result_exprt{a_bits, operand, b_bits};
    overflow_with_result.add_source_location() =
      state.source.pc->source_location();
    const struct_typet::componentst &result_comps =
      to_struct_type(overflow_with_result.type()).components();
    auto const &helper_symbol = get_fresh_aux_symbol(
      overflow_with_result.type(),
      "symex",
      "binary_op_bits_helper",
      overflow_with_result.source_location(),
      language_mode,
      ns,
      state.symbol_table).symbol_expr();
    symex_assign(
      state,
      helper_symbol,
      overflow_with_result,
      false);
    symex_assign(
      state,
      c_deref,
      make_byte_update(
        c_deref,
        from_integer(0, c_index_type()),
        cut_bit_representation(member_exprt{helper_symbol, result_comps[0]}, bvtype)),
      false);
    symex_assign(
      state,
      o_deref,
      make_byte_update(
        o_deref,
        from_integer(0, c_index_type()),
        extractbit_exprt{member_exprt{helper_symbol, result_comps[1]}, 0}),
      false);
  }
}

void goto_symext::symex_binary_op_overflow_only(
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
    arguments.size() == 4, CPROVER_PREFIX "this operation requires 4 arguments");

  const exprt& a = arguments[0];
  const exprt& b = arguments[1];
  const exprt& o = arguments[2];
  const exprt& w = arguments[3];

  check_overflow_ref(o);
  check_width(w);

  mp_integer w_mpint;
  to_integer(to_constant_expr(w), w_mpint);
  std::size_t w_ = w_mpint.to_long();

  // get the overflow bit
  const auto o_deref = deref_expr(o);
  check_overflow_deref(o_deref);

  const auto bvtype = compute_binary_op_type(a, b, w_);

  if((operand == ID_div && to_integer_bitvector_type(bvtype).smallest() >= 0)){
    symex_assign(
      state,
      o_deref,
      make_byte_update(
        o_deref,
        from_integer(0, c_index_type()),
        from_integer(0, o_deref.type())),
      false);
    return;
  }

  const auto a_bits = cut_bit_representation(a, bvtype);
  const auto b_bits = cut_bit_representation(b, bvtype);
  if(operand == ID_plus){
    symex_assign(
      state,
      o_deref,
      make_byte_update(
        o_deref,
        from_integer(0, c_index_type()),
        extractbit_exprt{plus_overflow_exprt{a_bits, b_bits}, 0}),
      false);
  }
  else if(operand == ID_minus){
    symex_assign(
      state,
      o_deref,
      make_byte_update(
        o_deref,
        from_integer(0, c_index_type()),
        extractbit_exprt{minus_overflow_exprt{a_bits, b_bits}, 0}),
      false);
  }
  else if(operand == ID_mult){
    symex_assign(
      state,
      o_deref,
      make_byte_update(
        o_deref,
        from_integer(0, c_index_type()),
        extractbit_exprt{mult_overflow_exprt{a_bits, b_bits}, 0}),
      false);
  }
  else if(operand == ID_shl){
    symex_assign(
      state,
      o_deref,
      make_byte_update(
        o_deref,
        from_integer(0, c_index_type()),
        extractbit_exprt{shl_overflow_exprt{a_bits, b_bits}, 0}),
      false);
  }
  else if(operand == ID_div){
    symex_assign(
      state,
      o_deref,
      typecast_exprt(
        and_exprt{
          equal_exprt{a_bits, bvtype.smallest_expr()},
          equal_exprt{b_bits, from_integer(-1, bvtype)}
        }, o_deref.type()),
      false);
  }
  else{
    UNREACHABLE;
  }
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

  const auto c_deref_type = to_integer_bitvector_type(c_deref.type());

  if(w_ < c_deref_type.get_width())
  {
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
  } else {
    const auto a_bits = cut_bit_representation(a, c_deref_type);
    symex_assign(
      state,
      c_deref,
      unary_minus_exprt{a_bits},
      false);
    symex_assign(
      state,
      o_deref,
      from_integer(0, o_deref.type()),
      false);
  }
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
  if(c_deref.type().id() == ID_bool || c_deref.type().id() == ID_c_bool){
    symex_assign(
      state,
      c_deref,
      typecast_exprt{a, c_deref.type()},
      false);
  }
  else
  {
    const auto c_deref_type = to_integer_bitvector_type(c_deref.type());
    if(w_ < c_deref_type.get_width())
    {
      const auto bvtype = compute_unary_op_type(c_deref, w_);
      const auto a_bits = cut_bit_representation(a, bvtype);
      symex_assign(
        state,
        c_deref,
        make_byte_update(c_deref, from_integer(0, c_index_type()), a_bits),
        false);
    }
    else
    {
      const auto a_bits = cut_bit_representation(a, c_deref_type);
      symex_assign(
        state,
        c_deref,
        make_byte_update(c_deref, from_integer(0, c_index_type()), a_bits),
        false);
    }
  }
}

void goto_symext::symex_nz_bits(
  const exprt &lhs,
  goto_symex_statet &state,
  const exprt::operandst &arguments)
{
  // parse set_field call
  INVARIANT(
    arguments.size() == 2, CPROVER_PREFIX "this operation requires 2 arguments");

  const exprt& a = arguments[0];
  const exprt& w = arguments[1];
  check_width(w);

  mp_integer w_mpint;
  to_integer(to_constant_expr(w), w_mpint);
  std::size_t w_ = w_mpint.to_long();

  const auto a_type = to_integer_bitvector_type(a.type());

  if(w_ < a_type.get_width()){
    const auto bvtype = compute_unary_op_type(lhs, w_);
    symex_assign(
      state,
      lhs,
      typecast_exprt{
      notequal_exprt{
        cut_bit_representation(a, bvtype),
        from_integer(0, bvtype)}, lhs.type()},
      false);
  } else {
    symex_assign(
      state,
      lhs,
      typecast_exprt{
        notequal_exprt{
          a,
          from_integer(0, a_type)}, lhs.type()},
      false);
  }
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

  const bool is_ashr = operand == ID_ashr;

  const auto bvtype = is_ashr?signedbv_typet{w_}:compute_binary_op_type(a, b, w_);
  const auto a_bits = (is_ashr?typecast_exprt{cut_bit_representation(a, bvtype), bvtype}:cut_bit_representation(a, bvtype));
  const auto b_bits = (is_ashr?typecast_exprt{cut_bit_representation(b, bvtype), bvtype}:cut_bit_representation(b, bvtype));

  {
    const auto c_deref_type = to_integer_bitvector_type(c_deref.type());
    if(w_ < c_deref_type.get_width())
    {
      symex_assign(
        state,
        c_deref,
        make_byte_update(
          c_deref,
          from_integer(0, c_index_type()),
          binary_exprt{a_bits, operand, b_bits}),
        false);
    }
    else
    {
      symex_assign(
        state,
        c_deref,
        typecast_exprt{binary_exprt{a_bits, operand, b_bits}, c_deref_type},
        false);
    }
  }
}

exprt make_bool(const exprt &a, size_t w_){
  if(a.type().id() == ID_bool){
    return a;
  } else if (a.type().id() == ID_c_bool){
    return typecast_exprt{extractbit_exprt{a,0}, bool_typet{}};
  } else {
    return typecast_exprt{cut_bit_representation(a, compute_unary_op_type(a, w_)), bool_typet{}};
  }
}

void goto_symext::symex_comparison_op_bits(
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

  const auto c_deref_type = to_integer_bitvector_type(c_deref.type());

  if(a.type().id() == ID_bool || b.type().id() == ID_bool || a.type().id() == ID_c_bool || b.type().id() == ID_c_bool){
    const auto bvtype = compute_unary_op_type(c_deref, w_);
    symex_assign(
      state,
      c_deref,
      make_byte_update(
        c_deref,
        from_integer(0, c_index_type()),
        typecast_exprt{binary_relation_exprt{make_bool(a, w_), operand, make_bool(b, w_)}, bvtype}),
      false);
  }
  else
  {
    const auto bvtype = compute_binary_op_type(a, b, w_);
    const auto a_bits = cut_bit_representation(a, bvtype);
    const auto b_bits = cut_bit_representation(b, bvtype);
    if(w_ < c_deref_type.get_width())
    {
      symex_assign(
        state,
        c_deref,
        make_byte_update(
          c_deref,
          from_integer(0, c_index_type()),
          typecast_exprt{
            binary_relation_exprt{a_bits, operand, b_bits}, bvtype}),
        false);
    }
    else
    {
      symex_assign(
        state,
        c_deref,
        typecast_exprt{
          binary_relation_exprt{a_bits, operand, b_bits}, c_deref_type},
        false);
    }
  }
}


void goto_symext::symex_unary_op_bits_no_overflow(
  goto_symex_statet &state,
  irep_idt operand,
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

  const auto c_deref_type = to_integer_bitvector_type(c_deref.type());

  if(w_ < c_deref_type.get_width()){
    const auto bvtype = w_ < c_deref_type.get_width() ? compute_unary_op_type(c_deref, w_) : c_deref_type;
    const auto a_bits = cut_bit_representation(a, bvtype);
    symex_assign(
      state,
      c_deref,
      make_byte_update(
        c_deref,
        from_integer(0, c_index_type()),
        unary_exprt{operand, a_bits}),
      false);
  } else {
    const auto a_bits = cut_bit_representation(a, c_deref_type);
    symex_assign(
      state,
      c_deref,
      unary_exprt{operand, a_bits},
      false);
  }
}