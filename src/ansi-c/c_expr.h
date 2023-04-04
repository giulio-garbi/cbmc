/*******************************************************************\

Module: API to expression classes that are internal to the C frontend

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_C_EXPR_H
#define CPROVER_ANSI_C_C_EXPR_H

/// \file ansi-c/c_expr.h
/// API to expression classes that are internal to the C frontend

#include <util/std_code.h>

#include <util/bitvector_types.h>

#include <string>
#include <utility>

/// \brief Shuffle elements of one or two vectors, modelled after Clang's
/// __builtin_shufflevector.
class shuffle_vector_exprt : public multi_ary_exprt
{
public:
  shuffle_vector_exprt(
    exprt vector1,
    optionalt<exprt> vector2,
    exprt::operandst indices);

  const vector_typet &type() const
  {
    return static_cast<const vector_typet &>(multi_ary_exprt::type());
  }

  vector_typet &type()
  {
    return static_cast<vector_typet &>(multi_ary_exprt::type());
  }

  const exprt &vector1() const
  {
    return op0();
  }

  exprt &vector1()
  {
    return op0();
  }

  const exprt &vector2() const
  {
    return op1();
  }

  exprt &vector2()
  {
    return op1();
  }

  bool has_two_input_vectors() const
  {
    return vector2().is_not_nil();
  }

  const exprt::operandst &indices() const
  {
    return op2().operands();
  }

  exprt::operandst &indices()
  {
    return op2().operands();
  }

  vector_exprt lower() const;
};

template <>
inline bool can_cast_expr<shuffle_vector_exprt>(const exprt &base)
{
  return base.id() == ID_shuffle_vector;
}

inline void validate_expr(const shuffle_vector_exprt &value)
{
  validate_operands(value, 3, "shuffle_vector must have three operands");
}

/// \brief Cast an exprt to a \ref shuffle_vector_exprt
///
/// \a expr must be known to be \ref shuffle_vector_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref shuffle_vector_exprt
inline const shuffle_vector_exprt &to_shuffle_vector_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_shuffle_vector);
  const shuffle_vector_exprt &ret =
    static_cast<const shuffle_vector_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_shuffle_vector_expr(const exprt &)
inline shuffle_vector_exprt &to_shuffle_vector_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_shuffle_vector);
  shuffle_vector_exprt &ret = static_cast<shuffle_vector_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief A Boolean expression returning true, iff the result of performing
/// operation \c kind on operands \c a and \c b in infinite-precision arithmetic
/// cannot be represented in the type of the object that \c result points to (or
/// the type of \c result, if it is not a pointer).
/// If \c result is a pointer, the result of the operation is stored in the
/// object pointed to by \c result.
class side_effect_expr_overflowt : public side_effect_exprt
{
public:
  side_effect_expr_overflowt(
    const irep_idt &kind,
    exprt _lhs,
    exprt _rhs,
    exprt _result,
    const source_locationt &loc)
    : side_effect_exprt(
        "overflow-" + id2string(kind),
        {std::move(_lhs), std::move(_rhs), std::move(_result)},
        bool_typet{},
        loc)
  {
  }

  exprt &lhs()
  {
    return op0();
  }

  const exprt &lhs() const
  {
    return op0();
  }

  exprt &rhs()
  {
    return op1();
  }

  const exprt &rhs() const
  {
    return op1();
  }

  exprt &result()
  {
    return op2();
  }

  const exprt &result() const
  {
    return op2();
  }
};

template <>
inline bool can_cast_expr<side_effect_expr_overflowt>(const exprt &base)
{
  if(base.id() != ID_side_effect)
    return false;

  const irep_idt &statement = to_side_effect_expr(base).get_statement();
  return statement == ID_overflow_plus || statement == ID_overflow_mult ||
         statement == ID_overflow_minus;
}

/// \brief Cast an exprt to a \ref side_effect_expr_overflowt
///
/// \a expr must be known to be \ref side_effect_expr_overflowt.
///
/// \param expr: Source expression
/// \return Object of type \ref side_effect_expr_overflowt
inline const side_effect_expr_overflowt &
to_side_effect_expr_overflow(const exprt &expr)
{
  const auto &side_effect_expr = to_side_effect_expr(expr);
  PRECONDITION(
    side_effect_expr.get_statement() == ID_overflow_plus ||
    side_effect_expr.get_statement() == ID_overflow_mult ||
    side_effect_expr.get_statement() == ID_overflow_minus);
  return static_cast<const side_effect_expr_overflowt &>(side_effect_expr);
}

/// \copydoc to_side_effect_expr_overflow(const exprt &)
inline side_effect_expr_overflowt &to_side_effect_expr_overflow(exprt &expr)
{
  auto &side_effect_expr = to_side_effect_expr(expr);
  PRECONDITION(
    side_effect_expr.get_statement() == ID_overflow_plus ||
    side_effect_expr.get_statement() == ID_overflow_mult ||
    side_effect_expr.get_statement() == ID_overflow_minus);
  return static_cast<side_effect_expr_overflowt &>(side_effect_expr);
}


/// \brief A function call that sets \c *of to true iff the result of performing
/// operation \c op on operands \c a and \c b lowest \c w bits in
/// infinite-precision arithmetic exceeds \c w bits. The result of the operation
/// is stored in the object pointed to by \c dest.
class binary_bitwidth_overflowt : public side_effect_exprt
{
public:
  binary_bitwidth_overflowt(
    const irep_idt &op,
    exprt a,
    exprt b,
    exprt dest,
    exprt of,
    const irep_idt &w,
    const source_locationt &loc)
    : side_effect_exprt(
        ID_binary_bitwidth_overflow,
        {std::move(a), std::move(b), std::move(dest), std::move(of)},
        empty_typet{},
        loc)
  {
    set(ID_operator, op);
    set(ID_width, w);
  }

  exprt &a()
  {
    return op0();
  }

  const exprt &a() const
  {
    return op0();
  }

  exprt &b()
  {
    return op1();
  }

  const exprt &b() const
  {
    return op1();
  }

  exprt &dest()
  {
    return op2();
  }

  const exprt &dest() const
  {
    return op2();
  }

  exprt &of()
  {
    return op3();
  }

  const exprt &of() const
  {
    return op3();
  }

  size_t width()
  {
    return stoi(id2string(get(ID_width)));
  }

  const irep_idt &op() const
  {
    return get(ID_operator);
  }
};

template <>
inline bool can_cast_expr<binary_bitwidth_overflowt>(const exprt &base)
{
  if(base.id() != ID_side_effect)
    return false;

  const irep_idt &statement = to_side_effect_expr(base).get_statement();
  return statement == ID_binary_bitwidth_overflow;
}

/// \brief Cast an exprt to a \ref binary_bitwidth_overflowt
///
/// \a expr must be known to be \ref binary_bitwidth_overflowt.
///
/// \param expr: Source expression
/// \return Object of type \ref binary_bitwidth_overflowt
inline const binary_bitwidth_overflowt &
to_binary_bitwidth_overflow(const exprt &expr)
{
  const auto &side_effect_expr = to_side_effect_expr(expr);
  PRECONDITION(
    side_effect_expr.get_statement() == ID_binary_bitwidth_overflow);
  return static_cast<const binary_bitwidth_overflowt &>(side_effect_expr);
}

/// \copydoc to_binary_bitwidth_overflow(const exprt &)
inline binary_bitwidth_overflowt &to_binary_bitwidth_overflow(exprt &expr)
{
  auto &side_effect_expr = to_side_effect_expr(expr);
  PRECONDITION(
    side_effect_expr.get_statement() == ID_binary_bitwidth_overflow);
  return static_cast<binary_bitwidth_overflowt &>(side_effect_expr);
}

class unary_bitwidth_overflowt : public side_effect_exprt
{
public:
  unary_bitwidth_overflowt(
    const irep_idt &op,
    exprt a,
    exprt dest,
    exprt of,
    const irep_idt &w,
    const source_locationt &loc)
    : side_effect_exprt(
        ID_unary_bitwidth_overflow,
        {std::move(a), std::move(dest), std::move(of)},
        empty_typet{},
        loc)
  {
    set(ID_operator, op);
    set(ID_width, w);
  }

  exprt &a()
  {
    return op0();
  }

  const exprt &a() const
  {
    return op0();
  }

  exprt &dest()
  {
    return op1();
  }

  const exprt &dest() const
  {
    return op1();
  }

  exprt &of()
  {
    return op2();
  }

  const exprt &of() const
  {
    return op2();
  }

  size_t width()
  {
    return stoi(id2string(get(ID_width)));
  }

  const irep_idt &op() const
  {
    return get(ID_operator);
  }
};

template <>
inline bool can_cast_expr<unary_bitwidth_overflowt>(const exprt &base)
{
  if(base.id() != ID_side_effect)
    return false;

  const irep_idt &statement = to_side_effect_expr(base).get_statement();
  return statement == ID_unary_bitwidth_overflow;
}

/// \brief Cast an exprt to a \ref unary_bitwidth_overflowt
///
/// \a expr must be known to be \ref unary_bitwidth_overflowt.
///
/// \param expr: Source expression
/// \return Object of type \ref unary_bitwidth_overflowt
inline const unary_bitwidth_overflowt &
to_unary_bitwidth_overflow(const exprt &expr)
{
  const auto &side_effect_expr = to_side_effect_expr(expr);
  PRECONDITION(
    side_effect_expr.get_statement() == ID_unary_bitwidth_overflow);
  return static_cast<const unary_bitwidth_overflowt &>(side_effect_expr);
}

/// \copydoc to_unary_bitwidth_overflow(const exprt &)
inline unary_bitwidth_overflowt &to_unary_bitwidth_overflow(exprt &expr)
{
  auto &side_effect_expr = to_side_effect_expr(expr);
  PRECONDITION(
    side_effect_expr.get_statement() == ID_unary_bitwidth_overflow);
  return static_cast<unary_bitwidth_overflowt &>(side_effect_expr);
}

class assign_bitwidtht : public side_effect_exprt
{
public:
  assign_bitwidtht(
    exprt a,
    exprt dest,
    const irep_idt &w,
    const source_locationt &loc)
    : side_effect_exprt(
        ID_assign_bitwidth,
        {std::move(a), std::move(dest)},
        empty_typet{},
        loc)
  {
    set(ID_width, w);
  }

  exprt &a()
  {
    return op0();
  }

  const exprt &a() const
  {
    return op0();
  }

  exprt &dest()
  {
    return op1();
  }

  const exprt &dest() const
  {
    return op1();
  }

  size_t width()
  {
    return stoi(id2string(get(ID_width)));
  }

  const irep_idt &op() const
  {
    return get(ID_operator);
  }
};

template <>
inline bool can_cast_expr<assign_bitwidtht>(const exprt &base)
{
  if(base.id() != ID_side_effect)
    return false;

  const irep_idt &statement = to_side_effect_expr(base).get_statement();
  return statement == ID_assign_bitwidth;
}

/// \brief Cast an exprt to a \ref assign_bitwidtht
///
/// \a expr must be known to be \ref assign_bitwidtht.
///
/// \param expr: Source expression
/// \return Object of type \ref assign_bitwidtht
inline const assign_bitwidtht &
to_assign_bitwidth(const exprt &expr)
{
  const auto &side_effect_expr = to_side_effect_expr(expr);
  PRECONDITION(
    side_effect_expr.get_statement() == ID_assign_bitwidth);
  return static_cast<const assign_bitwidtht &>(side_effect_expr);
}

/// \copydoc to_assign_bitwidth(const exprt &)
inline assign_bitwidtht &to_assign_bitwidth(exprt &expr)
{
  auto &side_effect_expr = to_side_effect_expr(expr);
  PRECONDITION(
    side_effect_expr.get_statement() == ID_assign_bitwidth);
  return static_cast<assign_bitwidtht &>(side_effect_expr);
}

class nz_bitwidtht : public side_effect_exprt
{
public:
  nz_bitwidtht(
    exprt a,
    const irep_idt &w,
    const source_locationt &loc)
    : side_effect_exprt(
        ID_nz_bitwidth,
        {std::move(a)},
        bool_typet{},
        loc)
  {
    set(ID_width, w);
  }

  exprt &a()
  {
    return op0();
  }

  const exprt &a() const
  {
    return op0();
  }

  size_t width()
  {
    return stoi(id2string(get(ID_width)));
  }

  const irep_idt &op() const
  {
    return get(ID_operator);
  }
};

template <>
inline bool can_cast_expr<nz_bitwidtht>(const exprt &base)
{
  if(base.id() != ID_side_effect)
    return false;

  const irep_idt &statement = to_side_effect_expr(base).get_statement();
  return statement == ID_nz_bitwidth;
}

/// \brief Cast an exprt to a \ref nz_bitwidtht
///
/// \a expr must be known to be \ref nz_bitwidtht.
///
/// \param expr: Source expression
/// \return Object of type \ref nz_bitwidtht
inline const nz_bitwidtht &
to_nz_bitwidth(const exprt &expr)
{
  const auto &side_effect_expr = to_side_effect_expr(expr);
  PRECONDITION(
    side_effect_expr.get_statement() == ID_nz_bitwidth);
  return static_cast<const nz_bitwidtht &>(side_effect_expr);
}

/// \copydoc to_nz_bitwidth(const exprt &)
inline nz_bitwidtht &to_nz_bitwidth(exprt &expr)
{
  auto &side_effect_expr = to_side_effect_expr(expr);
  PRECONDITION(
    side_effect_expr.get_statement() == ID_nz_bitwidth);
  return static_cast<nz_bitwidtht &>(side_effect_expr);
}

class cut_bitwidtht : public side_effect_exprt
{
public:
  cut_bitwidtht(
    exprt a,
    const irep_idt &w,
    const source_locationt &loc)
    : side_effect_exprt(
        ID_cut_bitwidth,
        {std::move(a)},
        empty_typet{},
        loc)
  {
    set(ID_width, w);
    type() = compute_type(op0(), w);
  }

  static typet compute_type(const exprt&a, const irep_idt &wstr){
    size_t w = stoi(id2string(wstr));
    const typet &tpA = a.type();
    if(tpA.id() == ID_bool || tpA.id() == ID_c_bool)
      return bool_typet{};
    else if(const auto u = type_try_dynamic_cast<unsignedbv_typet>(tpA)){
      if(u->get_width() <= w)
        return tpA;
      else
        return unsignedbv_typet{w};
    }
    else if(const auto s = type_try_dynamic_cast<signedbv_typet>(tpA)){
      if(s->get_width() <= w)
        return tpA;
      else
        return signedbv_typet{w};
    } else if(tpA.id() == ID_pointer){
      return tpA;
    }
    UNREACHABLE;
  }

  exprt &a()
  {
    return op0();
  }

  const exprt &a() const
  {
    return op0();
  }

  size_t width()
  {
    return stoi(id2string(get(ID_width)));
  }

  const irep_idt &op() const
  {
    return get(ID_operator);
  }
};

template <>
inline bool can_cast_expr<cut_bitwidtht>(const exprt &base)
{
  if(base.id() != ID_side_effect)
    return false;

  const irep_idt &statement = to_side_effect_expr(base).get_statement();
  return statement == ID_cut_bitwidth;
}

/// \brief Cast an exprt to a \ref cut_bitwidtht
///
/// \a expr must be known to be \ref cut_bitwidtht.
///
/// \param expr: Source expression
/// \return Object of type \ref cut_bitwidtht
inline const cut_bitwidtht &
to_cut_bitwidth(const exprt &expr)
{
  const auto &side_effect_expr = to_side_effect_expr(expr);
  PRECONDITION(
    side_effect_expr.get_statement() == ID_cut_bitwidth);
  return static_cast<const cut_bitwidtht &>(side_effect_expr);
}

/// \copydoc to_cut_bitwidth(const exprt &)
inline cut_bitwidtht &to_cut_bitwidth(exprt &expr)
{
  auto &side_effect_expr = to_side_effect_expr(expr);
  PRECONDITION(
    side_effect_expr.get_statement() == ID_cut_bitwidth);
  return static_cast<cut_bitwidtht &>(side_effect_expr);
}

/// \brief A class for an expression that indicates a history variable
class history_exprt : public unary_exprt
{
public:
  explicit history_exprt(exprt variable, const irep_idt &id)
    : unary_exprt(id, std::move(variable))
  {
  }

  const exprt &expression() const
  {
    return op0();
  }
};

inline const history_exprt &
to_history_expr(const exprt &expr, const irep_idt &id)
{
  PRECONDITION(id == ID_old || id == ID_loop_entry);
  PRECONDITION(expr.id() == id);
  auto &ret = static_cast<const history_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \brief A class for an expression that represents a conditional target or
/// a list of targets sharing a common condition
/// in an assigns clause.
class conditional_target_group_exprt : public exprt
{
public:
  explicit conditional_target_group_exprt(exprt _condition, exprt _target_list)
    : exprt(ID_conditional_target_group, empty_typet{})
  {
    add_to_operands(std::move(_condition));
    add_to_operands(std::move(_target_list));
  }

  static void check(
    const exprt &expr,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    DATA_CHECK(
      vm,
      expr.operands().size() == 2,
      "conditional target expression must have two operands");

    DATA_CHECK(
      vm,
      expr.operands()[1].id() == ID_expression_list,
      "conditional target second operand must be an ID_expression_list "
      "expression, found " +
        id2string(expr.operands()[1].id()));
  }

  static void validate(
    const exprt &expr,
    const namespacet &,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    check(expr, vm);
  }

  const exprt &condition() const
  {
    return op0();
  }

  exprt &condition()
  {
    return op0();
  }

  const exprt::operandst &targets() const
  {
    return op1().operands();
  }

  exprt::operandst &targets()
  {
    return op1().operands();
  }
};

inline void validate_expr(const conditional_target_group_exprt &value)
{
  conditional_target_group_exprt::check(value);
}

template <>
inline bool can_cast_expr<conditional_target_group_exprt>(const exprt &base)
{
  return base.id() == ID_conditional_target_group;
}

/// \brief Cast an exprt to a \ref conditional_target_group_exprt
///
/// \a expr must be known to be \ref conditional_target_group_exprt
///
/// \param expr: Source expression
/// \return Object of type \ref conditional_target_group_exprt
inline const conditional_target_group_exprt &
to_conditional_target_group_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_conditional_target_group);
  auto &ret = static_cast<const conditional_target_group_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_conditional_target_group_expr(const exprt &expr)
inline conditional_target_group_exprt &
to_conditional_target_group_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_conditional_target_group);
  auto &ret = static_cast<conditional_target_group_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

#endif // CPROVER_ANSI_C_C_EXPR_H
