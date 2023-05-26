//
// Created by giulio on 25/05/23.
//

#ifndef CBMC_ABSTRACTION_H
#define CBMC_ABSTRACTION_H

#include <util/ssa_expr.h>

class is_abstractt: public unary_exprt{
public:
  is_abstractt(ssa_exprt &expr) : unary_exprt(ID_is_abstract, expr, bool_typet{}){}
};


inline bool is_is_abstract(const exprt &expr)
{
  return expr.id() == ID_is_abstract;
}

template <>
inline bool can_cast_expr<is_abstractt>(const exprt &base)
{
  return is_is_abstract(base);
}

/// Cast a generic exprt to an \ref is_abstractt.
/// \param expr: Source expression
/// \return Object of type \ref is_abstractt
inline const is_abstractt &to_is_abstract(const exprt &expr)
{
  INVARIANT_WITH_DIAGNOSTICS(is_is_abstract(expr), "expr needs to be a is_abstractt", expr.pretty());
  return static_cast<const is_abstractt &>(expr);
}

/// \copydoc to_is_abstract(const exprt &)
inline is_abstractt &to_is_abstract(exprt &expr)
{
  INVARIANT_WITH_DIAGNOSTICS(is_is_abstract(expr), "expr needs to be a is_abstractt", expr.pretty());
  return static_cast<is_abstractt &>(expr);
}

class overflow_bitt: public unary_exprt{
public:
  overflow_bitt(exprt &expr) : unary_exprt(ID_overflow_bit, expr, bool_typet{}){}
};


inline bool is_overflow_bit(const exprt &expr)
{
  return expr.id() == ID_overflow_bit;
}

template <>
inline bool can_cast_expr<overflow_bitt>(const exprt &base)
{
  return is_overflow_bit(base);
}

/// Cast a generic exprt to an \ref overflow_bitt.
/// \param expr: Source expression
/// \return Object of type \ref overflow_bitt
inline const overflow_bitt &to_overflow_bit(const exprt &expr)
{
  INVARIANT_WITH_DIAGNOSTICS(is_overflow_bit(expr), "expr needs to be a overflow_bitt", expr.pretty());
  return static_cast<const overflow_bitt &>(expr);
}

/// \copydoc to_overflow_bit(const exprt &)
inline overflow_bitt &to_overflow_bit(exprt &expr)
{
  INVARIANT_WITH_DIAGNOSTICS(is_overflow_bit(expr), "expr needs to be a overflow_bitt", expr.pretty());
  return static_cast<overflow_bitt &>(expr);
}

const exprt is_expr_abstract(exprt&, size_t width);
bool is_abstractable_name(const std::string);
bool is_abstractable_type(typet&, size_t);

#endif //CBMC_ABSTRACTION_H
