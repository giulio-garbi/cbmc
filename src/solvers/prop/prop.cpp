/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "prop.h"
#include <iostream>

/// asserts a==b in the propositional formula
void propt::set_equal(literalt a, literalt b)
{
  if(b.is_constant())
  {
    if(b.is_true())
    {
      if(a.is_constant())
      {
        if(a.is_false())
        {
          std::cout << cur_expr->hash() << "-: ";
          std::cout << " 0\n";
          std::cout.flush();
        }
      } else
      {
        std::cout << cur_expr->hash() << "-: ";
        std::cout << a << " 0\n";
        std::cout.flush();
      }
      lcnf({a});
    } else
    {
      if(a.is_constant())
      {
        if(a.is_true())
        {
          std::cout << cur_expr->hash() << ": ";
          std::cout << " 0\n";
          std::cout.flush();
        }
      } else
      {
        std::cout << cur_expr->hash() << ": ";
        std::cout << !a << " 0\n";
        std::cout.flush();
      }
      lcnf({!a});
    }

    return;
  }
  std::cout << cur_expr->hash() << ": " << a << " " << !b <<" 0\n";
  std::cout.flush();
  lcnf(a, !b);
  std::cout << cur_expr->hash() << ": " << !a << " " << b <<" 0\n";
  std::cout.flush();
  lcnf(!a, b);
}

/// generates a bitvector of given width with new variables
/// \return bitvector
bvt propt::new_variables(std::size_t width)
{
  bvt result;
  result.reserve(width);
  for(std::size_t i=0; i<width; i++)
    result.push_back(new_variable());
  return result;
}

propt::resultt propt::prop_solve()
{
  ++number_of_solver_calls;
  return do_prop_solve();
}

std::size_t propt::get_number_of_solver_calls() const
{
  return number_of_solver_calls;
}
