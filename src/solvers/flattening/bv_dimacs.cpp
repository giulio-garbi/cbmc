/*******************************************************************\

Module: Writing DIMACS Files

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Writing DIMACS Files

#include "bv_dimacs.h"

#include <solvers/sat/dimacs_cnf.h>
#include <util/suffix.h>

#include <fstream> // IWYU pragma: keep
#include <iostream>

bool bv_dimacst::write_dimacs()
{
  if(filename.empty() || filename == "-")
    return write_dimacs(std::cout);

  std::ofstream out(filename);

  if(!out)
  {
    log.error() << "failed to open " << filename << messaget::eom;
    return false;
  }

  return write_dimacs(out);
}

bool bv_dimacst::write_dimacs(std::ostream &out)
{
  dynamic_cast<dimacs_cnft &>(prop).write_dimacs_cnf(out);

  // we dump the mapping variable<->literals
  for(const auto &s : get_symbols())
  {
    if(s.second.is_constant())
      out << "c " << s.first << " " << (s.second.is_true() ? "TRUE" : "FALSE")
          << "\n";
    else
      out << "c " << s.first << " " << s.second.dimacs() << "\n";
  }

  // dump mapping for selected bit-vectors
  for(const auto &m : get_map().get_mapping())
  {
    const auto &literal_map = m.second.literal_map;

    if(literal_map.empty())
      continue;

    out << "c " << m.first;

    for(const auto &lit : literal_map)
    {
      out << ' ';

      if(lit.is_constant())
        out << (lit.is_true() ? "TRUE" : "FALSE");
      else
        out << lit.dimacs();
    }

    out << "\n";
  }

  return false;
}

static bool
contains_one_of(const std::string &s, const std::list<std::string> &vars)
{
  for(const std::string &v : vars)
  {
    if(s.find(v) != std::string::npos)
      return true;
  }
  return false;
}

void bv_dimacst::show_prop_vars()
{
  // we print the mapping variable<->literals for given vars
  for(const auto &s : get_symbols())
  {
    if(!contains_one_of(id2string(s.first), vars_to_show))
      continue;

    if(s.second.is_constant())
    {
      if(has_suffix(id2string(s.first), "#1"))
      {
        log.result() << s.first << " "
                     << (s.second.is_true() ? "TRUE" : "FALSE")
                     << messaget::eom;
      }
    }
    else
    {
      if(has_suffix(id2string(s.first), "#1"))
      {
        log.result() << s.first << " " << s.second.dimacs() << messaget::eom;
      }
    }
  }

  // dump mapping for selected bit-vectors
  for(const auto &m : get_map().get_mapping())
  {
    if(!contains_one_of(id2string(m.first), vars_to_show))
      continue;

    const bvt &literal_map = m.second.literal_map;

    if(literal_map.empty())
      continue;

    if(has_suffix(id2string(m.first), "#1"))
    {
      log.result() << m.first;

      for(const auto &lit : literal_map)
      {
        if(lit.is_constant())
          log.result() << " " << (lit.is_true() ? "TRUE" : "FALSE");
        else
          log.result() << " " << lit.dimacs();
      }
      log.result() << messaget::eom;
    }
  }
}
