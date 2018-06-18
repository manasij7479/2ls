/*******************************************************************\

Module: SSA Simplification

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_2LS_SSA_SIMPLIFY_SSA_H
#define CPROVER_2LS_SSA_SIMPLIFY_SSA_H

#include <util/namespace.h>

#include "local_ssa.h"
#include "../domains/incremental_solver.h"

void simplify(local_SSAt &, const namespacet &);


typedef enum { D_SATISFIABLE, D_UNSATISFIABLE, D_ERROR } resultt;

class ssa_simplifiert {
public:
  ssa_simplifiert(local_SSAt& SSA_, const namespacet& ns_)
    : SSA(SSA_), ns(ns_), solver(ns, false) {
      solver << SSA.get_enabling_exprs();
    }
  void simplify_expr(exprt &in);

  exprt simplify_expr_cs(exprt in, exprt context);
  bool simplify_expr_to(exprt &in, exprt target);
  void simplify_expr_recursive(exprt &in);
  void internalize(local_SSAt::nodet::equalitiest::iterator in);
  void internalize(local_SSAt& SSA, std::string name) {
    if (ssa_cached.find(name) == ssa_cached.end()) {
      solver << SSA.get_enabling_exprs();
      solver << SSA;
      ssa_cached.insert(name);
    }
  }
  void record(local_SSAt::nodet::equalitiest::iterator in);
  void remove_redundant_equalities(local_SSAt& ssa);
  void replace(exprt &in);
private:
  local_SSAt& SSA;
  const namespacet& ns;
  incremental_solvert solver;
  
  replace_mapt map;
  std::set<std::string> ssa_cached;

  // TODO control these with cmdline option
  bool simplify_all = false;
  bool simplify_recursive = false;
  // bool replace_vars = false;
};

#endif
