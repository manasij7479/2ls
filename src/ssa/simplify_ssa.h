/*******************************************************************\

Module: SSA Simplification

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_2LS_SSA_SIMPLIFY_SSA_H
#define CPROVER_2LS_SSA_SIMPLIFY_SSA_H

#include <util/namespace.h>

#include "local_ssa.h"
#include "../domains/incremental_solver.h"
#include <fstream>

void simplify(local_SSAt &, const namespacet &);


typedef enum { D_SATISFIABLE, D_UNSATISFIABLE, D_ERROR } resultt;

class ssa_simplifiert {
public:
  ssa_simplifiert(local_SSAt& SSA_, const namespacet& ns_)
    : SSA(SSA_), ns(ns_), solver(ns, false), out("/tmp/out.txt", std::fstream::app) {
      // solver << SSA;
      solver << SSA.get_enabling_exprs();
    }
  void simplify_expr(exprt &in);

  exprt simplify_expr_cs(exprt in, exprt context);
  bool simplify_expr_to(exprt &in, exprt target);
  exprt simplify_expr_recursive(exprt in);
  void internalize(local_SSAt::nodet::equalitiest::iterator in);
  void record(local_SSAt::nodet::equalitiest::iterator in);
  void remove_redundant_equalities(local_SSAt& ssa);
  void replace(exprt &in);
private:
  local_SSAt& SSA;
  const namespacet& ns;
  incremental_solvert solver;
  std::ofstream out;
  
  replace_mapt map;
  // std::unordered_set<exprt, irep_hash> used;
  // struct expr_string_hash {
  //   expr_string_hash(const namespacet& ns_) : ns(ns_) {}
  //   std::size_t operator()(exprt in) { return std::hash<std::string>()(from_expr(ns, "", in));}
  //   const namespacet& ns;
  // };
  // hash_set_cont<exprt, irep_hash> not_simplifiable; 
};

#endif
