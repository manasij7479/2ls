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
    : SSA(SSA_), ns(ns_), solver(ns), out("/tmp/out.txt") {
      solver << SSA;
      solver << SSA.get_enabling_exprs();
    }
  exprt simplify_expr(exprt in);
  exprt simplify_expr_cs(exprt in, exprt context);
  exprt simplify_expr_to(exprt in, exprt target);
private:
  local_SSAt& SSA;
  const namespacet& ns;
  incremental_solvert solver;
  std::ofstream out;
};

#endif
