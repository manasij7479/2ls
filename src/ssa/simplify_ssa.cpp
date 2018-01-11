/*******************************************************************\

Module: SSA Simplification

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/simplify_expr.h>

#include "simplify_ssa.h"
#include "../domains/incremental_solver.h"
#include <fstream>

/*******************************************************************\

Function: simplify

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool is_guard_s(exprt e, const namespacet &ns) {
  if (e.id() == ID_symbol) {
    auto name = from_expr(ns, " ", e);
    if (name[0] == '$' && name[1] == 'g' && name[2] == 'u')
      return true;
  }
  return false;
}

exprt find_guard(local_SSAt::nodet &node, const namespacet &ns) {
  exprt result = true_exprt();

  for(local_SSAt::nodet::equalitiest::iterator
        e_it=node.equalities.begin();
        e_it!=node.equalities.end();
        e_it++)
  {
    if (is_guard_s(e_it->lhs(), ns)) {
      return e_it->rhs();
    }
  }

  return result;
}

void simplify(local_SSAt &ssa, const namespacet &ns)
{
  // std::ofstream out("/tmp/out.txt");
  // typedef enum { D_SATISFIABLE, D_UNSATISFIABLE, D_ERROR } resultt;
  // incremental_solvert solver(ns);
  // solver << ssa;
  // solver << ssa.get_enabling_exprs();

  std::ofstream before("/tmp/before.txt");
  std::ofstream after("/tmp/after.txt");

  ssa.output_verbose(before);

  ssa_simplifiert simplifier(ssa, ns);
  for(local_SSAt::nodest::iterator
      n_it=ssa.nodes.begin();
      n_it!=ssa.nodes.end();
      n_it++)
  {
    local_SSAt::nodet &node=*n_it;
     
    exprt guard = find_guard(node, ns);

    for(local_SSAt::nodet::equalitiest::iterator
        e_it=node.equalities.begin();
        e_it!=node.equalities.end();
        e_it++)
    {

      e_it->lhs()=simplify_expr(e_it->lhs(), ns);
      e_it->rhs()=simplify_expr(e_it->rhs(), ns);

      e_it->rhs() = simplifier.simplify_expr(e_it->rhs());
      e_it->rhs() = simplifier.simplify_expr_cs(e_it->rhs(), guard);
      
    }

    for(local_SSAt::nodet::constraintst::iterator
        c_it=node.constraints.begin();
        c_it!=node.constraints.end();
        c_it++)
    {
      *c_it=simplify_expr(*c_it, ns);
    }

    for(local_SSAt::nodet::assertionst::iterator
        a_it=node.assertions.begin();
        a_it!=node.assertions.end();
        a_it++)
    {
      *a_it=simplify_expr(*a_it, ns);
    }
  }
  ssa.output_verbose(after);
}

exprt ssa_simplifiert::simplify_expr(exprt in) {
  if (in.type().id() == ID_bool) {
    if (in != true_exprt() && in != false_exprt()) {
      in = simplify_expr_to(in, true_exprt());
      in = simplify_expr_to(in, false_exprt());
    }
  } else if (in.type().id() == ID_signed_int ) {
    in = simplify_expr_to(in, constant_exprt(0, in.type()));
  }
  return in;
}
exprt ssa_simplifiert::simplify_expr_cs(exprt in, exprt context) {
  exprt result;
  solver.new_context();
  solver << context;
  result = simplify_expr(in);
  solver.pop_context();
  return result;
}

exprt ssa_simplifiert::simplify_expr_to(exprt in, exprt target) {
  if (in != target) {
    solver.new_context();

    solver << not_exprt(equal_exprt(in, target));

    if (solver() == D_UNSATISFIABLE) {
      out << "TRY: " << from_expr(ns, " ", in) << std::endl;
      in = target;
      out << "RESULT: " <<  from_expr(ns, " ", in) << std::endl;
    }
    solver.pop_context();
  }
  return in;
}
