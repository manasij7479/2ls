/*******************************************************************\

Module: SSA Simplification

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/simplify_expr.h>

#include "simplify_ssa.h"
#include "../domains/incremental_solver.h"
#include <util/std_expr.h>
#include <util/arith_tools.h>
#include <util/expr_util.h>
#include "2ls/2ls_parse_options.h"
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
  auto name =ssa.goto_function;
  std::ofstream before("/tmp/before.txt", std::fstream::app);
  std::ofstream after("/tmp/after.txt", std::fstream::app);

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
      
      // if (options.get_bool_option("simplify-ssa")) {`c
      
      simplifier.internalize(e_it);
      e_it->rhs() = simplifier.simplify_expr(e_it->rhs());
      simplifier.record(e_it);

      // if (!is_guard_s(e_it->lhs(), ns)) {
      //   e_it->rhs() = simplifier.simplify_expr_cs(e_it->rhs(), guard);
      // }
      // }
      
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
  } else if (in.type().id() == ID_signedbv ) {

    // in = simplify_expr_to(in, gen_zero(in.type()));

    if (in.id() == ID_if) {
      out << "CID : " << in.op0().type().id() << "\n";
      if (simplify_expr_to(in.op0(), true_exprt()) == true_exprt()) {
        return in.op1();
      } else if (simplify_expr_to(in.op0(), false_exprt()) == false_exprt()) {
        return in.op2();
      }
    }
  } else {
    out << "BADTYPE : " <<  in.type().id() << " : " << from_expr(ns, "", in) << "\n";
  }

  if (in != true_exprt() && in != false_exprt()) {
    out << "IN :" << from_expr(ns, "", in) << "\n";
    replace_expr(map, in);
    out << "REP :" << from_expr(ns, "", in) << "\n";
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

exprt ssa_simplifiert::simplify_expr_recursive(exprt in) {
  if (in.type().id() == ID_bool) {
    if (in != true_exprt() && in != false_exprt()) {
      in = simplify_expr_to(in, true_exprt());
      in = simplify_expr_to(in, false_exprt());
    } else if (in.id() == ID_and) {
      return and_exprt(simplify_expr_recursive(in.op0()),
                      simplify_expr_recursive(in.op1()));
    } else if (in.id() == ID_or) {
      return or_exprt(simplify_expr_recursive(in.op0()),
                      simplify_expr_recursive(in.op1()));
    } else if (in.id() == ID_if) {
      if (simplify_expr_to(in.op0(), true_exprt()) == true_exprt()) {
        return simplify_expr_recursive(in.op1());
      } else if (simplify_expr_to(in.op0(), false_exprt()) == false_exprt()) {
        return simplify_expr_recursive(in.op2());
      }
    }

  } else if (in.type().id() == ID_signedbv ) {

    in = simplify_expr_to(in, gen_zero(in.type()));

    if (in.id() == ID_if) {
      out << "CID-REC : " << in.op0().type().id() << "\n";
      if (simplify_expr_to(in.op0(), true_exprt()) == true_exprt()) {
        return simplify_expr_recursive(in.op1());
      } else if (simplify_expr_to(in.op0(), false_exprt()) == false_exprt()) {
        return simplify_expr_recursive(in.op2());
      }
    }
  } else {
    out << "BADTYPE-REC : " <<  in.type().id() << " : " << from_expr(ns, "", in) << "\n";
  }
  return in;
}

exprt ssa_simplifiert::simplify_expr_to(exprt in, exprt target) {
  if (in != target) {
    solver.new_context();

    solver << not_exprt(equal_exprt(in, target));
    out << "TRY: " << from_expr(ns, " ", in) << " to " <<
           from_expr(ns, " ", target) << std::endl;
    if (solver() == D_UNSATISFIABLE) {
      in = target;
       out << "RESULT: " <<  from_expr(ns, " ", in) << std::endl;
    } else {
        out << "COULD NOT SIMPLIFY\n";
    }
    solver.pop_context();
  }
  return in;
}
void ssa_simplifiert::internalize(local_SSAt::nodet::equalitiest::iterator in) {
  solver << *in;
}

void ssa_simplifiert::record(local_SSAt::nodet::equalitiest::iterator in) {
  if (map.find(in->lhs()) == map.end()) {
    map[in->lhs()] = in->rhs();
  }
}
