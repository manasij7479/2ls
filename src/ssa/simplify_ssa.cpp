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
// #include "2ls/2ls_parse_options.h"
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

bool is_other(exprt e, const namespacet &ns) {
  if (e.id() == ID_symbol) {
    auto name = from_expr(ns, " ", e);
    if (name[0] == '_')
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
      
      simplifier.internalize(e_it);
      if (e_it->rhs().id() != ID_constant && e_it->rhs().id() != ID_symbol
          && e_it->rhs().type().id() != ID_pointer) {
        simplifier.simplify_expr(e_it->rhs());
      }
      
      // if (replace_vars) {
      //   if (e_it->rhs().id() != ID_if) {
      //     simplifier.record(e_it);
      //   }
      //   simplifier.replace(e_it->rhs());
      // }

      e_it->lhs()=simplify_expr(e_it->lhs(), ns);
      e_it->rhs()=simplify_expr(e_it->rhs(), ns);

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
      simplifier.simplify_expr(*a_it);
      *a_it=simplify_expr(*a_it, ns);
    }
  }
}

bool replace_expr_custom(const exprt &what, const exprt &by, exprt &dest)
{
  if(dest==what)
  {
    dest=by;
    return false;
  }

  bool result=true;

  Forall_operands(it, dest)
    result=replace_expr_custom(what, by, *it) && result;

  return result;
}

bool replace_expr_custom(const replace_mapt &what, exprt &dest)
{
  {
    replace_mapt::const_iterator it=what.find(dest);

    if(it!=what.end())
    {
      dest=it->second;
      return false;
    }
  }

  bool result=true;

  if (dest.id() == ID_if ) {
  } else Forall_operands(it, dest) {
    auto result_temp=replace_expr_custom(what, *it);
    result = result && result_temp;
  }

  return result;
}

void ssa_simplifiert::simplify_expr(exprt &in) {
  if (simplify_recursive) {
    simplify_expr_recursive(in);
  }

  auto T = true_exprt();
  auto F = false_exprt();

  if (in.type().id() == ID_bool && simplify_all) {
    if (in != T && in != F) {
      auto success = simplify_expr_to(in, T);
      if (!success) { 
        success = simplify_expr_to(in, F) && success;
      }
    }
  } else if (in.type().id() == ID_signedbv || in.type().id() == ID_unsignedbv) {

    if (in.id() == ID_if) {
      if (simplify_expr_to(in.op0(), T)) {
        in =  in.op1();
      } else if (simplify_expr_to(in.op0(), F)) {
        in =  in.op2();
      }
    }
  }
}

exprt ssa_simplifiert::simplify_expr_cs(exprt in, exprt context) {
  solver.new_context();
  solver << context;
  simplify_expr(in);
  solver.pop_context();
  return in;
}

void ssa_simplifiert::simplify_expr_recursive(exprt& in) {
  
  auto T = true_exprt();
  auto F = false_exprt();

  if (in.type().id() == ID_bool && simplify_all) {
    if (in != T && in != F) {
      auto success = simplify_expr_to(in, T);
      if (!success) { 
        success = simplify_expr_to(in, F) && success;
      }
    }
  } else if (in.type().id() == ID_signedbv || in.type().id() == ID_unsignedbv) {

    if (in.id() == ID_if) {
      if (simplify_expr_to(in.op0(), T)) {
        in =  in.op1();
        simplify_expr_recursive(in);
      } else if (simplify_expr_to(in.op0(), F)) {
        in =  in.op2();
        simplify_expr_recursive(in);
      }
    }
  }
}


bool ssa_simplifiert::simplify_expr_to(exprt& in, exprt target) {
  bool result = false;
  if (in != target) {
    solver.new_context();

    solver << not_exprt(equal_exprt(in, target));
    if (solver() == D_UNSATISFIABLE) {
      in = target;
      result = true;
    }
    solver.pop_context();
  }
  return result;
}
void ssa_simplifiert::internalize(local_SSAt::nodet::equalitiest::iterator in) {
  solver << *in;
}

void ssa_simplifiert::record(local_SSAt::nodet::equalitiest::iterator in) {
  if (map.find(in->lhs()) == map.end()) {
    if (in->rhs().id() == ID_constant || in->rhs().id() == ID_symbol) {
      map[in->lhs()] = in->rhs();
    }
  }
}

void ssa_simplifiert::remove_redundant_equalities(local_SSAt& ssa) {
  auto it = ssa.nodes.rbegin();
  bool skipped = false;
  for(auto
      n_it=it;
      n_it!=ssa.nodes.rend();
      n_it++)
  {
    local_SSAt::nodet &node=*n_it;

    if (!skipped && !node.equalities.empty()) {
      skipped = true;
      it++;
      continue;
    }

    std::vector<equal_exprt> new_vec;
    for(local_SSAt::nodet::equalitiest::iterator
        e_it=node.equalities.begin();
        e_it!=node.equalities.end();
        e_it++)
    {
      if ( !is_guard_s(e_it->lhs(), ns) && !is_other(e_it->lhs(), ns)) {
        if (map.find(e_it->lhs()) == map.end()) {
          new_vec.push_back(*e_it);
        }
      } else {
        new_vec.push_back(*e_it);
      }
    }
    node.equalities.swap(new_vec);
  }
}

void ssa_simplifiert::replace(exprt &in) {
  if (in.id() != ID_constant && in.id() != ID_symbol) {
    replace_expr_custom(map, in);
  }
}

