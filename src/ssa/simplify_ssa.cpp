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
#include <chrono>
#include <ctime>
#include <ratio>


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

// bool is_cond_s(exprt e, const namespacet &ns) {
//   if (e.id() == ID_symbol) {
//     auto name = from_expr(ns, " ", e);
//     if (name[0] == '$' && name[1] == 'c' && name[2] == 'o')
//       return true;
//   }
//   return false;
// }

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


  std::ofstream before("/tmp/before.txt", std::fstream::app);

  // std::ofstream after("/tmp/after.txt", std::fstream::app);

  // ssa.output_verbose(before);

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
      
      // if (options.get_bool_option("simplify-ssa")) {
      
      // simplifier.internalize(e_it);
      // if (e_it->rhs().id() != ID_constant && e_it->rhs().id() != ID_symbol
      //     && e_it->rhs().type().id() != ID_pointer) {
      //   simplifier.simplify_expr(e_it->rhs());
      // }
      // if (e_it->rhs().id() != ID_if) {
      //   simplifier.record(e_it);
      // }
      // simplifier.replace(e_it->rhs());



      e_it->lhs()=simplify_expr(e_it->lhs(), ns);
      // if (options.get_bool_option("simplify-ssa")) {
      
      std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();
//       simplifier.internalize(e_it);
//       simplifier.simplify_expr(e_it->rhs());
      
      e_it->rhs()=simplify_expr(e_it->rhs(), ns);


      // if (!is_guard_s(e_it->lhs(), ns)) {
      //   e_it->rhs() = simplifier.simplify_expr_cs(e_it->rhs(), guard);
      // }
      // }



      std::chrono::high_resolution_clock::time_point t2 = std::chrono::high_resolution_clock::now();
      std::chrono::duration<double> time_span = std::chrono::duration_cast<std::chrono::duration<double>>(t2 - t1);
      before << simptime << '\n';
      simptime += time_span.count();
      
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
      // simplifier.simplify_expr(*a_it);
      *a_it=simplify_expr(*a_it, ns);
    }
  }
  // simplifier.remove_redundant_equalities(ssa);
  // ssa.output_verbose(after);
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
    // result = replace_expr_custom(what, dest.op1()) && result;
    // result = replace_expr_custom(what, dest.op2()) && result;
  } else Forall_operands(it, dest) {
    auto result_temp=replace_expr_custom(what, *it);
    result = result && result_temp;
  }

  return result;
}

void ssa_simplifiert::simplify_expr(exprt &in) {

  auto T = true_exprt();
  auto F = false_exprt();

  // out << "TRY: " << from_expr(ns, "", in) << "\n";
  if (in.type().id() == ID_bool) {

    // if (not_simplifiable.find(in) != not_simplifiable.end()) {
    //   out << "BINGO\n";
    // }
//     if (in != T && in != F) {
// 
//       auto success = simplify_expr_to(in, T);
//       if (!success) { 
//         success = simplify_expr_to(in, F) && success;
//       }
//       // if (!success) {
//       //   not_simplifiable.insert(in);
//       //   out << "NOSIMP-ENTRY : " << from_expr(ns, "", in) << "\n";
//       // }
//     }
  } else if (in.type().id() == ID_signedbv || in.type().id() == ID_unsignedbv) {

    // in = simplify_expr_to(in, gen_zero(in.type()));

    if (in.id() == ID_if) {
      // out << "CID : " << in.op0().type().id() << "\n";
      if (simplify_expr_to(in.op0(), T)) {
        in =  in.op1();
      } else if (simplify_expr_to(in.op0(), F)) {
        in =  in.op2();
      }
    }
  } else {
    // out << "BADTYPE : " <<  in.type().id() << " : " << from_expr(ns, "", in) << "\n";
  }

}

exprt ssa_simplifiert::simplify_expr_cs(exprt in, exprt context) {
  solver.new_context();
  solver << context;
  simplify_expr(in);
  solver.pop_context();
  return in;
}

exprt ssa_simplifiert::simplify_expr_recursive(exprt in) {
  // if (in.type().id() == ID_bool) {
  //   if (in != true_exprt() && in != false_exprt()) {
  //     in = simplify_expr_to(in, true_exprt());
  //     in = simplify_expr_to(in, false_exprt());
  //   } else if (in.id() == ID_and) {
  //     return and_exprt(simplify_expr_recursive(in.op0()),
  //                     simplify_expr_recursive(in.op1()));
  //   } else if (in.id() == ID_or) {
  //     return or_exprt(simplify_expr_recursive(in.op0()),
  //                     simplify_expr_recursive(in.op1()));
  //   } else if (in.id() == ID_if) {
  //     if (simplify_expr_to(in.op0(), true_exprt()) == true_exprt()) {
  //       return simplify_expr_recursive(in.op1());
  //     } else if (simplify_expr_to(in.op0(), false_exprt()) == false_exprt()) {
  //       return simplify_expr_recursive(in.op2());
  //     }
  //   }

  // } else if (in.type().id() == ID_signedbv ) {

  //   in = simplify_expr_to(in, gen_zero(in.type()));

  //   if (in.id() == ID_if) {
  //     out << "CID-REC : " << in.op0().type().id() << "\n";
  //     if (simplify_expr_to(in.op0(), true_exprt()) == true_exprt()) {
  //       return simplify_expr_recursive(in.op1());
  //     } else if (simplify_expr_to(in.op0(), false_exprt()) == false_exprt()) {
  //       return simplify_expr_recursive(in.op2());
  //     }
  //   }
  // } else {
  //   out << "BADTYPE-REC : " <<  in.type().id() << " : " << from_expr(ns, "", in) << "\n";
  // }
  return in;
}


bool ssa_simplifiert::simplify_expr_to(exprt& in, exprt target) {
  bool result = false;
  if (in != target) {
    solver.new_context();

    solver << not_exprt(equal_exprt(in, target));
    out << "TRY: " << from_expr(ns, " ", in) << " to " <<
           from_expr(ns, " ", target) << std::endl;
    if (solver() == D_UNSATISFIABLE) {
      in = target;
      result = true;
      out << "RESULT: " <<  from_expr(ns, " ", in) << std::endl;
    } else {
        out << "COULD NOT SIMPLIFY\n";
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

    // out << "NODE\n";
    // node.output(out, ns);
    // out << "NODE END\n";

    if (!skipped && !node.equalities.empty()) {
      skipped = true;
      
      // out << "SKIP NODE\n";
      // node.output(out, ns);
      // out << "SKIP NODE END\n";
      it++;
      continue;
    }

     
    // exprt guard = find_guard(node, ns);
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
  // in=::simplify_expr(in, ns);
  if (in.id() != ID_constant && in.id() != ID_symbol) {
// out << "IN :" << from_expr(ns, "", in) << "\n";
    replace_expr_custom(map, in);
    out << "REP " << from_expr(ns, "", in) << " WITH " << from_expr(ns, "", in) << "\n";
  }
  // in=::simplify_expr(in, ns);
}

