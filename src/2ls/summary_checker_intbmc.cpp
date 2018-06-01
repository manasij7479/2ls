/*******************************************************************\

Module: Summary Checker for BMC

Author: Peter Schrammel

\*******************************************************************/

#include "summary_checker_intbmc.h"
#include <fstream>
#include <util/replace_expr.h>
#include <util/expr_util.h>
#include "../domains/incremental_solver.h"
#include "ssa/simplify_ssa.h"
/*******************************************************************\

Function: summary_checker_intbmct::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
// typedef enum { D_SATISFIABLE, D_UNSATISFIABLE, D_ERROR } resultt;

bool is_cond_s(exprt e, const namespacet &ns) {
  if (e.id() == ID_symbol) {
    auto name = from_expr(ns, " ", e);
    if (name[0] == '$' && name[1] == 'c'
        && name[2] == 'o' && name[3] == 'n' && name[4] == 'd')
      return true;
  }
  return false;
}

exprt summary_checker_intbmct::compute_wp(exprt pred, local_SSAt &ssa,
  std::ostream& out, local_SSAt::var_sett rets, std::vector<exprt> args, exprt guard, ssa_simplifiert* simp, exprt simp_context) {
  auto ns = ssa.ns;
  
  std::ofstream ssaout("/tmp/ssa.out", std::ios::app);
  ssa.output_verbose(ssaout);

  exprt WP = pred;

  auto p = ssa.params.begin();
  auto a = args.begin();
  for (; p != ssa.params.end(); ++p, ++a) {
    simp_context = and_exprt(simp_context, equal_exprt(*a, *p));
  }
  out << "SIMPCON " << from_expr(ns, "", simp_context) << std::endl;

  // out << "RET " << from_expr(ns, "", *rets.begin()) << std::endl;
   
  if (!rets.empty() && !ssa.globals_out.empty()) {
    // assert(rets.size() == 1);

    // assert(ssa.globals_out.size() == 1);
    if (ssa.globals_out.size() == 1 && rets.size() == 1) {
      replace_expr(*rets.begin(), *ssa.globals_out.begin(), WP);
    }
  }

  for(auto
      n_it=ssa.nodes.rbegin();
      n_it!=ssa.nodes.rend();
      n_it++)
  {
    local_SSAt::nodet &node=*n_it;
    for(auto
        a_it=node.assertions.rbegin();
        a_it!=node.assertions.rend();
        a_it++)
    {
      out << from_expr(ns, "", WP) << "\n";
      if (WP == true_exprt()) {
        WP = *a_it;
      } else if (WP == false_exprt()) {
        // do nothing
      } else {
        WP = and_exprt(WP, *a_it);
      }
      out << from_expr(ns, "", WP) << "\n";
    }

    
    bool callsite = false;
    for(auto
        e_it=node.function_calls.rbegin();
        e_it!=node.function_calls.rend();
        e_it++)
    {
      callsite = true;
        auto name = from_expr(ns, "", e_it->function());
        local_SSAt &callee = ssa_db.get(name);
        simp->internalize(callee, name);
           
        local_SSAt::var_sett cs_globals_in;
        goto_programt::const_targett loc=n_it->location;
        
        ssa.get_globals(loc, cs_globals_in, false);
        // for(auto gi : cs_globals_in)
        //   out << "GI: " << from_expr(ns, "", gi) << "\n";

        // for (auto go : callee.globals_out) {
        //   out << "GO: " << from_expr(ns, "", go) << "\n";
        // }

        // for (auto arg : e_it->arguments()) {
        //   out << "ARG: " << from_expr(ns, "", arg) << "\n";
        // }

        // for (auto param : callee.params) {
        //   out << "PARAM: " << from_expr(ns, "", param) << "\n";
        // }

        out << "WP F1 = " << from_expr(ns, "", WP) << "\n";

        exprt guard = ssa.guard_symbol(loc);
        out << "G : " << from_expr(ns, "", guard) << std::endl;

        WP = compute_wp(WP, callee, out, cs_globals_in,
          e_it->arguments(), guard, simp, simp_context);

        out << "WP F2 = " << from_expr(ns, "", WP) << "\n";

        out << "WP F3= " << from_expr(ns, "", WP) << "\n";


// #endif

    }

    for(auto
        e_it=node.equalities.begin();
        e_it!=node.equalities.end();
        e_it++)
    {
      // out << "RBEGIN\n";
      // out << from_expr(ns, "", WP) << "\t" << from_expr(ns, "", e_it->lhs()) << "\n";
      // out << "ISCND : " << from_expr(ns, "", e_it->lhs()) << "\t" <<  is_cond_s(e_it->lhs(), ns) << std::endl;
      if (callsite && !is_cond_s(e_it->lhs(), ns)) {
        replace_expr(e_it->rhs(), e_it->lhs(), WP);
      } else {
        // out << "LHS = " << from_expr(ns, "", e_it->lhs()) << "\n";
        // out << "RHS = " << from_expr(ns, "", e_it->rhs()) << "\n";
        auto target = e_it->rhs();
        if (e_it->rhs().id() == ID_if) {

          out << "SIMP " << from_expr(ns, "", target) << '\t' << from_expr(ns, "", guard) << std::endl;

          auto c = simp->simplify_expr_cs(target.op0(), and_exprt(guard, simp_context));
          if (c == true_exprt()) {
            target = target.op1();
          } else if (c == false_exprt()) {
            target = target.op2();
          }
        }

        if (WP != true_exprt() && WP != false_exprt()) {
          replace_expr(e_it->lhs(), target, WP);
        }
      }
      out << "WP = " << from_expr(ns, "", WP) << "\n";

      // out << "DIAG: " << e_it->rhs().id() << '\t' << e_it->rhs().type().id() << "\n";
      // out << "REND\n";
    }
  }

  p = ssa.params.begin();
  a = args.begin();
  for (; p != ssa.params.end(); ++p, ++a) {
    replace_expr(*p, *a, WP);
  }


  return WP;
}

property_checkert::resultt summary_checker_intbmct::operator()(
  const goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);

  SSA_functions(goto_model, ns);

  ssa_unwinder.init(false, true);

  property_checkert::resultt result=property_checkert::UNKNOWN;
  unsigned min_unwind=options.get_unsigned_int_option("unwind-min");
  unsigned max_unwind=options.get_unsigned_int_option("unwind");
  status() << "Max-unwind is " << max_unwind << eom;
  ssa_unwinder.init_localunwinders();

  for(unsigned unwind=min_unwind; unwind<=max_unwind; unwind++)
  {
    status() << "Unwinding (k=" << unwind << ")" << messaget::eom;
    summary_db.mark_recompute_all();
    ssa_unwinder.unwind_all(unwind);
    result=check_properties_simple();
    if(result==property_checkert::PASS)
    {
      status() << "BMC proof found after "
         << unwind << " unwinding(s)" << messaget::eom;
      break;
    }
    else if(result==property_checkert::FAIL)
    {
      status() << "BMC counterexample found after "
         << unwind << " unwinding(s)" << messaget::eom;
      break;
    }
  }
  report_statistics();
  return result;
}

template <typename solvert>
void print_symbol_values(
  const local_SSAt &SSA,
  solvert &solver,
  std::ostream &out,
  exprt expr)
{
  static std::unordered_set<irep_idt, irep_id_hash> seen;
  if (expr.id()==ID_forall)
    return;
  if(expr.id()==ID_symbol)
  {
    auto name = to_symbol_expr(expr).get_identifier();
    if (seen.find(name) == seen.end()) {
      out << from_expr(SSA.ns, "", expr) << "=="
        << from_expr(SSA.ns, "", solver.get(expr)) << "\n";
    }
    seen.insert(name);
    return;
  }
  for(exprt::operandst::const_iterator it=expr.operands().begin();
      it!=expr.operands().end(); it++)
  {
    print_symbol_values(SSA, solver, out, *it);
  }
}

property_checkert::resultt summary_checker_intbmct::check_properties_simple() {
  std::ofstream out("/tmp/out2.txt");
  local_SSAt &ssa = ssa_db.get("main");

  ssa_simplifiert simp(ssa, ssa.ns);

  simp.internalize(ssa, "main");
  
  auto WP = compute_wp(true_exprt(), ssa, out, {}, {}, true_exprt(),
    &simp, true_exprt());
  
  incremental_solvert solver(ssa.ns);

  solver << ssa;
  solver << ssa.get_enabling_exprs();

  solver << not_exprt(WP);

  if (solver() == D_SATISFIABLE) {

    out << "sat\nModel:\n";

    for(local_SSAt::nodest::const_iterator n_it=
        ssa.nodes.begin(); n_it!=ssa.nodes.end(); n_it++)
    {
      for(local_SSAt::nodet::equalitiest::const_iterator e_it=
            n_it->equalities.begin(); e_it!=n_it->equalities.end(); e_it++)
      {
        print_symbol_values(ssa, solver, out, *e_it);
      }
    }


    return property_checkert::FAIL;
  } else {
    return property_checkert::PASS;
  }
}
