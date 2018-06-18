/*******************************************************************\

Module: Interprocedural Summary Checker for BMC

Author: Manasij Mukherjee

\*******************************************************************/

#include "summary_checker_intbmc.h"
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
  local_SSAt::var_sett rets, std::vector<exprt> args, exprt guard, ssa_simplifiert* simp, exprt simp_context) {
  auto ns = ssa.ns;
  
  exprt WP = pred;

  auto p = ssa.params.begin();
  auto a = args.begin();
  for (; p != ssa.params.end(); ++p, ++a) {
    simp_context = and_exprt(simp_context, equal_exprt(*a, *p));
  }
  
   
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
      if (WP == true_exprt()) {
        WP = *a_it;
      } else if (WP == false_exprt()) {
        // do nothing
      } else {
        WP = and_exprt(WP, *a_it);
      }
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

        exprt guard = ssa.guard_symbol(loc);

        WP = compute_wp(WP, callee, cs_globals_in,
          e_it->arguments(), guard, simp, simp_context);

    }

    for(auto
        e_it=node.equalities.begin();
        e_it!=node.equalities.end();
        e_it++)
    {
      if (callsite && !is_cond_s(e_it->lhs(), ns)) {
        replace_expr(e_it->rhs(), e_it->lhs(), WP);
      } else {
        auto target = e_it->rhs();
        if (e_it->rhs().id() == ID_if) {

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
  local_SSAt &ssa = ssa_db.get("main");

  ssa_simplifiert simp(ssa, ssa.ns);

  simp.internalize(ssa, "main");
  
  auto WP = compute_wp(true_exprt(), ssa, {}, {}, true_exprt(),
    &simp, true_exprt());
  
  incremental_solvert solver(ssa.ns);

  solver << ssa;
  solver << ssa.get_enabling_exprs();

  solver << not_exprt(WP);

  if (solver() == D_SATISFIABLE) {
    return property_checkert::FAIL;
  } else {
    return property_checkert::PASS;
  }
}
