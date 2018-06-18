/*******************************************************************\

Module: Interprocedural Summary Checker for BMC

Author: Manasij Mukherjee

\*******************************************************************/

#ifndef CPROVER_2LS_2LS_SUMMARY_CHECKER_INTBMC_H
#define CPROVER_2LS_2LS_SUMMARY_CHECKER_INTBMC_H

#include "summary_checker_base.h"
#include "ssa/simplify_ssa.h"

class summary_checker_intbmct:public summary_checker_baset
{
public:
  explicit summary_checker_intbmct(optionst &_options):
    summary_checker_baset(_options)
  {
  }

  virtual resultt operator()(const goto_modelt &);

  property_checkert::resultt check_properties_simple();

  exprt compute_wp(exprt pred, local_SSAt& ssa,
  	local_SSAt::var_sett rets, std::vector<exprt> args,
  	exprt guard, ssa_simplifiert* simp, exprt simp_context);

};

#endif
