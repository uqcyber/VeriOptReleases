theory ExpandLogicPhase
  imports Canonicalizations.Common
begin

phase ExpandLogicPhase
  terminating size
begin

lemma ExpandShortCircuitVal:
  assumes "x \<noteq> UndefVal \<and> y \<noteq> UndefVal"
  assumes "val[(x || y)] \<noteq> UndefVal"
  shows "val[((x || y) ? t : f)] = val[(x ? t : (y ? t : f))]"
  using assms by (cases x; cases y; auto)

optimization ExpandShortCircuit:
  "((x || y) ? t : f) \<longmapsto> (x ? t : (y ? t : f))"
  defer apply simp
  using ExpandShortCircuitVal 
  apply (smt (verit, ccfv_threshold) ConditionalExpr ConditionalExprE bin_eval.simps(7) evaltree_not_undef intval_conditional.elims unfold_binary)
  sorry

lemma swap_branches:
  assumes "x \<noteq> UndefVal \<and> \<not>x \<noteq> UndefVal"
  shows "val[(\<not>x) ? t : f] = val[x ? f : t]"
  using assms
  by simp

optimization ExpandShortCircuitXNeg:
  "(((\<not>x) || y) ? t : f) \<longmapsto> (x ? (y ? t : f) : t)"
  defer apply simp
  apply (rule allI)+ apply (rule impI)
  using ExpandShortCircuit(1) unfolding rewrite_preservation.simps le_expr_def
  
  using swap_branches
  sorry
  
  (*apply (smt (verit, ccfv_threshold) ConditionalExpr ConditionalExprE ExpandShortCircuit(1) intval_logic_negation.elims le_expr_def rewrite_preservation.simps(1) unary_eval.simps(4) unfold_unary val_to_bool.simps(1) val_to_bool.simps(2) zero_neq_one)
  sorry*)

optimization ExpandShortCircuitYNeg:
  "((x || (\<not>y)) ? t : f) \<longmapsto> (x ? t : (y ? f : t))"
  defer apply simp
  apply (rule allI)+ apply (rule impI)
  using ExpandShortCircuitVal
  sorry

optimization ExpandShortCircuitXYNeg:
  "(((\<not>x) || (\<not>y)) ? t : f) \<longmapsto> (x ? (y ? f : t) : t)"
  defer apply simp
  apply (rule allI)+ apply (rule impI)
  using ExpandShortCircuitVal swap_branches 
  sorry

end

end