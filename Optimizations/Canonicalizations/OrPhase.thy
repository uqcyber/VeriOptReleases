subsection \<open>OrNode Phase\<close>

theory OrPhase
  imports
    Common
begin

context stamp_mask
begin

text \<open>
Taking advantage of the truth table of or operations.

\begin{center}
\begin{tabular}{ c c c c }
\# & x & y & $x | y$ \\
1 & 0 & 0 & 0 \\ 
2 & 0 & 1 & 1 \\  
3 & 1 & 0 & 1 \\
4 & 1 & 1 & 1   
\end{tabular}
\end{center}

If row 2 never applies, that is, canBeZero x \& canBeOne y = 0,
then $(x | y) = x$.

Likewise, if row 3 never applies, canBeZero y \& canBeOne x = 0,
then $(x | y) = y$.
\<close>

lemma OrLeftFallthrough:
  assumes "(and (not (\<down>x)) (\<up>y)) = 0"
  shows "exp[x | y] \<ge> exp[x]"
  using assms
  apply simp apply ((rule allI)+; rule impI)
  subgoal premises eval for m p v
  proof -
    obtain b vv where e: "[m, p] \<turnstile> exp[x | y] \<mapsto> IntVal b vv" 
      by (metis BinaryExprE bin_eval_new_int new_int.simps eval(2))
    from e obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
      apply (subst (asm) unfold_binary_width) by force+
    from e obtain yv where yv: "[m, p] \<turnstile> y \<mapsto> IntVal b yv"
      apply (subst (asm) unfold_binary_width) by force+
    have vdef: "v = val[(IntVal b xv) | (IntVal b yv)]"
      by (metis bin_eval.simps(5) eval(2) evalDet unfold_binary xv yv)
    have "\<forall> i. (bit xv i) | (bit yv i) = (bit xv i)"
      by (metis assms bit_and_iff not_down_up_mask_and_zero_implies_zero xv yv)
    then have "IntVal b xv = val[(IntVal b xv) | (IntVal b yv)]"
      by (metis (no_types, lifting) and.idem assms bit.conj_disj_distrib eval_unused_bits_zero yv xv
          intval_or.simps(1) new_int.simps new_int_bin.simps not_down_up_mask_and_zero_implies_zero 
          word_ao_absorbs(3))
    then show ?thesis
      using xv vdef by presburger
  qed
  done

lemma OrRightFallthrough: 
  assumes "(and (not (\<down>y)) (\<up>x)) = 0"
  shows "exp[x | y] \<ge> exp[y]"
  using assms
  apply simp apply ((rule allI)+; rule impI)
  subgoal premises eval for m p v
  proof -
    obtain b vv where e: "[m, p] \<turnstile> exp[x | y] \<mapsto> IntVal b vv"
      by (metis BinaryExprE bin_eval_new_int new_int.simps eval(2))
    from e obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
      apply (subst (asm) unfold_binary_width) by force+
    from e obtain yv where yv: "[m, p] \<turnstile> y \<mapsto> IntVal b yv"
      apply (subst (asm) unfold_binary_width) by force+
    have vdef: "v = val[(IntVal b xv) | (IntVal b yv)]"
      by (metis bin_eval.simps(5) eval(2) evalDet unfold_binary xv yv)
    have "\<forall> i. (bit xv i) | (bit yv i) = (bit yv i)"
      by (metis assms bit_and_iff not_down_up_mask_and_zero_implies_zero xv yv)
    then have "IntVal b yv = val[(IntVal b xv) | (IntVal b yv)]"
      by (metis (no_types, lifting) assms eval_unused_bits_zero intval_or.simps(1) new_int.elims yv 
          new_int_bin.elims stamp_mask.not_down_up_mask_and_zero_implies_zero stamp_mask_axioms xv
          word_ao_absorbs(8))
    then show ?thesis
      using vdef yv by presburger
  qed
  done

end

phase OrNode
  terminating size
begin

(* Word level proofs *)
lemma bin_or_equal:
  "bin[x | x] = bin[x]"
  by simp

lemma bin_shift_const_right_helper:
 "x | y = y | x"
  by simp

lemma bin_or_not_operands:
 "(~x | ~y) = (~(x & y))"
  by simp

(* Value level proofs *)
lemma val_or_equal:
  assumes "x = new_int b v"
  and     "val[x | x] \<noteq> UndefVal"
  shows   "val[x | x] = val[x]"
  by (auto simp: assms)

lemma val_elim_redundant_false:
  assumes "x = new_int b v"
  and     "val[x | false] \<noteq> UndefVal"
  shows   "val[x | false] = val[x]"
  using assms by (cases x; auto; presburger)

lemma val_shift_const_right_helper:
   "val[x | y] = val[y | x]"
  by (cases x; cases y; auto simp: or.commute)

lemma val_or_not_operands:
 "val[~x | ~y] = val[~(x & y)]"
  by (cases x; cases y; auto simp: take_bit_not_take_bit)

(* Exp level proofs *)
lemma exp_or_equal:
  "exp[x | x] \<ge> exp[x]"
  apply auto[1]
  subgoal premises p for m p xa ya
  proof-
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p(1) by auto
    obtain xb xvv where xvv: "xv = IntVal xb xvv"
      by (metis evalDet evaltree_not_undef intval_is_null.cases intval_or.simps(3,4,5) p(1,3) xv)
    then have evalNotUndef: "val[xv | xv] \<noteq> UndefVal"
      using p evalDet xv by blast
    then have orUnfold: "val[xv | xv] = (new_int xb (or xvv xvv))"
      by (simp add: xvv)
    then have simplify: "val[xv | xv] = (new_int xb (xvv))"
      by (simp add: orUnfold)
    then have eq: "(xv) = (new_int xb (xvv))"
      using eval_unused_bits_zero xv xvv by auto
    then show ?thesis
      by (metis evalDet p(1,2) simplify xv)
  qed
  done

lemma exp_elim_redundant_false:
 "exp[x | false] \<ge> exp[x]"
  apply auto[1]
  subgoal premises p for m p xa
  proof-
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p(1) by auto
    obtain xb xvv where xvv: "xv = IntVal xb xvv"
      by (metis evalDet evaltree_not_undef intval_is_null.cases intval_or.simps(3,4,5) p(1,2) xv)
    then have evalNotUndef: "val[xv | (IntVal 32 0)] \<noteq> UndefVal"
      using p evalDet xv by blast
    then have widthSame: "xb=32"
      by (metis intval_or.simps(1) new_int_bin.simps xvv)
    then have orUnfold: "val[xv | (IntVal 32 0)] = (new_int xb (or xvv 0))"
      by (simp add: xvv)
    then have simplify: "val[xv | (IntVal 32 0)] = (new_int xb (xvv))"
      by (simp add: orUnfold)
    then have eq: "(xv) = (new_int xb (xvv))"
      using eval_unused_bits_zero xv xvv by auto
    then show ?thesis
      by (metis evalDet p(1) simplify xv)
  qed
  done

text \<open>Optimisations\<close>

optimization OrEqual[nogen]: "exp[x | x] \<longmapsto> x"
  by (meson exp_or_equal)

optimization OrShiftConstantRight[nogen]: 
  when "cond[x instanceof ConstantNode]"
  when "cond[!(y instanceof ConstantNode)]"
  "exp[(x | y)] \<longmapsto> exp[y | x]"
  using is_ConstantExpr_def size_flip_binary
  apply (metis combine_cond_lhs combine_cond_rhs instance_of_const instance_of_not_const)
  using size_flip_binary by (auto simp: BinaryExpr unfold_const val_shift_const_right_helper)

optimization EliminateRedundantFalse: "x | false \<longmapsto> x"
  by (meson exp_elim_redundant_false)

optimization OrNotOperands: "(~x | ~y) \<longmapsto> ~(x & y)"
   apply (metis add_2_eq_Suc' less_SucI not_add_less1 not_less_eq size_binary_const size_non_add)
   using BinaryExpr UnaryExpr bin_eval.simps(4) intval_not.simps(2) unary_eval.simps(3) 
         val_or_not_operands by fastforce

(*
optimization OrLeftFallthrough:
  "x | y \<longmapsto> x when ((and (not (IRExpr_down x)) (IRExpr_up y)) = 0)"
  using simple_mask.OrLeftFallthrough by blast

optimization OrRightFallthrough:
  "x | y \<longmapsto> y when ((and (not (IRExpr_down y)) (IRExpr_up x)) = 0)"
  using simple_mask.OrRightFallthrough by blast
*)


end (* End of OrPhase *)


end (* End of file *)
