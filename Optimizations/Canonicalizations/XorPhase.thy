subsection \<open>XorNode Phase\<close>

theory XorPhase
  imports
    Common
    Proofs.StampEvalThms
begin

phase XorNode
  terminating size
begin

(* Word level proofs *)
lemma bin_xor_self_is_false:
 "bin[x \<oplus> x] = 0"
  by simp

lemma bin_xor_commute:
 "bin[x \<oplus> y] = bin[y \<oplus> x]"
  by (simp add: xor.commute)

lemma bin_eliminate_redundant_false:
 "bin[x \<oplus> 0] = bin[x]"
  by simp

(* Value level proofs *)
lemma val_xor_self_is_false:
  assumes "val[x \<oplus> x] \<noteq> UndefVal"
  shows "val_to_bool (val[x \<oplus> x]) = False"
  by (cases x; auto simp: assms)

lemma val_xor_self_is_false_2:
  assumes "val[x \<oplus> x] \<noteq> UndefVal"
  and     "x = IntVal 32 v" 
  shows "val[x \<oplus> x] = bool_to_val False"
  by (auto simp: assms)

(* Not sure if I need this; Optimization uses ConstantExpr False which is IntVal32 0 *)
lemma val_xor_self_is_false_3:
  assumes "val[x \<oplus> x] \<noteq> UndefVal \<and> x = IntVal 64 v" 
  shows "val[x \<oplus> x] = IntVal 64 0"
  by (auto simp: assms)

lemma val_xor_commute:
   "val[x \<oplus> y] = val[y \<oplus> x]"
  by (cases x; cases y; auto simp: xor.commute)

lemma val_eliminate_redundant_false:
  assumes "x = new_int b v"
  assumes "val[x \<oplus> (bool_to_val False)] \<noteq> UndefVal"
  shows   "val[x \<oplus> (bool_to_val False)] = x"
  using assms by (auto; meson)

(* Exp level proofs *)
lemma exp_xor_self_is_false:
 assumes "wf_stamp x \<and> stamp_expr x = default_stamp" 
 shows   "exp[x \<oplus> x] \<ge> exp[false]" 
  using assms apply auto[1] unfolding wf_stamp_def
  by (smt (z3) validDefIntConst IntVal0 Value.inject(1) bool_to_val.simps(2) 
      constantAsStamp.simps(1) evalDet int_signed_value_bounds new_int.simps unfold_const 
      val_xor_self_is_false_2 valid_int valid_stamp.simps(1) valid_value.simps(1) wf_value_def)

lemma exp_eliminate_redundant_false:
  shows "exp[x \<oplus> false] \<ge> exp[x]"
  using val_eliminate_redundant_false apply auto[1]
  subgoal premises p for m p xa
    proof -
      obtain xa where xa: "[m, p] \<turnstile> x \<mapsto> xa"
        using p(2) by blast
      then have "val[xa \<oplus> (IntVal 32 0)] \<noteq> UndefVal"
        using evalDet p(2,3) by blast
      then have "[m, p] \<turnstile> x \<mapsto> val[xa \<oplus> (IntVal 32 0)]"
        using eval_unused_bits_zero xa by (cases xa; auto)
      then show ?thesis
        using evalDet p(2) xa by blast
    qed
  done

text \<open>Optimisations\<close>

optimization XorSelfIsFalse: "(x \<oplus> x) \<longmapsto> false when 
                      (wf_stamp x \<and> stamp_expr x = default_stamp)"
  using size_non_const exp_xor_self_is_false by auto 

optimization XorShiftConstantRight: "(x \<oplus> y) \<longmapsto> y \<oplus> x when IsConstantExpr x && Not (IsConstantExpr y)"
  apply (metis IRExpr.collapse(6) size_flip_binary)
  using size_flip_binary val_xor_commute by auto

optimization EliminateRedundantFalse: "(x \<oplus> false) \<longmapsto> x"
    using exp_eliminate_redundant_false by auto 

(* BW: this doesn't seem right *)
(* Doesn't have any subgoals *)
(*
optimization MaskOutRHS: "(x \<oplus> y) \<longmapsto> ~x
                          when (is_ConstantExpr y
                             \<and> (stamp_expr (BinaryExpr BinXor x y) = IntegerStamp stampBits l h) 
                             \<and> (BinaryExpr BinAnd y (ConstantExpr (new_int stampBits (not 0))) 
                                                   = ConstantExpr (new_int stampBits (not 0))))"
  sorry
*)

end (* End of XorPhase *)

end (* End of file *)
