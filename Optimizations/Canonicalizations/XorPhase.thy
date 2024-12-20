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
 "bin[x ^ x] = 0"
  by simp

lemma bin_xor_commute:
 "bin[x ^ y] = bin[y ^ x]"
  by (simp add: xor.commute)

lemma bin_eliminate_redundant_false:
 "bin[x ^ 0] = bin[x]"
  by simp

(* Value level proofs *)
lemma val_xor_self_is_false:
  assumes "val[x ^ x] \<noteq> UndefVal"
  shows "val_to_bool (val[x ^ x]) = False"
  by (cases x; auto simp: assms)

lemma val_xor_self_is_false_2:
  assumes "val[x ^ x] \<noteq> UndefVal"
  and     "x = IntVal 32 v" 
  shows "val[x ^ x] = bool_to_val False"
  by (auto simp: assms)

(* Not sure if I need this; Optimization uses ConstantExpr False which is IntVal32 0 *)
lemma val_xor_self_is_false_3:
  assumes "val[x ^ x] \<noteq> UndefVal \<and> x = IntVal 64 v" 
  shows "val[x ^ x] = IntVal 64 0"
  by (auto simp: assms)

lemma val_xor_commute:
   "val[x ^ y] = val[y ^ x]"
  by (cases x; cases y; auto simp: xor.commute)

lemma val_eliminate_redundant_false:
  assumes "x = new_int b v"
  assumes "val[x ^ (bool_to_val False)] \<noteq> UndefVal"
  shows   "val[x ^ (bool_to_val False)] = x"
  using assms by (auto; meson)

lemma bit_wf_stamp:
  assumes "wf_stamp x"
  assumes "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
  assumes "stamp_expr x = IntegerStamp b' l h d u"
  shows "b = b'"
  using assms unfolding wf_stamp_def using valid_value.simps(1)
  using valid_value.elims(2) by fastforce

(* Exp level proofs *)
lemma exp_xor_self_is_false:
 assumes "wf_stamp x \<and> stamp_expr x = default_stamp" 
 shows   "exp[x ^ x] \<ge> exp[false]" 
  apply simp apply (rule allI)+ apply (rule impI)
  subgoal premises p for m p v
  proof -
    obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> IntVal 32 xv"
      using p bit_wf_stamp assms unfolding default_stamp_def unrestricted_stamp.simps
      by (metis EvalTreeE(5) assms(1) valid_value_elims(3) wf_stamp_def)
    then have e: "[m, p] \<turnstile> BinaryExpr BinXor x x \<mapsto> intval_xor (IntVal 32 xv) (IntVal 32 xv)"
      using p
      using evalDet by auto
    then have c: "[m, p] \<turnstile> (ConstantExpr (IntVal 32 0)) \<mapsto> (IntVal 32 0)"
      using wf_value_def valid_value.simps constantAsStamp.simps
      by (metis ConstantExpr IntVal0 Value.inject(1) eval_bits_1_64 new_int.simps validDefIntConst xv)
    have "intval_xor (IntVal 32 xv) (IntVal 32 xv) = IntVal 32 0"
      unfolding intval_xor.simps new_int_bin.simps by auto
    then show ?thesis using p e evalDet
      by (metis c)
  qed
  done

lemma exp_eliminate_redundant_false:
  shows "exp[x ^ false] \<ge> exp[x]"
  using val_eliminate_redundant_false apply auto[1]
  subgoal premises p for m p xa
    proof -
      obtain xa where xa: "[m, p] \<turnstile> x \<mapsto> xa"
        using p(2) by blast
      then have "val[xa ^ (IntVal 32 0)] \<noteq> UndefVal"
        using evalDet p(2,3) by blast
      then have "[m, p] \<turnstile> x \<mapsto> val[xa ^ (IntVal 32 0)]"
        using eval_unused_bits_zero xa by (cases xa; auto)
      then show ?thesis
        using evalDet p(2) xa by blast
    qed
  done

text \<open>Optimisations\<close>

(*TODO(BW)
optimization XorSelfIsFalse:
  when "wf_stamp x"
  when "cond[x..stamp() eq (Stamp default_stamp)]"
  "(x ^ x) \<longmapsto> false when
                      (WellFormed x; IsStamp x default_stamp)"
  using size_non_const exp_xor_self_is_false apply simp
  using StampEvalThms.wf_stamp_def exp_xor_self_is_false by auto 
*)

optimization XorShiftConstantRight: 
  when "cond[x instanceof ConstantNode]"
  when "cond[!(y instanceof ConstantNode)]"
  "(x ^ y) \<longmapsto> (y ^ x)"
  apply (metis IRExpr.collapse(6) combine_cond_lhs combine_cond_rhs instance_of_const instance_of_not_const size_flip_binary)
  using size_flip_binary val_xor_commute by auto

optimization EliminateRedundantFalse: 
  "(x ^ false) \<longmapsto> x"
  using exp_eliminate_redundant_false by simp 

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
