subsection \<open>NegateNode Phase\<close>

theory NegatePhase
  imports
    Common
begin

phase NegateNode
  terminating size
begin

(* Word level proofs *)
lemma bin_negative_cancel:
 "-1 * (-1 * ((x::('a::len) word))) = x"
  by auto

(* Value level proofs *)
lemma val_negative_cancel:
  assumes "val[-(new_int b v)] \<noteq> UndefVal"
  shows   "val[-(-(new_int b v))] = val[new_int b v]"
  by simp

lemma val_distribute_sub:
  assumes "x \<noteq> UndefVal \<and> y \<noteq> UndefVal"
  shows   "val[-(x - y)] = val[y - x]"
  by (cases x; cases y; auto)

(* Exp level proofs *)
lemma exp_distribute_sub:
  shows "exp[-(x - y)] \<ge> exp[y - x]"
  by (auto simp: val_distribute_sub evaltree_not_undef)

thm_oracles exp_distribute_sub

lemma exp_negative_cancel:
  shows "exp[-(-x)] \<ge> exp[x]"
  apply auto[1]
  by (metis (no_types, opaque_lifting) eval_unused_bits_zero intval_negate.elims new_int.simps
      intval_negate.simps(1) minus_equation_iff take_bit_dist_neg) 
 
lemma exp_negative_shift: 
  assumes "stamp_expr x = IntegerStamp b' lo hi d u" 
  and     "unat y = (b' - 1)"
  shows   "exp[-(x >> (const (new_int b y)))] \<ge> exp[x >>> (const (new_int b y))]"
  apply auto[1]
  subgoal premises p for m p xa
  proof - 
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p(2) by auto
    then have 1: "val[-(xa >> (IntVal b (take_bit b y)))] \<noteq> UndefVal"
      using evalDet p(1,2) by blast
    then have 2: "val[xa >> (IntVal b (take_bit b y))] \<noteq> UndefVal"
      by auto
    then have 4: "sint (signed_take_bit (b - Suc (0::nat)) (take_bit b y)) < (2::int) ^ b div (2::int)"
      by (metis Suc_le_lessD Suc_pred eval_bits_1_64 int_power_div_base p(4) zero_less_numeral
          signed_take_bit_int_less_exp_word size64 unfold_const wsst_TYs(3))
    then have 5: "(0::nat) < b"
      using eval_bits_1_64 p(4) by blast
    then have 6: "b \<sqsubseteq> (64::nat)"
      using eval_bits_1_64 p(4) by blast
    then have 7: "[m,p] \<turnstile> BinaryExpr BinURightShift x
                 (ConstantExpr (IntVal b (take_bit b y))) \<mapsto> 
                  intval_negate (intval_right_shift xa (IntVal b (take_bit b y)))"
      apply (cases y; auto)

      subgoal premises p for n
        proof - 
          have sg1: "y = word_of_nat n"
            by (simp add: p(1))
          then have sg2: "n < (18446744073709551616::nat)"
            by (simp add: p(2))
          then have sg3: "b \<sqsubseteq> (64::nat)"
            by (simp add: "6")
          then have sg4: "[m,p] \<turnstile> BinaryExpr BinURightShift x
                 (ConstantExpr (IntVal b (take_bit b (word_of_nat n)))) \<mapsto> 
                  intval_negate (intval_right_shift xa (IntVal b (take_bit b (word_of_nat n))))"
             sorry
          then show ?thesis
            by simp
        qed 
      done
    then show ?thesis
      by (metis evalDet p(2) xa)
  qed 
  done


text \<open>Optimisations\<close>

optimization NegateCancel: "-(-(x)) \<longmapsto> x"
  using exp_negative_cancel by blast 

(* FloatStamp condition is omitted. Not 100% sure. *)
optimization DistributeSubtraction: "-(x - y) \<longmapsto> (y - x)"
  apply (smt (verit, best) add.left_commute add_2_eq_Suc' add_diff_cancel_left' is_ConstantExpr_def
         less_Suc_eq_0_disj plus_1_eq_Suc size.simps(11) size_binary_const size_non_add
         zero_less_diff exp_distribute_sub nat_add_left_cancel_less less_add_eq_less add_Suc lessI
         trans_less_add2 size_binary_rhs Suc_eq_plus1 Nat.add_0_right old.nat.inject
         zero_less_Suc)
   using exp_distribute_sub by simp

(* Need to prove exp_negative_shift *)
(*
optimization NegativeShift: "-(x >> (const (new_int b y))) \<longmapsto> x >>> (const (new_int b y))
                                   when (stamp_expr x = IntegerStamp b' lo hi \<and> unat y = (b' - 1))"
  using exp_negative_shift by simp 
*)

end (* End of NegatePhase *)

end (* End of file *)
