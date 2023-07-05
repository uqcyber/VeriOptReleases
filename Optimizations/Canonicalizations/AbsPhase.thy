subsection \<open>AbsNode Phase\<close>

theory AbsPhase
  imports
    Common
begin

phase AbsNode
  terminating size
begin


(* Marks' lemmas *)

lemma abs_pos:
  fixes v :: "('a :: len word)"
  assumes "0 \<le>s v"
  shows "(if v <s 0 then - v else v) = v"
  by (simp add: assms signed.leD)

lemma abs_neg:
  fixes v :: "('a :: len word)"
  assumes "v <s 0"
  assumes "-(2 ^ (Nat.size v - 1)) <s v" (* changed size func used*)
  shows "(if v <s 0 then - v else v) = - v \<and> 0 <s -v"
  by (smt (verit, ccfv_SIG) assms(1) assms(2) signed_take_bit_int_greater_eq_minus_exp 
     signed_take_bit_int_greater_eq_self_iff sint_0 sint_word_ariths(4) word_sless_alt)
 
lemma abs_max_neg:
  fixes v :: "('a :: len word)"
  assumes "v <s 0"
  assumes "- (2 ^ (Nat.size v - 1)) = v" (* changed size func used *)
  shows "-v = v"
  using assms
  by (metis One_nat_def add.inverse_neutral double_eq_zero_iff mult_minus_right size_word.rep_eq)

lemma final_abs:
  fixes v :: "('a :: len word)"
  assumes "take_bit (Nat.size v) v = v"
  assumes "- (2 ^ (Nat.size v - 1)) \<noteq> v" (* changed size func used *)
  shows "0 \<le>s (if v <s 0 then -v else v)"
 
proof (cases "v <s 0")
  case True
  then show ?thesis
  proof (cases "v = - (2 ^ (Nat.size v - 1))") (* changed size func used *)
    case True
    then show ?thesis using abs_max_neg
      using assms by presburger
  next
    case False
    then have "- (2 ^ (Nat.size v - 1)) <s v" (* changed size func used *)
      unfolding word_sless_def using signed_take_bit_int_greater_self_iff
      by (smt (verit, best) One_nat_def diff_less double_eq_zero_iff len_gt_0 lessI less_irrefl 
          mult_minus_right neg_equal_0_iff_equal signed.rep_eq signed_of_int 
          signed_take_bit_int_greater_eq_self_iff signed_word_eqI sint_0 sint_range_size 
          sint_sbintrunc' sint_word_ariths(4) size_word.rep_eq unsigned_0 word_2p_lem 
          word_sless.rep_eq word_sless_def)
    then show ?thesis
      using abs_neg abs_pos signed.nless_le by auto
  qed
next
  case False
  then show ?thesis using abs_pos by auto
qed 

(* end *)

lemma wf_abs: "is_IntVal x \<Longrightarrow> intval_abs x \<noteq> UndefVal"
  using intval_abs.simps unfolding new_int.simps
  using is_IntVal_def by force

fun bin_abs :: "'a ::len word \<Rightarrow> 'a ::len word" where
  "bin_abs v = (if (v <s 0) then (- v) else v)"


(* Helpers - Value level *)
lemma val_abs_zero:
  "intval_abs (new_int b 0) = new_int b 0"
  by simp

lemma less_eq_zero:
  assumes "val_to_bool (val[(IntVal b 0) < (IntVal b v)])"
  shows "int_signed_value b v > 0"
  using assms unfolding intval_less_than.simps(1) apply simp
  by (metis bool_to_val.elims val_to_bool.simps(1))

lemma val_abs_pos:
  assumes "val_to_bool(val[(new_int b 0) < (new_int b v)])"
  shows "intval_abs (new_int b v) = (new_int b v)" 
  using assms using less_eq_zero unfolding intval_abs.simps new_int.simps
  by force

lemma val_abs_neg:
  assumes "val_to_bool(val[(new_int b v) < (new_int b 0)])"
  shows "intval_abs (new_int b v) = intval_negate (new_int b v)" 
  using assms using less_eq_zero unfolding intval_abs.simps new_int.simps
  by force

lemma val_bool_unwrap:
  "val_to_bool (bool_to_val v) = v"
  by (metis bool_to_val.elims one_neq_zero val_to_bool.simps(1))

lemma take_bit_unwrap:
  "b = 64 \<Longrightarrow> take_bit b (v1::64 word) = v1"
  by (metis size64 size_word.rep_eq take_bit_length_eq)

lemma bit_less_eq_def:
  fixes v1 v2 :: "64 word"
  assumes "b \<le> 64"
  shows "sint (signed_take_bit (b - Suc (0::nat)) (take_bit b v1))
    < sint (signed_take_bit (b - Suc (0::nat)) (take_bit b v2)) \<longleftrightarrow>
    signed_take_bit (63::nat) (Word.rep v1) < signed_take_bit (63::nat) (Word.rep v2)"
  using assms sorry
  (* likely untrue but is a very useful simplification temporarily during merging *)
lemma less_eq_def:
  (*assumes "0 < b \<and> b \<le> 64"*)
  shows "val_to_bool(val[(new_int b v1) < (new_int b v2)]) \<longleftrightarrow> v1 <s v2"
  unfolding new_int.simps intval_less_than.simps bool_to_val_bin.simps bool_to_val.simps 
            int_signed_value.simps 
  apply (simp add: val_bool_unwrap) apply auto[1]
  unfolding word_sless_def apply auto[1]
  unfolding signed_def apply auto[1] apply auto[2]
  using bit_less_eq_def apply (metis bot_nat_0.extremum take_bit_0)
  by (metis bit_less_eq_def bot_nat_0.extremum take_bit_0)

lemma val_abs_always_pos:
  assumes "intval_abs (new_int b v) = (new_int b v')"
  shows "0 \<le>s v'"
  using assms
proof (cases "v = 0")
  case True
  then have "v' = 0"
    using val_abs_zero assms
    by (smt (verit, ccfv_threshold) Suc_diff_1 bit_less_eq_def bot_nat_0.extremum diff_is_0_eq 
        len_gt_0 len_of_numeral_defs(2) order_le_less signed_eq_0_iff take_bit_0 
        take_bit_signed_take_bit take_bit_unwrap)
  then show ?thesis by simp
next
  case neq0: False
  then show ?thesis
  proof (cases "val_to_bool(val[(new_int b 0) < (new_int b v)])")
    case True
    then show ?thesis using less_eq_def
      using assms val_abs_pos
      by (smt (verit, ccfv_SIG) One_nat_def Suc_leI bit.compl_one bit_less_eq_def 
          cancel_comm_monoid_add_class.diff_cancel diff_zero len_gt_0 len_of_numeral_defs(2) 
          mask_0 mask_1 one_le_numeral one_neq_zero signed_word_eqI take_bit_dist_subL 
          take_bit_minus_one_eq_mask take_bit_not_eq_mask_diff take_bit_signed_take_bit 
          zero_le_numeral)
  next
    case False
    then have "val_to_bool(val[(new_int b v) < (new_int b 0)])"
      using neq0 less_eq_def
      by (metis signed.neqE)
    then show ?thesis using val_abs_neg less_eq_def unfolding new_int.simps intval_negate.simps
      by (metis signed.nless_le take_bit_0)
  qed
  
qed


lemma intval_abs_elims:
  assumes "intval_abs x \<noteq> UndefVal"
  shows "\<exists>t v . x = IntVal t v \<and> intval_abs x = new_int t (if int_signed_value t v < 0 then - v else v)"
  using assms
  by (meson intval_abs.elims)

lemma wf_abs_new_int:
  assumes "intval_abs (IntVal t v) \<noteq> UndefVal"
  shows "intval_abs (IntVal t v) = new_int t v \<or> intval_abs (IntVal t v) = new_int t (-v)"
  using assms
  using intval_abs.simps(1) by presburger

lemma mono_undef_abs:
  assumes "intval_abs (intval_abs x) \<noteq> UndefVal"
  shows "intval_abs x \<noteq> UndefVal"
  using assms
  by force

(* Value level proofs *)
lemma val_abs_idem:
  assumes "intval_abs(intval_abs(x)) \<noteq> UndefVal"
  shows "intval_abs(intval_abs(x)) = intval_abs x"
  using assms
proof -
  obtain b v where in_def: "intval_abs x = new_int b v"
    using assms intval_abs_elims mono_undef_abs by blast
  then show ?thesis
  proof (cases "val_to_bool(val[(new_int b v) < (new_int b 0)])")
    case True
    then have nested: "(intval_abs (intval_abs x)) = new_int b (-v)"
      using val_abs_neg intval_negate.simps in_def
      by simp
    then have "x = new_int b (-v)"
      using in_def True unfolding new_int.simps
      by (smt (verit, best) intval_abs.simps(1) less_eq_def less_eq_zero less_numeral_extra(1) 
          mask_1 mask_eq_take_bit_minus_one neg_one.elims neg_one_signed new_int.simps 
          one_le_numeral one_neq_zero signed.neqE signed.not_less take_bit_of_0 val_abs_always_pos)
    then show ?thesis using val_abs_always_pos
      using True in_def less_eq_def signed.leD
      using signed.nless_le by blast
  next
    case False
    then show ?thesis
      using in_def by force
  qed
qed
  
lemma val_abs_negate:
  assumes "intval_abs (intval_negate x) \<noteq> UndefVal"
  shows   "intval_abs (intval_negate x) = intval_abs x"
  using assms apply (cases x; auto)
   apply (metis less_eq_def new_int.simps signed.dual_order.strict_iff_not signed.less_linear 
          take_bit_0)
  by (smt (verit, ccfv_threshold) add.inverse_neutral intval_abs.simps(1) less_eq_def less_eq_zero 
      less_numeral_extra(1) mask_1 mask_eq_take_bit_minus_one neg_one.elims neg_one_signed 
      new_int.simps one_le_numeral one_neq_zero signed.order.order_iff_strict take_bit_of_0 
      val_abs_always_pos)


text \<open>Optimisations\<close>

optimization AbsIdempotence: "abs(abs(x)) \<longmapsto>  abs(x)"
   apply auto[1]
  by (metis UnaryExpr unary_eval.simps(1) val_abs_idem)

value AbsIdempotence_code

optimization AbsNegate: "(abs(-x)) \<longmapsto>  abs(x)"
    apply auto[1] using val_abs_negate
  by (metis unary_eval.simps(1) unfold_unary)

value "(AbsIdempotence_code else AbsNegate_code)"


end (* End of AbsPhase *)

end (* End of file *)