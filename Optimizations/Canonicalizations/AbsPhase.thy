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
  apply (rule conjI) using assms apply simp
  by (smt (verit, del_insts) assms signed_take_bit_int_greater_eq_minus_exp sint_word_ariths(4)
      word_sless_alt signed_take_bit_int_greater_eq_self_iff sint_0)
 
lemma abs_max_neg:
  fixes v :: "('a :: len word)"
  assumes "v <s 0"
  assumes "- (2 ^ (Nat.size v - 1)) = v" (* changed size func used *)
  shows "-v = v"
  by (metis One_nat_def add.inverse_neutral double_eq_zero_iff mult_minus_right size_word.rep_eq 
      assms(2))

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
    then show ?thesis 
      using assms by presburger
  next
    case False
    then have "- (2 ^ (Nat.size v - 1)) <s v" (* changed size func used *)
      by (smt (verit, best) One_nat_def diff_less double_eq_zero_iff len_gt_0 lessI less_irrefl 
          mult_minus_right neg_equal_0_iff_equal signed.rep_eq signed_of_int signed_word_eqI
          signed_take_bit_int_greater_eq_self_iff sint_0 sint_range_size sint_word_ariths(4)
          sint_sbintrunc' size_word.rep_eq unsigned_0 word_2p_lem word_sless.rep_eq
          signed_take_bit_int_greater_self_iff)
    then show ?thesis
      using abs_neg signed.nless_le by auto
  qed
next
  case False
  then show ?thesis 
    using abs_pos by auto
qed 

(* end *)

lemma wf_abs: "is_IntVal x \<Longrightarrow> intval_abs x \<noteq> UndefVal"
  using is_IntVal_def by auto

fun bin_abs :: "'a ::len word \<Rightarrow> 'a ::len word" where
  "bin_abs v = (if (v <s 0) then (- v) else v)"

(* Helpers - Value level *)
lemma val_abs_zero:
  "intval_abs (new_int b 0) = new_int b 0"
  by simp

lemma less_eq_zero:
  assumes "val_to_bool (val[(IntVal b 0) < (IntVal b v)])"
  shows "int_signed_value b v > 0"
  using bool_to_val.elims assms by fastforce

lemma val_abs_pos:
  assumes "val_to_bool(val[(new_int b 0) < (new_int b v)])"
  shows "intval_abs (new_int b v) = (new_int b v)"
  using assms by force

lemma val_abs_neg:
  assumes "val_to_bool(val[(new_int b v) < (new_int b 0)])"
  shows "intval_abs (new_int b v) = intval_negate (new_int b v)"
  using assms by force

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
  apply (simp add: val_bool_unwrap word_sless_def)
  using bit_less_eq_def unfolding signed_def by fastforce

lemma val_abs_always_pos:
  assumes "intval_abs (new_int b v) = (new_int b v')"
  shows "0 \<le>s v'"
proof (cases "v = 0")
  case True
  then have isZero: "intval_abs (new_int b 0) = new_int b 0"
    by auto
  then have "v' = 0"
    by (metis True less_eq_def signed.not_less_iff_gr_or_eq assms)
  then show ?thesis by simp
next
  case neq0: False
  then show ?thesis
  proof (cases "val_to_bool(val[(new_int b 0) < (new_int b v)])")
    case True
    then have "0 \<le>s v'"
      by (metis True assms less_eq_def signed.less_imp_le val_abs_pos)
    then show ?thesis
      by blast
  next
    case False
    then have "val_to_bool(val[(new_int b v) < (new_int b 0)])"
      by (metis signed.neqE neq0 less_eq_def)
    then show ?thesis
      by (metis signed.nless_le take_bit_0 new_int.simps less_eq_def)
  qed
qed

lemma intval_abs_elims:
  assumes "intval_abs x \<noteq> UndefVal"
  shows "\<exists>t v . x = IntVal t v \<and> 
                    intval_abs x = new_int t (if int_signed_value t v < 0 then - v else v)"
  by (meson intval_abs.elims assms)

lemma wf_abs_new_int:
  assumes "intval_abs (IntVal t v) \<noteq> UndefVal"
  shows "intval_abs (IntVal t v) = new_int t v \<or> intval_abs (IntVal t v) = new_int t (-v)" 
  by simp

lemma mono_undef_abs:
  assumes "intval_abs (intval_abs x) \<noteq> UndefVal"
  shows "intval_abs x \<noteq> UndefVal"
  using assms by force

(* Value level proofs *)
lemma val_abs_idem:
  assumes "intval_abs(intval_abs(x)) \<noteq> UndefVal"
  shows "intval_abs(intval_abs(x)) = intval_abs x"
proof -
  obtain b v where in_def: "intval_abs x = new_int b v"
    using assms intval_abs_elims mono_undef_abs by blast
  then show ?thesis
  proof (cases "val_to_bool(val[(new_int b v) < (new_int b 0)])")
    case True
    then have nested: "(intval_abs (intval_abs x)) = new_int b (-v)"
      using val_abs_neg in_def by simp
    then have "x = new_int b (-v)"
      by (metis take_bit_0 val_abs_zero less_eq_def new_int.simps signed.not_less val_abs_always_pos
          True)
    then show ?thesis
      using val_abs_always_pos True in_def less_eq_def signed.leD by blast
  next
    case False
    then show ?thesis
      using in_def by fastforce
  qed
qed
  
lemma val_abs_negate:
  assumes "intval_abs val[-x] \<noteq> UndefVal"
  shows   "intval_abs val[-x] = intval_abs x"
  using less_eq_def
  by (metis (no_types, opaque_lifting) new_int.simps zero_neq_one take_bit_0 signed.less_linear 
      signed.dual_order.strict_iff_not)

text \<open>Optimisations\<close>

optimization AbsIdempotence: "abs(abs(x)) \<longmapsto> abs(x)"
  using val_abs_idem by auto

value AbsIdempotence_code

optimization AbsNegate: "(abs(-x)) \<longmapsto>  abs(x)"
  using val_abs_negate by auto

value "(AbsIdempotence_code else AbsNegate_code)"


end (* End of AbsPhase *)

end (* End of file *)