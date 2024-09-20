theory DivPhase
imports Common Proofs.StampEvalThms
begin

lemma int_div_itself:
  assumes "x \<noteq> 0"
  shows "(x::int) sdiv x = 1"
  using assms
  by (simp add: signed_divide_int_eq_divide_int)

lemma word_div_itself:
  fixes x :: "'a::len word"
  assumes "x \<noteq> 0"
  shows "(sint x) sdiv (sint x) = 1"
  using int_div_itself
  by (simp add: assms signed_eq_0_iff)

lemma word64_div_itself:
  fixes x :: "64 word"
  assumes "take_bit b x \<noteq> 0"
  shows "(int_signed_value b x) sdiv (int_signed_value b x) = 1"
  using int_div_itself
  by (metis (no_types, opaque_lifting) Suc_pred' add_0_left add_implies_diff assms bot_nat_0.not_eq_extremum diff_le_self dual_order.refl int_signed_value.simps signed_eq_0_iff take_bit_of_0 take_bit_signed_take_bit)

fun valid_int :: "Value \<Rightarrow> bool" where
  "valid_int (IntVal b v) = (0 < b \<and> b \<le> 64 \<and> take_bit b v = v)" |
  "valid_int _ = False"

lemma value_div_itself:
  assumes "val[x / x] = IntVal b v"
  assumes "valid_int x"
  assumes "x \<noteq> val[IntVal b 0]"
  shows "val[x / x] = val[IntVal b 1]"
  using assms apply (cases x)
  apply simp
  using word64_div_itself
  apply (smt (verit) IntVal1 Value.distinct(1) bot_nat_0.not_eq_extremum intval_div.simps(1) intval_word.simps new_int.simps new_int_bin.elims of_int_1 take_bit_numeral_1 take_bit_of_1 take_bit_of_1_eq_0_iff valid_int.simps(1))
  by simp+

phase DivPhase
  terminating size
begin

optimization DivItself: 
  when "wf_stamp x"
  when "(stamp_expr x = IntegerStamp b lo hi)"
  "(x / x) \<longmapsto> (const (IntVal b 1))"
  using size_non_const apply force
  apply simp apply (rule impI; (rule allI)+; rule impI)
  subgoal premises p for m p v
  proof -
    obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
      using p(2)
      by (metis BinaryExprE p(1) valid_int wf_stamp_def)
    then have "intval_div (IntVal b xv) (IntVal b xv) \<noteq> UndefVal"
      using p(2)
      by (metis bin_eval.simps(4) evalDet unfold_binary)
    then have "xv \<noteq> 0"
      by force
    then show ?thesis
      using value_div_itself
      by (metis (no_types, lifting) BinaryExprE xv bin_eval.simps(4) evalDet eval_bits_1_64 eval_unused_bits_zero intval_div.simps(1) new_int.simps new_int_bin.elims p(2) unfold_const validDefIntConst valid_int.simps(1) wf_value_def)
  qed
  done

thm_oracles DivItself

end

end