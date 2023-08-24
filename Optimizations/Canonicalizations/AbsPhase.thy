subsection \<open>AbsNode Phase\<close>

theory AbsPhase
  imports
    Common Proofs.StampEvalThms
begin

phase AbsNode
  terminating size
begin

text \<open>
Note:

We can't use @{const word_sless} for reasoning about @{const intval_less_than}.
@{const word_sless} will always treat the 64^{th} bit as the sign flag
while @{const intval_less_than} uses the b^{th} bit depending on the size of the word.
\<close>

value "val[new_int 32 0 < new_int 32 4294967286]" \<comment> \<open>0 < -10 = False\<close>
value "(0::int64) <s 4294967286" \<comment> \<open>0 < 4294967286 = True\<close>


lemma signed_eqiv:
  assumes "b > 0 \<and> b \<le> 64"
  shows "val_to_bool (val[new_int b v < new_int b v']) = (int_signed_value b v < int_signed_value b v')"
  using assms
  by (metis (no_types, lifting) ValueThms.signed_take_take_bit bool_to_val.elims bool_to_val_bin.elims int_signed_value.simps intval_less_than.simps(1) new_int.simps one_neq_zero val_to_bool.simps(1))

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


lemma take_bit_64:
  assumes "0 < b \<and> b \<le> 64"
  assumes "take_bit b v = v"
  shows "take_bit 64 v = take_bit b v"
  using assms
  by (metis min_def nle_le take_bit_take_bit)


text \<open>
A special value exists for the maximum negative integer as its negation is itself.
We can define the value as @{term "(set_bit (b - 1) 0)::int64"} for any bit-width, b.
\<close>

value "(set_bit 1 0)::2 word" \<comment> \<open>2\<close>
value "-(set_bit 1 0)::2 word" \<comment> \<open>2\<close>
value "(set_bit 31 0)::32 word" \<comment> \<open>2147483648\<close>
value "-(set_bit 31 0)::32 word" \<comment> \<open>2147483648\<close>

lemma negate_horner:
  fixes v :: "'a::len word"
  shows "-v = (horner_sum of_bool 2 (map (\<lambda>i. \<not>(bit v i)) [0..<LENGTH('a)])) + 1"
  sorry


lemma negative_def:
  fixes v :: "'a::len word"
  assumes "v <s 0"
  shows "bit v (LENGTH('a) - 1)"
  using assms
  by (simp add: bit_last_iff word_sless_alt)

lemma positive_def:
  fixes v :: "'a::len word"
  assumes "0 <s v"
  shows "\<not>(bit v (LENGTH('a) - 1))"
  using assms
  by (simp add: bit_last_iff word_sless_alt)

lemma invert:
  fixes v :: "'a::len word"
  assumes "v <s 0"
  assumes "v \<noteq> (set_bit (LENGTH('a) - 1) 0)"
  shows "0 <s (-v)"
proof -
  have negBitSet: "bit v (LENGTH('a) - 1)"
    using assms(1)
    using negative_def by blast
  have "v = (horner_sum of_bool 2 (map (\<lambda>i. (bit v i)) [0..<LENGTH('a)]))"
    by (simp add: horner_sum_bit_eq_take_bit)
  then have "-v = (horner_sum of_bool 2 (map (\<lambda>i. \<not>(bit v i)) [0..<LENGTH('a)])) + 1"
    using negate_horner by blast
  then have "\<not>(bit v (LENGTH('a) - 1))"
    sorry
  then show ?thesis
    using negBitSet by blast
qed

text \<open>We need to do the same proof at the value level.\<close>

lemma invert_intval:
  assumes "int_signed_value b v < 0"
  assumes "b > 0 \<and> b \<le> 64"
  assumes "take_bit b v = v"
  assumes "v \<noteq> (set_bit (b - 1) 0)"
  shows "0 < int_signed_value b (-v)"
  using assms apply simp sorry

lemma negate_max_negative:
  assumes "b > 0 \<and> b \<le> 64"
  assumes "take_bit b v = v"
  assumes "v = (set_bit (b - 1) 0)"
  shows "new_int b v = intval_negate (new_int b v)"
  using assms apply simp sorry

lemma val_abs_always_pos:
  assumes "b > 0 \<and> b \<le> 64"
  assumes "take_bit b v = v"
  assumes "v \<noteq> (set_bit (b - 1) 0)"
  assumes "intval_abs (new_int b v) = (new_int b v')"
  shows "val_to_bool (val[(new_int b 0) < (new_int b v')]) \<or> val_to_bool (val[(new_int b 0) eq (new_int b v')])"
proof (cases "v = 0")
  case True
  then have isZero: "intval_abs (new_int b 0) = new_int b 0"
    by auto
  then have "IntVal b 0 = new_int b v'"
    using True assms by auto
  then have "val_to_bool (val[(new_int b 0) eq (new_int b v')])"
    by simp
  then show ?thesis by simp
next
  case neq0: False
  have zero: "int_signed_value b 0 = 0"
    by simp
  then show ?thesis
  proof (cases "int_signed_value b v > 0")
    case True
    then have "val_to_bool(val[(new_int b 0) < (new_int b v)])"
      using zero apply simp
      by (metis One_nat_def ValueThms.signed_take_take_bit assms(1) val_bool_unwrap)
    then have "val_to_bool (val[new_int b 0 < new_int b v'])"
      by (metis assms(4) val_abs_pos)
    then show ?thesis
      by blast
  next
    case neg: False
    then have "val_to_bool (val[new_int b 0 < new_int b v'])"
    proof -
      have "int_signed_value b v \<le> 0"
        using assms neg neq0 by simp
      then show ?thesis
      proof (cases "int_signed_value b v = 0")
        case True
        then have "v = 0"
          by (metis One_nat_def Suc_pred assms(1) assms(2) dual_order.refl int_signed_value.simps signed_eq_0_iff take_bit_of_0 take_bit_signed_take_bit)
        then show ?thesis
          using neq0 by simp
      next
        case False
        then have "int_signed_value b v < 0"
          using \<open>int_signed_value (b::nat) (v::64 word) \<sqsubseteq> (0::int)\<close> by linarith
        then have "new_int b v' = new_int b (-v)"
          using assms using intval_abs.elims
          by simp
        then have "0 < int_signed_value b (-v)"
          using assms(3) invert_intval
          using \<open>int_signed_value (b::nat) (v::64 word) < (0::int)\<close> assms(1) assms(2) by blast
        then show ?thesis
          using \<open>new_int (b::nat) (v'::64 word) = new_int b (- (v::64 word))\<close> assms(1) signed_eqiv zero by presburger
      qed
    qed
    then show ?thesis
      by simp
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
  assumes "valid_value x (IntegerStamp b l h)"
  assumes "val[abs(abs(x))] \<noteq> UndefVal"
  shows "val[abs(abs(x))] = val[abs x]"
proof -
  obtain b v where in_def: "x = IntVal b v"
    using assms intval_abs_elims mono_undef_abs by blast
  then have bInRange: "b > 0 \<and> b \<le> 64"
    using assms(1)
    by (metis valid_stamp.simps(1) valid_value.simps(1))
  then show ?thesis
  proof (cases "int_signed_value b v < 0")
    case neg: True
    then show ?thesis
    proof (cases "v = (set_bit (b - 1) 0)")
      case min: True
      then show ?thesis
        by (smt (z3) assms(1) bInRange in_def intval_abs.simps(1) intval_negate.simps(1) negate_max_negative new_int.simps valid_value.simps(1))
    next
      case notMin: False
      then have nested: "(intval_abs x) = new_int b (-v)"
        using neg val_abs_neg in_def by simp
      also have "int_signed_value b (-v) > 0"
        using neg notMin invert_intval bInRange
        by (metis assms(1) in_def valid_value.simps(1))
      then have "(intval_abs (new_int b (-v))) = new_int b (-v)"
        by (smt (verit, best) ValueThms.signed_take_take_bit bInRange int_signed_value.simps intval_abs.simps(1) new_int.simps new_int_unused_bits_zero)
      then show ?thesis
        using nested by presburger
    qed
  next
    case False
    then show ?thesis
      by (metis (mono_tags, lifting) assms(1) in_def intval_abs.simps(1) new_int.simps valid_value.simps(1))
  qed
qed

paragraph \<open>Optimisations\<close>

optimization AbsIdempotence:
  "abs(abs(x)) \<longmapsto> abs(x) when wf_stamp x \<and> stamp_expr x = IntegerStamp b l h"
  using val_abs_idem
  using wf_stamp_def by fastforce

end

end