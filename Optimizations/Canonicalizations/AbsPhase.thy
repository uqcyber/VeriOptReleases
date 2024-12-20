subsection \<open>AbsNode Phase\<close>

theory AbsPhase
  imports
    Common Proofs.StampEvalThms
begin

phase AbsNode
  terminating size
begin

fun abs :: "nat \<Rightarrow> 64 word \<Rightarrow> 64 word" where
  "abs b x = (if b \<turnstile> x <j 0 then take_bit b (-x) else take_bit b x)"

lemma positive_abs:
  assumes "b \<turnstile> 0 \<le>j ve"
  shows "abs b ve = take_bit b ve"
  using assms
  by simp

lemma min_int_negative:
  assumes "0 < b \<and> b \<le> 64"
  shows "b \<turnstile> min_int b <j 0"
  using assms min_int_signed by auto

lemma abs_min_int:
  assumes "0 < b \<and> b \<le> 64"
  assumes "ve = min_int b"
  shows "abs b ve = take_bit b (-ve)"
  using assms min_int_negative by simp

value "min_int 1"
value "-(min_int 1)"
value "min_int 4"
value "-(min_int 4)"

lemma negative_abs_signed:
  assumes "0 < b \<and> b \<le> 64"
  shows "signed_take_bit (b-1) (take_bit b (-(min_int b))) = signed_take_bit (b-1) (min_int b)"
  using assms
  by (smt (verit) JavaWords.take_bit_dist_neg ValueThms.signed_take_take_bit diff_diff_cancel diff_is_0_eq' less_le_not_le mask_1 mask_eq_take_bit_minus_one min_int_push_bit min_int_signed_neg2pow not_less push_bit_of_1 take_bit_push_bit)

lemma negative_abs':
  assumes "0 < b \<and> b \<le> 64"
  assumes "v = (min_int b)"
  shows "take_bit b (-v) = take_bit b v"
  using assms
  by (metis (no_types, lifting) JavaWords.signed_take_take_bit Suc_pred' negative_abs_signed signed_take_bit_eq_iff_take_bit_eq)

lemma negative_abs:
  assumes "0 < b \<and> b \<le> 64"
  assumes "v = take_bit b (min_int b)"
  shows "take_bit b (-v) = v"
  using assms
  by (metis (no_types, lifting) One_nat_def Suc_leI diff_diff_cancel mask_1 mask_eq_take_bit_minus_one min_int_push_bit min_int_signed_neg2pow push_bit_of_1 take_bit_push_bit)

lemma jlt_zero_sign_bit:
  assumes "0 < b \<and> b \<le> 64"
  shows "(b \<turnstile> v <j 0) = bit v (b-1)"
proof -
  have "(b \<turnstile> v <j 0) = (signed_take_bit (b-1) v <s signed_take_bit (b-1) 0)"
    by (simp add: word_sless_alt)
  have "... = (signed_take_bit (b-1) v <s 0)"
    by simp
  have "bit v (b-1) = bit (sint (signed_take_bit (b-1) v)) (b-1)"
    by (smt (verit, ccfv_threshold) assms bit.compl_one bit_mask_iff bit_not_iff bit_or_iff bit_push_bit_iff bit_sint_iff bit_take_bit_iff cancel_comm_monoid_add_class.diff_cancel len_of_numeral_defs(2) linordered_nonzero_semiring_class.zero_le_one min_int_def min_int_signed_neg2pow minus_1_eq_mask more_arith_simps(5) not_less_zero of_bool_eq(2) of_bool_eq(2) order_less_le power_0 power_strict_increasing_iff push_bit_bit_set signed_take_bit_def signed_take_bit_eq_if_positive take_bit_not_mask_eq_0)
  then show ?thesis 
    using assms
    by (smt (verit) JavaWords.signed_take_bit_int_greater_eq_minus_exp_word JavaWords.signed_take_bit_int_less_exp_word bit_mask_iff bit_minus_1_iff bit_push_bit_iff int_signed_value.simps minus_1_eq_mask push_bit_bit_set signed_take_bit_int_less_eq_self_iff signed_take_bit_int_less_self_iff signed_take_bit_negative_iff signed_take_bit_of_0 sint_0)
qed

lemma jgte_zero_sign_bit:
  assumes "0 < b \<and> b \<le> 64"
  shows "(b \<turnstile> 0 \<le>j v) = (\<not>(bit v (b-1)))"
  using assms jlt_zero_sign_bit verit_comp_simplify(3) by blast

lemma jlte_jlt:
  assumes "0 < b \<and> b \<le> 64"
  shows "(b \<turnstile> x \<le>j y) = ((b \<turnstile> x <j y) \<or> (signed_take_bit (b-1) x = signed_take_bit (b-1) y))"
  by (smt (verit, best) int_signed_value.simps signed_word_eqI)

lemma jgt_zero_sign_bit:
  assumes "0 < b \<and> b \<le> 64"
  shows "(b \<turnstile> 0 <j v) \<Longrightarrow> (\<not>(bit v (b-1)))"
  using assms jgte_zero_sign_bit less_le_not_le by blast

thm take_bit_incr_eq

lemma take_bit_incr_eq_word: \<comment>\<open>Borrowed proof strategy from @{thm take_bit_incr_eq}\<close>
  fixes k :: "'a::len word"
  assumes "n < LENGTH('a)"
  assumes "take_bit n k = k"
  assumes "take_bit n k \<noteq> 2 ^ n - 1"
  shows \<open>take_bit n (k + 1) = 1 + take_bit n k\<close>
proof -
  from assms have \<open>2 ^ n \<noteq> k mod 2 ^ n + 1\<close>
    by (metis add_diff_cancel_right' take_bit_mod)
  moreover have \<open>k mod 2 ^ n < 2 ^ n\<close>
    by (metis and_mask_less' assms(1) take_bit_eq_mask take_bit_eq_mod)
  ultimately have *: \<open>k mod 2 ^ n + 1 < 2 ^ n\<close>
    by (smt (verit) len_gt_0 of_bool_eq(2) one_mod_2_pow_eq uint_2p uint_arith_simps(5) uint_word_ariths(8) unsigned_less word_arith_wis(1) word_greater_zero_iff word_less_iff_unsigned word_of_int_2p)
  have \<open>(k + 1) mod 2 ^ n = (k mod 2 ^ n + 1) mod 2 ^ n\<close>
    by (metis assms(2) take_bit_eq_mod)
  also have \<open>\<dots> = k mod 2 ^ n + 1\<close>
    using *
    using mod_word_less by blast
  finally have \<open>(k + 1) mod 2 ^ n = k mod 2 ^ n + 1\<close> .
  then show ?thesis
    by (simp add: take_bit_eq_mod)
qed

thm take_bit_redundant

value "mask 3::int64"

lemma bit_invariant_not_mask:
  fixes v :: "'a::len word"
  assumes "0 < b \<and> b \<le> LENGTH('a)"
  assumes "v \<noteq> mask b"
  assumes "take_bit b v = v"
  shows "bit v b = bit (v + 1) b"
  using assms
  by (metis (no_types, lifting) Groups.add_ac(2) bit_imp_le_length bit_take_bit_iff less_le mask_eq_exp_minus_1 take_bit_incr_eq_word)

lemma bit_invariant_not_mask':
  fixes v :: "'a::len word"
  assumes "0 < b \<and> b \<le> LENGTH('a)"
  assumes "v \<noteq> mask b"
  shows "bit (take_bit b v) b = bit (take_bit b (v + 1)) b"
  using assms
  by (metis (no_types, lifting) Groups.add_ac(2) bit_imp_le_length bit_take_bit_iff less_le mask_eq_exp_minus_1 take_bit_incr_eq_word)


lemma negative_negation_is_positive:
  assumes "0 < b \<and> b \<le> 64"
  assumes "v \<noteq> take_bit b (min_int b)"
  assumes "take_bit b v = v"    
  assumes "b \<turnstile> v <j 0"
  shows "b \<turnstile> 0 \<le>j -v"
  using assms take_bit_incr_eq
proof -
  have "take_bit b (not v) \<noteq> 2 ^ b - 1"
    by (metis (no_types, opaque_lifting) assms(3) assms(4) bit.compl_zero less_le mask_eq_exp_minus_1 mask_eq_take_bit_minus_one take_bit_not_iff take_bit_of_0)
  then have "take_bit b ((not v) + 1) = 1 + take_bit b (not v)"
    using take_bit_incr_eq_word [where n=b and k="not v"]
    by (metis (no_types, lifting) Groups.add_ac(2) JavaWords.take_bit_dist_addR take_bit_incr_eq_word new_int.elims new_int_take_bits take_bit_word_eq_self verit_comp_simplify(3))
  have "bit v (b-1)"
    using assms(1,4) jlt_zero_sign_bit by simp
  have "-v = (not v) + 1"
    by (simp add: minus_eq_not_plus_1)
  have "\<not>(bit (not v) (b-1))"
    using \<open>bit v (b - 1)\<close> bit_not_iff by blast
  also have "not v \<noteq> mask b"
    by (metis assms(3) assms(4) bit.conj_cancel_right less_irrefl take_bit_eq_mask)
  ultimately have "\<not>(bit ((not v) + 1) (b-1))"
    using bit_invariant_not_mask
    by (smt (verit, best) Suc_pred' \<open>take_bit b (not v + 1) = 1 + take_bit b (not v)\<close> add.commute assms(1) assms(2) assms(3) bit.double_compl bit_imp_le_length bit_take_bit_iff less_Suc_eq less_le mask_0 min_int_def new_int.elims new_int_take_bits signed_take_bit_eq_if_positive signed_take_bit_iffpos take_bit_0 take_bit_not_iff)
  then show ?thesis
    using \<open>- v = not v + 1\<close> assms(1) jgte_zero_sign_bit by presburger
qed

lemma
  fixes v :: "'a::len word"
  assumes "0 < b \<and> b < LENGTH('a)"
  assumes "take_bit b v = v"
  shows "take_bit b (not v) = (and (not v) (mask (b)))"
  using assms
  using take_bit_eq_mask by blast

fun old_intval_right_shift :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "old_intval_right_shift (IntVal b1 v1) (IntVal b2 v2) = 
     (let shift = shift_amount b1 v2 in
      let ones = and (mask b1) (not (mask (b1 - shift) :: int64)) in
      (if int_signed_value b1 v1 < 0
       then new_int b1 (or ones (v1 >>> shift))
       else new_int b1 (v1 >>> shift)))" |
  "old_intval_right_shift _ _ = UndefVal"

value "mask 6:: 64 word"

lemma
  assumes "0 < b1 \<and> b1 \<le> 64 \<and> 0 < b2 \<and> b2 \<le> 64"
  shows "old_intval_right_shift (IntVal b1 v1) (IntVal b2 v2)
    = new_int b1 (v1 >>[b1] shift_amount b1 v2)" (is "?lhs = ?rhs")
proof (cases "int_signed_value b1 v1 < 0")
  case True
  have neg: "(bit v1 (b1 - (1::nat)))"
    using True
    by (metis Suc_leI Suc_pred assms bit_1_0 bit_imp_le_length bit_last_iff bit_take_bit_iff int_signed_value.simps not_less push_bit_bit_set signed_take_bit_eq_if_positive)
  obtain n where n: "n = shift_amount b1 v2" by simp
  have rhs: "?rhs = new_int b1 (or (v1 >>> n) ((not (mask (b1-n)))))"
    using neg
    by (simp add: n sshiftr_def)
  obtain ones where ones: "ones = and (mask b1) (not (mask (b1 - n) :: int64))"
    by auto
  then have lhs: "?lhs = new_int b1 (or ones (v1 >>> n))"
    by (smt (verit, ccfv_SIG) True old_intval_right_shift.simps(1) n)
  from lhs rhs show ?thesis
    by (metis (no_types, lifting) new_int.simps ones take_bit_eq_mask word_ao_absorbs(6) word_ao_dist word_bw_comms(1) word_bw_comms(2) word_oa_dist)
next
  case False
  have lhs: "?lhs = new_int b1 (v1 >>> shift_amount b1 v2)"
    using False unfolding old_intval_right_shift.simps
    by presburger
  have "\<not>(bit v1 (b1 - (1::nat)))"
    using False
    using assms jlt_zero_sign_bit by force
  then have rhs: "?rhs = new_int b1 (v1 >>> shift_amount b1 v2)"
    unfolding sshiftr_def by auto
  from lhs rhs show ?thesis
    by presburger
qed

(*
lemma positive_negation_is_negative:
  assumes "0 < b \<and> b \<le> 64"
  assumes "take_bit b v = v"    
  assumes "b \<turnstile> 0 <j v"
  shows "b \<turnstile> -v <j 0"
proof -
  have "\<not>(bit v (b-1))"
    using assms(1) assms(3) jgt_zero_sign_bit by blast
  then have "take_bit b ((not v) + 1) = 1 + take_bit b (not v)"
    using take_bit_incr_eq_word [where n=b and k="not v"]
    by (smt (verit, ccfv_SIG) Groups.add_ac(2) JavaWords.signed_take_take_bit JavaWords.take_bit_dist_addR Suc_pred assms(1) assms(3) bit.compl_zero jlte_jlt mask_eq_exp_minus_1 mask_eq_take_bit_minus_one not_less numeral_nat(7) signed_take_bit_eq_iff_take_bit_eq take_bit_incr_eq_word take_bit_not_iff take_bit_word_eq_self)
  have "-v = (not v) + 1"
    by (simp add: minus_eq_not_plus_1)
  have "bit (not v) (b-1)"
    using \<open>\<not> bit v (b - 1)\<close> assms(1) bit_not_iff_eq by fastforce
  have nm: "not v \<noteq> mask (b-1)"
    by (metis \<open>bit (not v) (b - 1)\<close> assms(1) jgte_zero_sign_bit max_int_mask max_int_max max_int_signed_2pow_signed)
  have "?thesis = ((sint (signed_take_bit (b-1) (-v))) < sint 0)" (is "?thesis = ?uf")
    by simp
  then have "?uf s = ((sint (signed_take_bit (b-1) (take_bit b (-v)))) < 0)"
    by (metis ValueThms.signed_take_take_bit assms(1) signed_eq_0_iff)
  then have "... = ((sint (signed_take_bit (b-1) (1 + (take_bit b (not v))))) < 0)"
    by (simp add: \<open>- v = not v + 1\<close> \<open>take_bit b (not v + 1) = 1 + take_bit b (not v)\<close>)
  have "bit (not v) (b-1)"
    using \<open>bit (not v) (b - 1)\<close> by blast
  then have "bit (take_bit (b-1) (not v)) (b-1)"
    sorry
  have "take_bit (b-1) (not v) \<noteq> mask (b-1)"
    by (metis \<open>bit (take_bit (b-1) (not v)) (b - 1)\<close> assms(1) jgte_zero_sign_bit max_int_mask max_int_max max_int_signed_2pow_signed)
  then have "bit (1 + (take_bit (b-1) (not v))) (b-1)"
    using bit_invariant_not_mask
    using \<open>bit (take_bit (b - 1) (not v)) (b - 1)\<close> bit_take_bit_iff by blast
  then have "((sint (signed_take_bit (b-1) (1 + (take_bit b (not v))))) < 0)"
    using \<open>bit (take_bit (b - 1) (not v)) (b - 1)\<close> bit_take_bit_iff by blast
  show ?thesis using bit_invariant_not_mask'
    using \<open>(b \<turnstile> - v <j 0) = (sint (signed_take_bit (b - 1) (- v)) < sint 0)\<close> \<open>(sint (signed_take_bit (b - 1) (- v)) < sint 0) = (sint (signed_take_bit (b - 1) (take_bit b (- v))) < 0)\<close> \<open>(sint (signed_take_bit (b - 1) (take_bit b (- v))) < 0) = (sint (signed_take_bit (b - 1) (1 + take_bit b (not v))) < 0)\<close> \<open>sint (signed_take_bit (b - 1) (1 + take_bit b (not v))) < 0\<close> by blast
qed
*)

lemma abs_value_idempotence: \<comment>\<open>Proof walked through in Brae's thesis Chap. 9\<close>
  assumes "0 < b \<and> b \<le> 64"
  assumes "take_bit b v = v"
  shows "abs b (abs b v) = abs b v"
  using assms
proof (cases "b \<turnstile> 0 \<le>j v")
  case pos: True
  then have "abs b v = v"
    using assms positive_abs by simp
  then show ?thesis by simp
next
  case neg: False
  then show ?thesis proof (cases "v = take_bit b (min_int b)")
    case True
    then have "abs b v = v"
      using assms negative_abs by simp
    then show ?thesis by simp
  next
    case False
    have neg:"b \<turnstile> v <j 0"
      using neg by simp
    then have res: "abs b v = take_bit b (-v)"
      by simp
    from neg have "b \<turnstile> 0 \<le>j -v"
      using assms False negative_negation_is_positive by simp
    then have "abs b (-v) = take_bit b (-v)"
      using positive_abs by blast
    then show ?thesis using res
      by (smt (verit, best) ValueThms.signed_take_take_bit \<open>b \<turnstile> 0 \<le>j - v\<close> abs.elims assms(1) int_signed_value.simps new_int.elims new_int_take_bits)
  qed
qed

thm_oracles abs_value_idempotence

lemma intval_abs_simp:
  assumes "intval_abs (IntVal b v) = (IntVal b' v')"
  shows "abs b v = v'"
  using assms
  by fastforce

optimization AbsIdempotence:
  "abs(abs(x)) \<longmapsto> abs(x)"
  apply auto
  using intval_abs_simp abs_value_idempotence
  by (smt (verit, best) eval_bits_1_64 eval_unused_bits_zero intval_abs.elims new_int.simps unary_eval.simps(1) unfold_evaltree(2))

thm_oracles AbsIdempotence

lemma mod_plus_one:
  fixes v :: "'a::len word"
  assumes "0 < b \<and> b < LENGTH('a)"
  assumes "v mod (2^b) < (2^b) - 1"
  shows "v mod (2^b) + 1 = (v+1) mod (2^b)"
proof -
  have t1:"take_bit LENGTH('a) 2^b = 2^b"
    by (smt (verit, ccfv_SIG) One_nat_def Suc_pred assms(1) bits_one_mod_two_eq_one bot_nat_0.extremum_strict less_Suc_numeral less_irrefl minus_mod_eq_div_mult minus_mod_eq_mult_div mult_div_mod_eq not_gr0 numeral_Bit0_div_2 numeral_code(1) of_nat_numeral of_nat_take_bit rel_simps(51) take_bit_Suc_0 take_bit_of_1 take_bit_rec)
  have t2:"take_bit LENGTH('a) 2^LENGTH('a)-1 = 2^LENGTH('a)-1"
    by (smt (verit, ccfv_SIG) One_nat_def Suc_pred assms(1) bits_one_mod_two_eq_one bot_nat_0.extremum_strict less_Suc_numeral less_irrefl minus_mod_eq_div_mult minus_mod_eq_mult_div mult_div_mod_eq not_gr0 numeral_Bit0_div_2 numeral_code(1) of_nat_numeral of_nat_take_bit rel_simps(51) take_bit_Suc_0 take_bit_of_1 take_bit_rec)
  (*have "2^b < 2^LENGTH('a)-1"
    using t1 t2 assms(1) sledgehammer*)
  then have "v mod (2^b) + 1 < (2^b)"
    by (smt (verit) assms(1) assms(2) exp_eq_zero_iff not_less one_le_power uint_2p uint_arith_simps(2) uint_arith_simps(5) uint_word_ariths(2) uint_word_ariths(8) word_greater_zero_iff zmod_le_nonneg_dividend)
    then show ?thesis
  using assms
  by (metis ValueThms.take_bit_dist_addL take_bit_eq_word take_bit_mod)
qed

lemma
  fixes v y :: "'a::len word"
  assumes "0 < y \<and> y < 2^LENGTH('a)-1"
  assumes "0 \<le> r \<and> r < y"
  shows "((((v div y) * y)) div y) = (v div y)"
  using assms
  using div_lt' word_div_mult by blast


lemma bit_invariant_modulo:
  fixes v :: "'a::len word"
  assumes "b > 0 \<and> b < LENGTH('a)"
  assumes "v mod (2^b) \<noteq> (2^b) - 1"
  shows "odd (v div (2^b)) = odd ((v+1) div (2^b))"
proof -
  have "(v mod 2^b) < 2^b"
    by (metis and_mask_less_size assms(1) take_bit_eq_mask take_bit_mod wsst_TYs(3))
  then have "(v mod 2^b) < (2^b) - 1"
    using assms(2)
    by (smt (verit, best) len_gt_0 less_le mod_pos_pos_trivial of_bool_eq(2) one_mod_2_pow_eq uint_arith_simps(2) uint_lt2p uint_word_ariths(8) uint_word_of_int wi_le word_arith_wis(2) word_mod_def word_sub_less_iff)
  then have "(v mod 2^b) + 1 = (v+1) mod 2^b"
    by (simp add: assms(1) mod_plus_one)
  then have e: "(v div 2^b)*2^b + (v mod 2^b) + 1
        = (v div 2^b)*2^b + ((v+1) mod 2^b)"
    using assms by (simp)
  have "of_bool (bit v b) = ((v div 2^b) mod 2)"
    by (simp add: bit_iff_odd mod2_eq_if)
  have "(((v + 1) div 2^b) mod 2) = ((((v div 2^b) * 2^b + v mod 2^b)+1) div 2^b) mod 2"
    by presburger
  then have a: "... = (((((v+1) div 2^b) * 2^b + (v+1) mod 2^b)) div 2^b) mod 2"
    using assms
    by presburger
  then have b: "... = ((((v div 2^b) * 2^b + (v+1) mod 2^b)) div 2^b) mod 2"
    using assms
    using e by presburger
  then have "... = (v div 2^b) mod 2"
    using assms
    by (smt (verit, del_insts) add_diff_cancel_right' e exp_eq_zero_iff minus_mod_eq_div_mult mult_div_le mult_div_mod_eq nonzero_mult_div_cancel_right not_less of_bool_eq(2) take_bit_int_less_exp take_bit_of_1 uint_2p uint_div uint_lt2p uint_mult_lem word_div_def word_greater_zero_iff)
  then show ?thesis
    by (metis b mod_div_decomp odd_iff_mod_2_eq_one)
qed

lemma bit_invariant_not_mask'':
  fixes v :: "'a::len word"
  assumes "0 < b \<and> b < LENGTH('a)"
  assumes "take_bit b v \<noteq> mask b"
  shows "bit v b = bit ((v + 1)) b"
  using assms bit_invariant_modulo
  by (metis bit_iff_odd mask_eq_exp_minus_1 take_bit_eq_mod)

lemma positive_negation_is_positive:
  assumes "0 < b \<and> b \<le> 64"
  assumes "take_bit b v = v"    
  assumes "b \<turnstile> 0 <j v"
  shows "b \<turnstile> -v <j 0"
  using assms take_bit_incr_eq
proof -
  have "\<not>(bit v (b-1))"
    using assms(1) assms(3) jgt_zero_sign_bit by presburger
  have "-v = (not v) + 1"
    by (simp add: minus_eq_not_plus_1)
  have "(bit (not v) (b-1))"
    using \<open>\<not> bit v (b - 1)\<close> assms(1) bit_not_iff_eq by fastforce
  also have nm: "take_bit (b-1) (not v) \<noteq> mask (b-1)"
    by (metis (mono_tags, opaque_lifting) \<open>\<not> bit v (b - 1)\<close> assms(3) bit.compl_zero int_signed_value.simps less_le signed_take_bit_eq_if_positive signed_take_bit_of_0 take_bit_minus_one_eq_mask take_bit_not_take_bit take_bit_of_0 word_not_not)
  ultimately have "(bit ((not v) + 1) (b-1))"
    by (metis assms(1) assms(3) bit_imp_le_length bit_invariant_not_mask'' diff_is_0_eq le_simps(1) mask_0 max_int_mask max_int_max max_int_signed_2pow_signed not_less zero_less_diff)
  then show ?thesis
    using \<open>- v = not v + 1\<close> assms(1) jlt_zero_sign_bit by presburger
qed

lemma abs_value_negation: \<comment>\<open>Proof walked through in Brae's thesis Chap. 9\<close>
  assumes "0 < b \<and> b \<le> 64"
  assumes "take_bit b v = v"
  shows "abs b (take_bit b (-v)) = abs b v"
proof (cases "v = take_bit b (min_int b)")
  case True
  then show ?thesis
    using assms(1) negative_abs by auto
next
  case notmin: False
  then show ?thesis proof (cases "v = 0")
    case True
    then show ?thesis
      by simp
  next
    case notzero: False
    then show ?thesis proof (cases "b \<turnstile> 0 <j v")
      case True
      have "b \<turnstile> -v <j 0"
        using notmin positive_negation_is_positive
        using True assms(1) assms(2) by blast
      then show ?thesis
        by (smt (verit) JavaWords.take_bit_dist_neg ValueThms.signed_take_take_bit abs.simps assms(1) int_signed_value.simps more_arith_simps(10) negative_negation_is_positive)
    next
      case False
      then show ?thesis
        by (smt (verit, best) abs.simps abs_value_idempotence assms(1) assms(2) notzero signed_value_eq take_bit_of_0)

    qed
  qed
qed

optimization AbsNegation:
  "abs(-x) \<longmapsto> abs(x)"
  apply auto
  using intval_abs_simp abs_value_negation
  by (smt (verit, ccfv_threshold) eval_bits_1_64 eval_unused_bits_zero intval_abs.simps(1) intval_negate.elims new_int.simps unary_eval.simps(1) unfold_unary)

thm_oracles AbsNegation

end (* End of AbsPhase *)

end (* End of file *)

