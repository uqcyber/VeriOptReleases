subsection \<open>Fixed-width Word Theories\<close>

theory ValueThms
  imports Values
begin

(* declare [[show_types=true]] *)

subsubsection \<open>Support Lemmas for Upper/Lower Bounds\<close>

(* these two were weirdly hard to prove given it should be by definition *)
lemma size32: "size v = 32" for v :: "32 word"
  by (smt (verit, del_insts) size_word.rep_eq numeral_Bit0 numeral_2_eq_2 mult_Suc_right One_nat_def
      mult.commute len_of_numeral_defs(2,3) mult.right_neutral)

lemma size64: "size v = 64" for v :: "64 word"
  by (simp add: size64)

(* Nb. Word.sint_ge and sint_lt subsume these lemmas.
lemma signed_int_bottom32: "-(((2::int) ^ 31)) \<le> sint (v::int32)"
  using sint_range_size size32
  by (smt (verit, ccfv_SIG) One_nat_def Suc_pred add_Suc add_Suc_right eval_nat_numeral(3) nat.inject numeral_2_eq_2 numeral_Bit0 numeral_Bit1 zero_less_numeral)

lemma signed_int_top32: "(2 ^ 31) - 1 \<ge> sint (v::int32)"
  using sint_range_size size32
  by (smt (verit, ccfv_SIG) One_nat_def Suc_pred add_Suc add_Suc_right eval_nat_numeral(3) nat.inject numeral_2_eq_2 numeral_Bit0 numeral_Bit1 zero_less_numeral)
*)

lemma lower_bounds_equiv: 
  assumes "0 < N"
  shows "-(((2::int) ^ (N-1))) = (2::int) ^ N div 2 * - 1"
  by (simp add: assms int_power_div_base)

lemma upper_bounds_equiv:
  assumes "0 < N"
  shows "(2::int) ^ (N-1) = (2::int) ^ N div 2"
  by (simp add: assms int_power_div_base)

text \<open>Some min/max bounds for 64-bit words\<close>

lemma bit_bounds_min64: "((fst (bit_bounds 64))) \<le> (sint (v::int64))"
  using sint_ge[of v] by simp

lemma bit_bounds_max64: "((snd (bit_bounds 64))) \<ge> (sint (v::int64))"
  using sint_lt[of v] by simp

text \<open>Extend these min/max bounds to extracting smaller signed words using $signed\_take\_bit$.\<close>

text \<open>Note: we could use signed to convert between bit-widths, instead of 
  signed\_take\_bit.  But that would have to be done separately for each bit-width type.\<close>

value "sint(signed_take_bit 7 (128 :: int8))"

ML_val \<open>@{thm signed_take_bit_decr_length_iff}\<close>
declare [[show_types=true]]
ML_val \<open>@{thm signed_take_bit_int_less_exp}\<close>

lemma signed_take_bit_int_less_exp_word:
  fixes ival :: "'a :: len word"
  assumes "n < LENGTH('a)"
  shows "sint(signed_take_bit n ival) < (2::int) ^ n"
  apply transfer
  by (smt (verit) not_take_bit_negative signed_take_bit_eq_take_bit_shift 
     signed_take_bit_int_less_exp take_bit_int_greater_self_iff) 

lemma signed_take_bit_int_greater_eq_minus_exp_word:
  fixes ival :: "'a :: len word"
  assumes "n < LENGTH('a)"
  shows "- (2 ^ n) \<le> sint(signed_take_bit n ival)"
  using signed_take_bit_int_greater_eq_minus_exp_word assms by blast

lemma signed_take_bit_range:
  fixes ival :: "'a :: len word"
  assumes "n < LENGTH('a)"
  assumes "val = sint(signed_take_bit n ival)"
  shows "- (2 ^ n) \<le> val \<and> val < 2 ^ n"
  by (auto simp add: assms signed_take_bit_int_greater_eq_minus_exp_word 
      signed_take_bit_int_less_exp_word)

text \<open>A $bit\_bounds$ version of the above lemma.\<close>

lemma signed_take_bit_bounds:
  fixes ival :: "'a :: len word"
  assumes "n \<le> LENGTH('a)"
  assumes "0 < n"
  assumes "val = sint(signed_take_bit (n - 1) ival)"
  shows "fst (bit_bounds n) \<le> val \<and> val \<le> snd (bit_bounds n)"
  by (metis bit_bounds.simps fst_conv less_imp_diff_less nat_less_le sint_ge sint_lt snd_conv 
      zle_diff1_eq upper_bounds_equiv lower_bounds_equiv signed_take_bit_range assms)

(* It is helpful to have the 64-bit instance of the above, to avoid uninstantiated types
   when apply it backwards. *)
lemma signed_take_bit_bounds64:
  fixes ival :: "int64"
  assumes "n \<le> 64"
  assumes "0 < n"
  assumes "val = sint(signed_take_bit (n - 1) ival)"
  shows "fst (bit_bounds n) \<le> val \<and> val \<le> snd (bit_bounds n)"
  by (metis size64 word_size signed_take_bit_bounds assms)

lemma int_signed_value_bounds:
  assumes "b1 \<le> 64"
  assumes "0 < b1"
  shows "fst (bit_bounds b1) \<le> int_signed_value b1 v2 \<and>
         int_signed_value b1 v2 \<le> snd (bit_bounds b1)"
  using signed_take_bit_bounds64 by (simp add: assms)

lemma int_signed_value_range:
  fixes ival :: "int64"
  assumes "val = int_signed_value n ival"
  shows "- (2 ^ (n - 1)) \<le> val \<and> val < 2 ^ (n - 1)"
  using assms int_signed_value_range by blast

text \<open>Some lemmas about unsigned words smaller than 64-bit, for zero-extend operators.\<close>

lemma take_bit_smaller_range:
  fixes ival :: "'a :: len word"
  assumes "n < LENGTH('a)"
  assumes "val = sint(take_bit n ival)"
  shows "0 \<le> val \<and> val < (2::int) ^ n"
  by (simp add: assms signed_take_bit_eq)

lemma take_bit_same_size_nochange:
  fixes ival :: "'a :: len word"
  assumes "n = LENGTH('a)"
  shows "ival = take_bit n ival"
  by (simp add: assms)

text \<open>A simplification lemma for $new\_int$, showing that upper bits can be ignored.\<close>

lemma take_bit_redundant[simp]:
  fixes ival :: "'a :: len word"
  assumes "0 < n"
  assumes "n < LENGTH('a)"
  shows "signed_take_bit (n - 1) (take_bit n ival) = signed_take_bit (n - 1) ival"
proof -
  have "\<not> (n \<le> n - 1)" 
    using assms by simp
  then have "\<And>i . signed_take_bit (n - 1) (take_bit n i) = signed_take_bit (n-1) i"
    by (metis (mono_tags) signed_take_bit_take_bit) 
  then show ?thesis
    by simp
qed

lemma take_bit_same_size_range:
  fixes ival :: "'a :: len word"
  assumes "n = LENGTH('a)"
  assumes "ival2 = take_bit n ival"
  shows "- (2 ^ n div 2) \<le> sint ival2 \<and> sint ival2 < 2 ^ n div 2"
  using lower_bounds_equiv sint_ge sint_lt by (auto simp add: assms)

lemma take_bit_same_bounds:
  fixes ival :: "'a :: len word"
  assumes "n = LENGTH('a)"
  assumes "ival2 = take_bit n ival"
  shows "fst (bit_bounds n) \<le> sint ival2 \<and> sint ival2 \<le> snd (bit_bounds n)"
  using assms take_bit_same_size_range by force

text \<open>Next we show that casting a word to a wider word preserves any upper/lower bounds.
  (These lemmas may not be needed any more, since we are not using scast now?)\<close>

lemma scast_max_bound:
  assumes "sint (v :: 'a :: len word) < M"
  assumes "LENGTH('a) < LENGTH('b)"
  shows "sint ((scast v) :: 'b :: len word) < M"
  using scast_max_bound assms by fast
(* helpful thms?
  Word.scast_eq: scast (?w::?'b word) = word_of_int (sint ?w)
  Word.sint_lt: sint (?x::?'a word) < (2::int) ^ (LENGTH(?'a) - (1::nat)
  Word.sint_uint: sint (w::'a word) = signed_take_bit (LENGTH('a) - Suc (0::nat)) (uint w)
  Word.sint_sbintrunc' :  sint (word_of_int (?bin::int)) = signed_take_bit (LENGTH(?'a) - (1::nat)) ?bin
  Word.int_word_sint   - moves up, takes mod, then moves down
  Bit_Operations.signed_take_bit_int_eq_self_iff:
    (signed_take_bit (?n::nat) (?k::int) = ?k) = (- ((2::int) ^ ?n) \<sqsubseteq> ?k \<and> ?k < (2::int) ^ ?n)
  Bit_Operations.signed_take_bit_int_eq_self:
    - ((2::int) ^ (?n::nat)) \<sqsubseteq> (?k::int) \<Longrightarrow> ?k < (2::int) ^ ?n \<Longrightarrow> signed_take_bit ?n ?k = ?k
*)

lemma scast_min_bound:
  assumes "M \<le> sint (v :: 'a :: len word)"
  assumes "LENGTH('a) < LENGTH('b)"
  shows "M \<le> sint ((scast v) :: 'b :: len word)"
  by (simp add: scast_min_bound assms)

lemma scast_bigger_max_bound:
  assumes "(result :: 'b :: len word) = scast (v :: 'a :: len word)"
  shows "sint result < 2 ^ LENGTH('a) div 2"
  using assms scast_bigger_max_bound by blast

lemma scast_bigger_min_bound:
  assumes "(result :: 'b :: len word) = scast (v :: 'a :: len word)"
  shows "- (2 ^ LENGTH('a) div 2) \<le> sint result"
  using scast_bigger_min_bound assms by blast

lemma scast_bigger_bit_bounds:
  assumes "(result :: 'b :: len word) = scast (v :: 'a :: len word)"
  shows "fst (bit_bounds (LENGTH('a))) \<le> sint result \<and> sint result \<le> snd (bit_bounds (LENGTH('a)))"
  by (auto simp add: scast_bigger_max_bound scast_bigger_min_bound assms)

text \<open>Results about $new\_int$.\<close>

(* may be too trivial? *)
lemma new_int_take_bits:
  assumes "IntVal b val = new_int b ival"
  shows "take_bit b val = val"
  using assms by simp

subsubsection \<open>Support lemmas for take bit and signed take bit.\<close>

text \<open>Lemmas for removing redundant take\_bit wrappers.\<close>

lemma take_bit_dist_addL[simp]: 
  fixes x :: "'a :: len word"
  shows "take_bit b (take_bit b x + y) = take_bit b (x + y)"
proof (induction b)
  case 0
  then show ?case
    by simp 
next
  case (Suc b)
  then show ?case
    by (simp add: add.commute mask_eqs(2) take_bit_eq_mask) 
qed

lemma take_bit_dist_addR[simp]: 
  fixes x :: "'a :: len word"
  shows "take_bit b (x + take_bit b y) = take_bit b (x + y)"
  by (metis add.commute take_bit_dist_addL)

lemma take_bit_dist_subL[simp]: 
  fixes x :: "'a :: len word"
  shows "take_bit b (take_bit b x - y) = take_bit b (x - y)"
  by (metis take_bit_dist_addR uminus_add_conv_diff)

lemma take_bit_dist_subR[simp]: 
  fixes x :: "'a :: len word"
  shows "take_bit b (x - take_bit b y) = take_bit b (x - y)"
  by (metis (no_types) take_bit_dist_subL diff_add_cancel diff_right_commute diff_self) 

lemma take_bit_dist_neg[simp]:
  fixes ix :: "'a :: len word"
  shows "take_bit b (- take_bit b (ix)) = take_bit b (- ix)"
  by (metis diff_0 take_bit_dist_subR)

lemma signed_take_take_bit[simp]: 
  fixes x :: "'a :: len word"
  assumes "0 < b"
  shows "signed_take_bit (b - 1) (take_bit b x) = signed_take_bit (b - 1) x"
  using signed_take_take_bit assms by blast

lemma mod_larger_ignore:
  fixes a :: int
  fixes m n :: nat
  assumes "n < m"
  shows "(a mod 2 ^ m) mod 2 ^ n = a mod 2 ^ n"
  using mod_larger_ignore assms by blast
  
lemma mod_dist_over_add:
  fixes a b c :: int64  (* "'a :: len word" *)
  fixes n :: nat
  assumes 1: "0 < n"
  assumes 2: "n < 64"
  shows "(a mod 2^n + b) mod 2^n = (a + b) mod 2^n"
proof -
  have 3: "(0 :: int64) < 2 ^ n"
    by (simp add: size64 word_2p_lem assms)
  then show ?thesis
    unfolding word_mod_2p_is_mask[OF 3] apply transfer
    by (metis (no_types, opaque_lifting) and.right_idem take_bit_add take_bit_eq_mask)
qed

end
