subsection \<open>Experimental AndNode Phase\<close>

theory NewAnd
  imports
    Common
    Graph.Long
begin

lemma bin_distribute_and_over_or:
  "bin[z & (x | y)] = bin[(z & x) | (z & y)]"
  by (smt (verit, best) bit_and_iff bit_eqI bit_or_iff)

lemma intval_distribute_and_over_or:
  "val[z & (x | y)] = val[(z & x) | (z & y)]"
  apply (cases x; cases y; cases z; auto)
  using bin_distribute_and_over_or by blast+

lemma exp_distribute_and_over_or:
  "exp[z & (x | y)] \<ge> exp[(z & x) | (z & y)]"
  apply simp using intval_distribute_and_over_or
  using BinaryExpr bin_eval.simps(4,5)
  using intval_or.simps(1) unfolding new_int_bin.simps new_int.simps apply auto
  by (metis bin_eval.simps(4) bin_eval.simps(5) intval_or.simps(2) intval_or.simps(5))


lemma intval_and_commute:
  "val[x & y] = val[y & x]"
  by (cases x; cases y; auto simp: and.commute)

lemma intval_or_commute:
  "val[x | y] = val[y | x]"
  by (cases x; cases y; auto simp: or.commute)

lemma intval_xor_commute:
  "val[x \<oplus> y] = val[y \<oplus> x]"
  by (cases x; cases y; auto simp: xor.commute)

lemma exp_and_commute:
  "exp[x & z] \<ge> exp[z & x]"
  apply simp using intval_and_commute by auto

lemma exp_or_commute:
  "exp[x | y] \<ge> exp[y | x]"
  apply simp using intval_or_commute by auto

lemma exp_xor_commute:
  "exp[x \<oplus> y] \<ge> exp[y \<oplus> x]"
  apply simp using intval_xor_commute by auto


lemma bin_eliminate_y:
  assumes "bin[y & z] = 0"
  shows "bin[(x | y) & z] = bin[x & z]"
  using assms
  by (simp add: and.commute bin_distribute_and_over_or)

lemma intval_eliminate_y:
  assumes "val[y & z] = IntVal b 0"
  shows "val[(x | y) & z] = val[x & z]"
  using assms bin_eliminate_y by (cases x; cases y; cases z; auto)

lemma intval_and_associative:
  "val[(x & y) & z] = val[x & (y & z)]"
  apply (cases x; cases y; cases z; auto)
  by (simp add: and.assoc)+

lemma intval_or_associative:
  "val[(x | y) | z] = val[x | (y | z)]"
  apply (cases x; cases y; cases z; auto)
  by (simp add: or.assoc)+

lemma intval_xor_associative:
  "val[(x \<oplus> y) \<oplus> z] = val[x \<oplus> (y \<oplus> z)]"
  apply (cases x; cases y; cases z; auto)
  by (simp add: xor.assoc)+

lemma exp_and_associative:
  "exp[(x & y) & z] \<ge> exp[x & (y & z)]"
  apply simp using intval_and_associative by fastforce

lemma exp_or_associative:
  "exp[(x | y) | z] \<ge> exp[x | (y | z)]"
  apply simp using intval_or_associative by fastforce

lemma exp_xor_associative:
  "exp[(x \<oplus> y) \<oplus> z] \<ge> exp[x \<oplus> (y \<oplus> z)]"
  apply simp using intval_xor_associative by fastforce


lemma intval_and_absorb_or:
  assumes "\<exists>b v . x = new_int b v" (* TODO: required? *)
  assumes "val[x & (x | y)] \<noteq> UndefVal"
  shows "val[x & (x | y)] = val[x]"
  using assms apply (cases x; cases y; auto)
  by (metis (mono_tags, lifting) intval_and.simps(5))

lemma intval_or_absorb_and:
  assumes "\<exists>b v . x = new_int b v" (* TODO: required? *)
  assumes "val[x | (x & y)] \<noteq> UndefVal"
  shows "val[x | (x & y)] = val[x]"
  using assms apply (cases x; cases y; auto)
  by (metis (mono_tags, lifting) intval_or.simps(5))

lemma exp_and_absorb_or:
  "exp[x & (x | y)] \<ge> exp[x]"
  apply auto using intval_and_absorb_or eval_unused_bits_zero
  by (smt (verit) evalDet intval_or.elims new_int.elims)

lemma exp_or_absorb_and:
  "exp[x | (x & y)] \<ge> exp[x]"
  apply auto using intval_or_absorb_and eval_unused_bits_zero
  by (smt (verit) evalDet intval_or.elims new_int.elims)

definition IRExpr_up :: "IRExpr \<Rightarrow> int64" where
  "IRExpr_up e = not 0"

definition IRExpr_down :: "IRExpr \<Rightarrow> int64" where
  "IRExpr_down e = 0"

lemma
  assumes "y = 0"
  shows "x + y = or x y"
  using assms
  by simp

(*
lemma
  fixes x y :: "64 word"
  assumes "\<exists>e. n = 2^e"
  assumes "and y n = 0"
  shows "x + y = (or (and x n) (and y n)) + ((x >> n) + (y >> n) << n)"
*)

lemma no_overlap_or:
  assumes "and x y = 0"
  shows "x + y = or x y"
  using assms
  by (metis bit_and_iff bit_xor_iff disjunctive_add xor_self_eq)

(*lemma no_carry_zero_bit:
  assumes "\<not>(bit y j)"
  assumes "\<not>(bit y (Suc j))"
  shows "bit (x + y) (Suc j) = bit x (Suc j)"
  using assms sorry*)

(*
lemma
  fixes x y :: "'a :: len word"
  assumes "(and y (mask (Suc j))) = 0"
  shows "bit (x + y) j = bit (or x y) j"
  using assms proof (induction j)
  case 0
  then show ?case
    by (metis Word.mask_Suc_0 bit_0 bit_1_iff bit_and_iff bit_mask_iff even_add even_or_iff less_numeral_extra(3) mask_0)
next
  case (Suc j)
  then show ?case sorry
qed

lemma packed_bottom_zeros_elim_add:
  fixes x y :: "'a :: len word"
  assumes "\<And>n. n \<le> j \<Longrightarrow> \<not>(bit y n)"
  shows "bit (x + y) j = bit x j"
  using assms 
proof -
  have "(and y (mask j)) = 0"
    using assms
    by (metis (no_types, opaque_lifting) bit_and_iff bit_eq_iff bit_mask_iff order_le_less zero_and_eq)
  have "bit (x + y) j = bit (or x y) j"
    using assms
    proof (induction j)
      case 0
      then show ?case
        by (simp add: even_or_iff)
    next
      case (Suc j)
      then show ?case sorry
    qed
  then show ?thesis
    by (simp add: assms bit_or_iff)
qed
proof (induction j)
  case 0
  then show ?case
    by auto
next
  case (Suc j)
  have "(and y (2^(Suc j))) = 0"
    using Suc.prems and_exp_eq_0_iff_not_bit by blast
  
  then show ?case sorry
qed 
  
  using assms bit_and_iff bit_xor_iff disjunctive_add xor_self_eq sorry*)
 (*
using assms proof (induction j)
  case 0
  then show ?case
    by (metis assms bit_0 bot_nat_0.extremum even_add)
next
  case (Suc j)
  have j0: "\<not>(bit y j)"
    by (simp add: Suc.prems)
  have sj0: "\<not>(bit y (Suc j))"
    by (simp add: Suc.prems)
  show ?case using j0 sj0 no_overlap_or
    by blast
qed *)

(*
lemma packed_bits:
  fixes a :: "64 word"
  assumes "numberOfLeadingZeros a + bitCount a = 64"
  assumes "a \<noteq> 0"
  shows "n \<le> highestOneBit a \<longrightarrow> bit a n"
proof -
  obtain j where j: "j = highestOneBit a"
    by simp
  then have "\<forall>i. i < Nat.size a \<and> i > j \<longrightarrow> \<not>(bit a i)"
    unfolding highestOneBit_def
    by (simp add: j zerosAboveHighestOne)
  have "Nat.size a > highestOneBit a"
    unfolding highestOneBit_def MaxOrNeg_def
    by (simp add: max_bit)
  then have jcard: "numberOfLeadingZeros a = card {i. j \<le> i \<and> i \<le> Nat.size a}"
    unfolding numberOfLeadingZeros_def using j card_of_range_bound leadingZerosAddHighestOne sorry
    by presburger
  obtain k where k: "k = Nat.size a - numberOfLeadingZeros a"
    by presburger
  then have "k = bitCount a"
    using assms
    using size64 by auto
  have union: "{i. j < i \<and> i < Nat.size a} \<union> {i. i \<le> j} = {i. i < Nat.size a}"
    apply auto
    using \<open>highestOneBit (a::64 word) < int (size_class.size a)\<close> j by linarith
  have intersect: "{i. j < i \<and> i < Nat.size a} \<inter> {i. i \<le> j} = {}"
    by force
  have "card {i. j < i \<and> i < Nat.size a} + card {i. i \<le> j} = card {i. i < Nat.size a}"
    using card_add intersect union sorry
    by (metis (no_types, lifting) Int_commute bounded_nat_set_is_finite finite_Un mem_Collect_eq)
  then have "numberOfLeadingZeros a + card {i. i \<le> j} = Nat.size a + 1"
    unfolding jcard card_of_range apply auto sorry
    by (metis j jcard leadingZerosAddHighestOne)
  then have "k = card {i. i < j}"
    using assms k
    by (simp add: add.commute)
  have "{i. j < i \<and> i < Nat.size a} \<inter> {i. i \<le> j} = {}"
    using intersect by blast
  have "\<forall>i . i \<in> {i. j < i \<and> i < Nat.size a} \<longrightarrow> \<not>(bit a i)"
    using \<open>\<forall>i::nat. i < size_class.size (a::64 word) \<and> (j::nat) < i \<longrightarrow> \<not> bit a i\<close> by blast
  then have "\<forall>i . i \<in> {i. i < j} \<longrightarrow> bit a i"
    sorry
  then have less: "\<forall>i. i < j \<longrightarrow> bit a i"
    by blast
  have eq: "bit a j"
    using j unfolding highestOneBit_def MaxOrZero_def
    by (metis Max_in assms(2) disjunctive_diff eq_iff_diff_eq_0 equals0D finite_bit_word mem_Collect_eq zero_and_eq)
  then show ?thesis
    using j
    by (simp add: less order_le_less)
qed
*)

context stamp_mask
begin

lemma intval_up_and_zero_implies_zero:
  assumes "and (\<up>x) (\<up>y) = 0"
  assumes "[m, p] \<turnstile> x \<mapsto> xv"
  assumes "[m, p] \<turnstile> y \<mapsto> yv"
  assumes "val[xv & yv] \<noteq> UndefVal"
  shows "\<exists> b . val[xv & yv] = new_int b 0"
  using assms apply (cases xv; cases yv; auto)
  using up_mask_and_zero_implies_zero
  apply (smt (verit, best) take_bit_and take_bit_of_0)
  by presburger

lemma exp_eliminate_y:
  "and (\<up>y) (\<up>z) = 0 \<longrightarrow> BinaryExpr BinAnd (BinaryExpr BinOr x y) z \<ge> BinaryExpr BinAnd x z"
  apply simp apply (rule impI; rule allI; rule allI; rule allI) 
  subgoal premises p for m p v apply (rule impI) subgoal premises e
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using e by auto
    obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> yv"
      using e by auto
    obtain zv where zv: "[m,p] \<turnstile> z \<mapsto> zv"
      using e by auto
    have lhs: "v = val[(xv | yv) & zv]"
      using xv yv zv
      by (smt (verit, best) BinaryExprE bin_eval.simps(4) bin_eval.simps(5) e evalDet)
    then have "v = val[(xv & zv) | (yv & zv)]"
      by (simp add: intval_and_commute intval_distribute_and_over_or)
    also have "\<exists>b. val[yv & zv] = new_int b 0"
      using intval_up_and_zero_implies_zero
      by (metis calculation e intval_or.simps(5) p unfold_binary yv zv)
    ultimately have rhs: "v = val[xv & zv]"
      using intval_eliminate_y lhs by force
    from lhs rhs show ?thesis
      by (metis BinaryExpr BinaryExprE bin_eval.simps(4) e xv zv)
  qed
  done
  done

lemma leadingZeroBounds:
  fixes x :: "'a::len word"
  assumes "n = numberOfLeadingZeros x"
  shows "0 \<le> n \<and> n \<le> Nat.size x"
  using assms unfolding numberOfLeadingZeros_def
  by (simp add: MaxOrNeg_def highestOneBit_def nat_le_iff)

lemma above_nth_not_set:
  fixes x :: int64
  assumes "n = 64 - numberOfLeadingZeros x"
  shows "j > n \<longrightarrow> \<not>(bit x j)"
  using assms unfolding numberOfLeadingZeros_def
  by (smt (verit, ccfv_SIG) highestOneBit_def int_nat_eq int_ops(6) less_imp_of_nat_less max_set_bit size64 zerosAboveHighestOne)

no_notation LogicNegationNotation ("!_")

lemma zero_horner:
  "horner_sum of_bool 2 (map (\<lambda>x. False) xs) = 0"
  apply (induction xs) apply simp
  by force

lemma zero_map:
  assumes "j \<le> n"
  assumes "\<forall>i. j \<le> i \<longrightarrow> \<not>(f i)"
  shows "map f [0..<n] = map f [0..<j] @ map (\<lambda>x. False) [j..<n]"
  apply (insert assms)
  by (smt (verit, del_insts) add_diff_inverse_nat atLeastLessThan_iff bot_nat_0.extremum leD map_append map_eq_conv set_upt upt_add_eq_append)

lemma map_join_horner:
  assumes "map f [0..<n] = map f [0..<j] @ map (\<lambda>x. False) [j..<n]"
  shows "horner_sum of_bool (2::'a::len word) (map f [0..<n]) = horner_sum of_bool 2 (map f [0..<j])"
proof -
  have "horner_sum of_bool (2::'a::len word) (map f [0..<n]) = horner_sum of_bool 2 (map f [0..<j]) + 2 ^ length [0..<j] * horner_sum of_bool 2 (map f [j..<n])"
    using horner_sum_append
    by (smt (verit) assms diff_le_self diff_zero le_add_same_cancel2 length_append length_map length_upt map_append upt_add_eq_append)
  also have "... = horner_sum of_bool 2 (map f [0..<j]) + 2 ^ length [0..<j] * horner_sum of_bool 2 (map (\<lambda>x. False) [j..<n])"
    using assms
    by (metis calculation horner_sum_append length_map)
  also have "... = horner_sum of_bool 2 (map f [0..<j])"
    using zero_horner
    using mult_not_zero by auto
  finally show ?thesis by simp
qed

lemma split_horner:
  assumes "j \<le> n"
  assumes "\<forall>i. j \<le> i \<longrightarrow> \<not>(f i)"
  shows "horner_sum of_bool (2::'a::len word) (map f [0..<n]) = horner_sum of_bool 2 (map f [0..<j])"
  apply (rule map_join_horner)
  apply (rule zero_map)
  using assms by auto

lemma transfer_map:
  assumes "\<forall>i. i < n \<longrightarrow> f i = f' i"
  shows "(map f [0..<n]) = (map f' [0..<n])"
  using assms by simp

lemma transfer_horner:
  assumes "\<forall>i. i < n \<longrightarrow> f i = f' i"
  shows "horner_sum of_bool (2::'a::len word) (map f [0..<n]) = horner_sum of_bool 2 (map f' [0..<n])"
  using assms using transfer_map
  by (smt (verit, best))

lemma L1:
  assumes "n = 64 - numberOfLeadingZeros (\<up>z)"
  assumes "[m, p] \<turnstile> z \<mapsto> IntVal b zv"
  shows "and v zv = and (v mod 2^n) zv"
proof -
  have nle: "n \<le> 64"
    using assms
    using diff_le_self by blast
  also have "and v zv = horner_sum of_bool 2 (map (bit (and v zv)) [0..<64])"
    using horner_sum_bit_eq_take_bit size64
    by (metis size_word.rep_eq take_bit_length_eq)
  also have "... = horner_sum of_bool 2 (map (\<lambda>i. bit (and v zv) i) [0..<64])"
    by blast
  also have "... = horner_sum of_bool 2 (map (\<lambda>i. ((bit v i) \<and> (bit zv i))) [0..<64])"
    using bit_and_iff by metis
  also have "... = horner_sum of_bool 2 (map (\<lambda>i. ((bit v i) \<and> (bit zv i))) [0..<n])"
  proof -
    have "\<forall>i. i \<ge> n \<longrightarrow> \<not>(bit zv i)"
      using above_nth_not_set assms(1)
      using assms(2) not_may_implies_false
      by (smt (verit, ccfv_SIG) One_nat_def diff_less int_ops(6) leadingZerosAddHighestOne linorder_not_le nat_int_comparison(2) not_numeral_le_zero size64 zero_less_Suc zerosAboveHighestOne)
    then have "\<forall>i. i \<ge> n \<longrightarrow> \<not>((bit v i) \<and> (bit zv i))"
      by auto
    then show ?thesis using nle split_horner
      by (metis (no_types, lifting))
  qed
  also have "... = horner_sum of_bool 2 (map (\<lambda>i. ((bit (v mod 2^n) i) \<and> (bit zv i))) [0..<n])"
  proof -
    have "\<forall>i. i < n \<longrightarrow> bit (v mod 2^n) i = bit v i"
      by (metis bit_take_bit_iff take_bit_eq_mod)
    then have "\<forall>i. i < n \<longrightarrow> ((bit v i) \<and> (bit zv i)) = ((bit (v mod 2^n) i) \<and> (bit zv i))"
      by force
    then show ?thesis
      by (rule transfer_horner)
  qed
  also have "... = horner_sum of_bool 2 (map (\<lambda>i. ((bit (v mod 2^n) i) \<and> (bit zv i))) [0..<64])"
  proof -
    have "\<forall>i. i \<ge> n \<longrightarrow> \<not>(bit zv i)"
      using above_nth_not_set assms(1)
      using assms(2) not_may_implies_false
      by (smt (verit, ccfv_SIG) One_nat_def diff_less int_ops(6) leadingZerosAddHighestOne linorder_not_le nat_int_comparison(2) not_numeral_le_zero size64 zero_less_Suc zerosAboveHighestOne)
    then show ?thesis
      by (metis (no_types, lifting) assms(1) diff_le_self split_horner)
  qed
  also have "... = horner_sum of_bool 2 (map (bit (and (v mod 2^n) zv)) [0..<64])"
    by (meson bit_and_iff)
  also have "... = and (v mod 2^n) zv"
    using horner_sum_bit_eq_take_bit size64
    by (metis size_word.rep_eq take_bit_length_eq)
  finally show ?thesis
    using \<open>and (v::64 word) (zv::64 word) = horner_sum of_bool (2::64 word) (map (bit (and v zv)) [0::nat..<64::nat])\<close> \<open>horner_sum of_bool (2::64 word) (map (\<lambda>i::nat. bit ((v::64 word) mod (2::64 word) ^ (n::nat)) i \<and> bit (zv::64 word) i) [0::nat..<64::nat]) = horner_sum of_bool (2::64 word) (map (bit (and (v mod (2::64 word) ^ n) zv)) [0::nat..<64::nat])\<close> \<open>horner_sum of_bool (2::64 word) (map (\<lambda>i::nat. bit ((v::64 word) mod (2::64 word) ^ (n::nat)) i \<and> bit (zv::64 word) i) [0::nat..<n]) = horner_sum of_bool (2::64 word) (map (\<lambda>i::nat. bit (v mod (2::64 word) ^ n) i \<and> bit zv i) [0::nat..<64::nat])\<close> \<open>horner_sum of_bool (2::64 word) (map (\<lambda>i::nat. bit (v::64 word) i \<and> bit (zv::64 word) i) [0::nat..<64::nat]) = horner_sum of_bool (2::64 word) (map (\<lambda>i::nat. bit v i \<and> bit zv i) [0::nat..<n::nat])\<close> \<open>horner_sum of_bool (2::64 word) (map (\<lambda>i::nat. bit (v::64 word) i \<and> bit (zv::64 word) i) [0::nat..<n::nat]) = horner_sum of_bool (2::64 word) (map (\<lambda>i::nat. bit (v mod (2::64 word) ^ n) i \<and> bit zv i) [0::nat..<n])\<close> \<open>horner_sum of_bool (2::64 word) (map (bit (and ((v::64 word) mod (2::64 word) ^ (n::nat)) (zv::64 word))) [0::nat..<64::nat]) = and (v mod (2::64 word) ^ n) zv\<close> \<open>horner_sum of_bool (2::64 word) (map (bit (and (v::64 word) (zv::64 word))) [0::nat..<64::nat]) = horner_sum of_bool (2::64 word) (map (\<lambda>i::nat. bit v i \<and> bit zv i) [0::nat..<64::nat])\<close> by presburger
qed

lemma up_mask_upper_bound:
  assumes "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
  shows "xv \<le> (\<up>x)"
  using assms
  by (metis (no_types, lifting) and.idem and.right_neutral bit.conj_cancel_left bit.conj_disj_distribs(1) bit.double_compl ucast_id up_spec word_and_le1 word_not_dist(2))

lemma L2:
  assumes "numberOfLeadingZeros (\<up>z) + numberOfTrailingZeros (\<up>y) \<ge> 64"
  assumes "n = 64 - numberOfLeadingZeros (\<up>z)"
  assumes "[m, p] \<turnstile> z \<mapsto> IntVal b zv"
  assumes "[m, p] \<turnstile> y \<mapsto> IntVal b yv"
  shows "yv mod 2^n = 0"
proof -
  have "yv mod 2^n = horner_sum of_bool 2 (map (bit yv) [0..<n])"
    by (simp add: horner_sum_bit_eq_take_bit take_bit_eq_mod)
  also have "... \<le> horner_sum of_bool 2 (map (bit (\<up>y)) [0..<n])"
    using up_mask_upper_bound assms(4)
    by (metis (no_types, opaque_lifting) and.right_neutral bit.conj_cancel_right bit.conj_disj_distribs(1) bit.double_compl horner_sum_bit_eq_take_bit take_bit_and ucast_id up_spec word_and_le1 word_not_dist(2))
  also have "horner_sum of_bool 2 (map (bit (\<up>y)) [0..<n]) = horner_sum of_bool 2 (map (\<lambda>x. False) [0..<n])"
  proof -
    have "\<forall>i < n. \<not>(bit (\<up>y) i)"
      using assms(1,2) zerosBelowLowestOne
      by (metis add.commute add_diff_inverse_nat add_lessD1 leD le_diff_conv numberOfTrailingZeros_def)
    then show ?thesis
      by (metis (full_types) transfer_map)
  qed
  also have "horner_sum of_bool 2 (map (\<lambda>x. False) [0..<n]) = 0"
    using zero_horner
    by blast
  finally show ?thesis
    by auto
qed

thm_oracles L1 L2

lemma unfold_binary_width_add:
  shows "([m,p] \<turnstile> BinaryExpr BinAdd xe ye \<mapsto> IntVal b val) = (\<exists> x y.
          (([m,p] \<turnstile> xe \<mapsto> IntVal b x) \<and>
           ([m,p] \<turnstile> ye \<mapsto> IntVal b y) \<and>
           (IntVal b val = bin_eval BinAdd (IntVal b x) (IntVal b y)) \<and>
           (IntVal b val \<noteq> UndefVal)
        ))" (is "?L = ?R")
proof (intro iffI)
  assume 3: ?L
  show ?R apply (rule evaltree.cases[OF 3])
    apply force+ apply auto[1]
    apply (smt (verit) intval_add.elims intval_bits.simps)
    by blast
next
  assume R: ?R
  then obtain x y where "[m,p] \<turnstile> xe \<mapsto> IntVal b x"
        and "[m,p] \<turnstile> ye \<mapsto> IntVal b y"
        and "new_int b val = bin_eval BinAdd (IntVal b x) (IntVal b y)"
        and "new_int b val \<noteq> UndefVal"
    by auto
  then show ?L
    using R by blast
 qed

lemma unfold_binary_width_and:
  shows "([m,p] \<turnstile> BinaryExpr BinAnd xe ye \<mapsto> IntVal b val) = (\<exists> x y.
          (([m,p] \<turnstile> xe \<mapsto> IntVal b x) \<and>
           ([m,p] \<turnstile> ye \<mapsto> IntVal b y) \<and>
           (IntVal b val = bin_eval BinAnd (IntVal b x) (IntVal b y)) \<and>
           (IntVal b val \<noteq> UndefVal)
        ))" (is "?L = ?R")
proof (intro iffI)
  assume 3: ?L
  show ?R apply (rule evaltree.cases[OF 3])
    apply force+ apply auto[1] using intval_and.elims intval_bits.simps
    apply (smt (verit) new_int.simps new_int_bin.simps take_bit_and)
    by blast
next
  assume R: ?R
  then obtain x y where "[m,p] \<turnstile> xe \<mapsto> IntVal b x"
        and "[m,p] \<turnstile> ye \<mapsto> IntVal b y"
        and "new_int b val = bin_eval BinAnd (IntVal b x) (IntVal b y)"
        and "new_int b val \<noteq> UndefVal"
    by auto
  then show ?L 
    using R by blast
qed

lemma mod_dist_over_add_right:
  fixes a b c :: int64
  fixes n :: nat
  assumes 1: "0 < n"
  assumes 2: "n < 64"
  shows "(a + b mod 2^n) mod 2^n = (a + b) mod 2^n"
  using mod_dist_over_add
  by (simp add: "1" "2" add.commute)

lemma numberOfLeadingZeros_range:
  "0 \<le> numberOfLeadingZeros n \<and> numberOfLeadingZeros n \<le> Nat.size n"
  unfolding numberOfLeadingZeros_def highestOneBit_def using max_set_bit
  by (simp add: highestOneBit_def leadingZeroBounds numberOfLeadingZeros_def)

lemma improved_opt:
  assumes "numberOfLeadingZeros (\<up>z) + numberOfTrailingZeros (\<up>y) \<ge> 64"
  shows "exp[(x + y) & z] \<ge> exp[x & z]"
  apply simp apply ((rule allI)+; rule impI)
  subgoal premises eval for m p v
proof -
  obtain n where n: "n = 64 - numberOfLeadingZeros (\<up>z)"
    by simp
  obtain b val where val: "[m, p] \<turnstile> exp[(x + y) & z] \<mapsto> IntVal b val"
    by (metis BinaryExprE bin_eval_new_int eval new_int.simps)
  then obtain xv yv where addv: "[m, p] \<turnstile> exp[x + y] \<mapsto> IntVal b (xv + yv)"
    apply (subst (asm) unfold_binary_width_and) by (metis add.right_neutral)
  then obtain yv where yv: "[m, p] \<turnstile> y \<mapsto> IntVal b yv"
    apply (subst (asm) unfold_binary_width_add) by blast
  from addv obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
    apply (subst (asm) unfold_binary_width_add) by blast
  from val obtain zv where zv: "[m, p] \<turnstile> z \<mapsto> IntVal b zv"
    apply (subst (asm) unfold_binary_width_and) by blast
  have addv: "[m, p] \<turnstile> exp[x + y] \<mapsto> new_int b (xv + yv)"
    apply (rule evaltree.BinaryExpr)
    using xv apply simp
    using yv apply simp
    by simp+
  have lhs: "[m, p] \<turnstile> exp[(x + y) & z] \<mapsto> new_int b (and (xv + yv) zv)"
    apply (rule evaltree.BinaryExpr)
    using addv apply simp
    using zv apply simp
    using addv apply auto[1]
    by simp
  have rhs: "[m, p] \<turnstile> exp[x & z] \<mapsto> new_int b (and xv zv)"
    apply (rule evaltree.BinaryExpr)
    using xv apply simp
    using zv apply simp
     apply force
    by simp
  then show ?thesis
  proof (cases "numberOfLeadingZeros (\<up>z) > 0")
    case True
    have n_bounds: "0 \<le> n \<and> n < 64"
      using diff_le_self n numberOfLeadingZeros_range
      by (simp add: True)
    have "and (xv + yv) zv = and ((xv + yv) mod 2^n) zv"
      using L1 n zv by blast
    also have "... = and ((xv + (yv mod 2^n)) mod 2^n) zv"
      using mod_dist_over_add_right n_bounds
      by (metis take_bit_0 take_bit_eq_mod zero_less_iff_neq_zero)
    also have "... = and (((xv mod 2^n) + (yv mod 2^n)) mod 2^n) zv"
      by (metis bits_mod_by_1 mod_dist_over_add n_bounds order_le_imp_less_or_eq power_0)
    also have "... = and ((xv mod 2^n) mod 2^n) zv"
      using L2 n zv yv
      using assms by auto
    also have "... = and (xv mod 2^n) zv"
      using mod_mod_trivial
      by (smt (verit, best) and.idem take_bit_eq_mask take_bit_eq_mod word_bw_assocs(1))
    also have "... = and xv zv"
      using L1 n zv by metis
    finally show ?thesis
      using eval lhs rhs
      by (metis evalDet)
  next
    case False
    then have "numberOfLeadingZeros (\<up>z) = 0"
      by simp
    then have "numberOfTrailingZeros (\<up>y) \<ge> 64"
      using assms(1)
      by fastforce 
    then have "yv = 0"
      using yv
      by (metis (no_types, lifting) L1 L2 add_diff_cancel_left' and.comm_neutral and.idem bit.compl_zero bit.conj_cancel_right bit.conj_disj_distribs(1) bit.double_compl less_imp_diff_less linorder_not_le word_not_dist(2))
    then show ?thesis
      by (metis add.right_neutral eval evalDet lhs rhs)
  qed
qed
done

thm_oracles improved_opt

lemma falseBelowN_nBelowLowest:
  assumes "n \<le> Nat.size a"
  assumes "\<forall> i < n. \<not>(bit a i)"
  shows "lowestOneBit a \<ge> n"
proof (cases "{i. bit a i} = {}")
  case True
  then show ?thesis unfolding lowestOneBit_def MinOrHighest_def
    using assms(1) trans_le_add1 by presburger
next
  case False
  have "n \<le> Min (Collect (bit a))"
    by (metis False Min_ge_iff assms(2) finite_bit_word linorder_le_less_linear mem_Collect_eq)
  then show ?thesis unfolding lowestOneBit_def MinOrHighest_def
    using False by presburger
qed

lemma noZeros:
  fixes a :: "64 word"
  assumes "zeroCount a = 0"
  shows "i < Nat.size a \<longrightarrow> bit a i"
  using assms unfolding zeroCount_def size64
  using zeroCount_finite by auto

lemma zerosAboveOnly:
  fixes a :: "64 word"
  assumes "numberOfLeadingZeros a = zeroCount a"
  shows "\<not>(bit a i) \<longrightarrow> i \<ge> (64 - numberOfLeadingZeros a)"
  sorry
(*proof -
  have "a = 2^(64 - numberOfLeadingZeros a)"
    using assms 
    unfolding numberOfLeadingZeros_def zeroCount_def highestOneBit_def MaxOrNeg_def sorry
  then show ?thesis sorry
qed
  apply (rule impI) subgoal premises notSet
proof -
  obtain z where "zeroCount a = zeroCount (z::64 word)"
    by auto
  have adef: "a = 2^(64- numberOfLeadingZeros a) * (1 + z)"
    sorry
  have "and a (2^i) = 0"
    using notSet
    by (simp add: and_exp_eq_0_iff_not_bit)
  then have "a = and (2^(64- numberOfLeadingZeros a) * (1 + z)) (2^i)"
    using adef sorry

  using assms proof (induction "numberOfLeadingZeros a"; induction i)
  case 0
  then have "zeroCount a = 0"
    using assms by presburger
  then have notSet: "\<forall>i < Nat.size a. bit a i"
    using noZeros by blast
  have "64 - numberOfLeadingZeros a \<le> Nat.size a"
    using numberOfLeadingZeros_range size64 by simp
  then show ?case
    using linorder_le_less_linear notSet size64
    by (metis word_size_gt_0)
next
  case (Suc x)
  then have "\<not>(bit a (Suc x))"
    sorry
  then show ?case unfolding zeroCount_def using zeroCount_finite sorry
qed*)


lemma consumes: 
  assumes "numberOfLeadingZeros (\<up>z) + bitCount (\<up>z) = 64"
  and "\<up>z \<noteq> 0"
  and "and (\<up>y) (\<up>z) = 0"
  shows "numberOfLeadingZeros (\<up>z) + numberOfTrailingZeros (\<up>y) \<ge> 64"
proof -
  obtain n where "n = 64 - numberOfLeadingZeros (\<up>z)"
    by simp
  then have "n = bitCount (\<up>z)"
    by (metis add_diff_cancel_left' assms(1))
  have "numberOfLeadingZeros (\<up>z) = zeroCount (\<up>z)"
    using assms(1) size64 ones_zero_sum_to_width
    by (metis add.commute add_left_imp_eq)
  then have "\<forall>i. \<not>(bit (\<up>z) i) \<longrightarrow> i \<ge> n"
    using assms(1) zerosAboveOnly
    using \<open>(n::nat) = (64::nat) - numberOfLeadingZeros (\<up> (z::IRExpr))\<close> by blast
  then have "\<forall> i < n. bit (\<up>z) i"
    using leD by blast
  then have "\<forall> i < n. \<not>(bit (\<up>y) i)"
    using assms(3)
    by (metis bit.conj_cancel_right bit_and_iff bit_not_iff)
  then have "lowestOneBit (\<up>y) \<ge> n"
    by (simp add: \<open>(n::nat) = (64::nat) - numberOfLeadingZeros (\<up> (z::IRExpr))\<close> falseBelowN_nBelowLowest size64)
  then have "n \<le> numberOfTrailingZeros (\<up>y)"
    unfolding numberOfTrailingZeros_def
    by simp
  have "card {i. i < n} = bitCount (\<up>z)"
    by (simp add: \<open>(n::nat) = bitCount (\<up> (z::IRExpr))\<close>)
  then have "bitCount (\<up>z) \<le> numberOfTrailingZeros (\<up>y)"
    using \<open>(n::nat) \<sqsubseteq> numberOfTrailingZeros (\<up> (y::IRExpr))\<close> by auto
  then show ?thesis using assms(1) by auto
qed

thm_oracles consumes

(*
lemma wrong:
  assumes "numberOfLeadingZeros (\<down>z) + highestOneBit (\<down>z) = 64"
  assumes "\<down>z \<noteq> 0"
  assumes "and (\<up>y) (\<down>z) = 0"
  shows "exp[(x + y) & z] \<ge> x"
  using assms apply auto sorry

lemma wrong2:
  (* assumes "numberOfLeadingZeros (\<up>z) + highestOneBit (\<up>z) = 64" see: leadingZerosAddHighestOne *)
  assumes "\<up>z \<noteq> 0"
  assumes "and (\<up>y) (\<up>z) = 0"
  shows "exp[(x + y) & z] \<ge> x"
  using assms apply simp apply (rule allI)+
  subgoal premises p for m p v apply (rule impI) subgoal premises e
    print_facts
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using e by auto
    obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> yv"
      using e by auto
    obtain zv where zv: "[m,p] \<turnstile> z \<mapsto> zv"
      using e by auto
    have lhs: "v = val[(xv + yv) & zv]"
      using xv yv zv
      by (smt (verit, best) BinaryExprE bin_eval.simps(1) bin_eval.simps(4) e evalDet)
    have "val[yv & zv] \<noteq> UndefVal"
      sorry
    also have "\<exists>b. val[yv & zv] = new_int b 0"
      using intval_up_and_zero_implies_zero yv zv p(2)
      using calculation by presburger
    ultimately have rhs: "v = val[xv & zv]"
      using intval_eliminate_y lhs sorry
    from lhs rhs show ?thesis sorry
  qed
  done
  done*)

lemma right:
  assumes "numberOfLeadingZeros (\<up>z) + bitCount (\<up>z) = 64"
  assumes "\<up>z \<noteq> 0"
  assumes "and (\<up>y) (\<up>z) = 0"
  shows "exp[(x + y) & z] \<ge> exp[x & z]"
apply simp apply (rule allI)+ 
  subgoal premises p for m p v apply (rule impI) subgoal premises e
proof -
  obtain j where j: "j = highestOneBit (\<up>z)"
    by simp
  obtain xv b where xv: "[m,p] \<turnstile> x \<mapsto> IntVal b xv"
    using e
    by (metis EvalTreeE(5) bin_eval_inputs_are_ints bin_eval_new_int new_int.simps)
  obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> IntVal b yv"
    using e EvalTreeE(5) bin_eval_inputs_are_ints bin_eval_new_int new_int.simps
    by (smt (verit) Value.sel(1) bin_eval.simps(1) evalDet intval_add.elims xv)
  obtain xyv where xyv: "[m, p] \<turnstile> exp[x + y] \<mapsto> IntVal b xyv"
    using e EvalTreeE(5) bin_eval_inputs_are_ints bin_eval_new_int new_int.simps
    xv yv
    by (metis BinaryExpr Value.distinct(1) bin_eval.simps(1) intval_add.simps(1))
  then obtain zv where zv: "[m,p] \<turnstile> z \<mapsto> IntVal b zv"
    using e EvalTreeE(5) bin_eval_inputs_are_ints bin_eval_new_int new_int.simps
    Value.sel(1) bin_eval.simps(4) evalDet intval_and.elims
    by (smt (verit) new_int_bin.simps)
  have "xyv = take_bit b (xv + yv)"
    using xv yv xyv
    by (metis BinaryExprE Value.sel(2) bin_eval.simps(1) evalDet intval_add.simps(1))
  then have "v = IntVal b (take_bit b (and (take_bit b (xv + yv)) zv))"
    using zv
    by (smt (verit) EvalTreeE(5) Value.sel(1) Value.sel(2) bin_eval.simps(4) e evalDet intval_and.elims new_int.simps new_int_bin.simps xyv)
  then have veval: "v = IntVal b (and (xv + yv) zv)"
    by (metis (no_types, lifting) eval_unused_bits_zero take_bit_eq_mask word_bw_comms(1) word_bw_lcs(1) zv)
  have obligation: "(and (xv + yv) zv) = (and xv zv) \<Longrightarrow> [m,p] \<turnstile> BinaryExpr BinAnd x z \<mapsto> v"
    by (smt (verit) EvalTreeE(5) Value.inject(1) \<open>(v::Value) = IntVal (b::nat) (take_bit b (and (take_bit b ((xv::64 word) + (yv::64 word))) (zv::64 word)))\<close> \<open>(xyv::64 word) = take_bit (b::nat) ((xv::64 word) + (yv::64 word))\<close> bin_eval.simps(4) e evalDet eval_unused_bits_zero evaltree.simps intval_and.simps(1) take_bit_and xv xyv zv)
  have per_bit: "\<forall>n . bit (and (xv + yv) zv) n = bit (and xv zv) n \<Longrightarrow> (and (xv + yv) zv) = (and xv zv)"
    by (simp add: bit_eq_iff)
  show ?thesis
    apply (rule obligation)
    apply (rule per_bit)
    apply (rule allI)
    subgoal for n
  proof (cases "n \<le> j")
    case True
    (*
    then have "\<not>(bit yv n)"
      by (metis (no_types, opaque_lifting) assms(1) assms(2) assms(3) bit_and_iff bit_not_iff impossible_bit j packed_bits ucast_id up_spec yv)
    have "\<forall>n' . n' \<le> n \<longrightarrow> \<not>(bit yv n')"
      by (metis (no_types, lifting) True assms(1) assms(2) assms(3) bit_and_iff bit_not_iff down_spec dual_order.trans j not_may_implies_false packed_bits yv)
    then have "bit (xv + yv) n = bit xv n"
      sorry using packed_bottom_zeros_elim_add
      by blast*)
    then show ?thesis sorry
      (*by (simp add: bit_and_iff)*)
  next
    case False
    then have "\<not>(bit zv n)"
      by (metis j linorder_not_less not_may_implies_false zerosAboveHighestOne zv)
    then have v: "\<not>(bit (and (xv + yv) zv) n)"
      by (simp add: bit_and_iff)
    then have v': "\<not>(bit (and xv zv) n)"
      by (simp add: \<open>\<not> bit (zv::64 word) (n::nat)\<close> bit_and_iff)
    from v v' show ?thesis
      by simp
  qed
  done
qed
  done
  done

end

lemma ucast_zero: "(ucast (0::int64)::int32) = 0"
  by simp

lemma ucast_minus_one: "(ucast (-1::int64)::int32) = -1"
  apply transfer by auto

interpretation simple_mask: stamp_mask
  "IRExpr_up :: IRExpr \<Rightarrow> int64"
  "IRExpr_down :: IRExpr \<Rightarrow> int64"
  unfolding IRExpr_up_def IRExpr_down_def
  apply unfold_locales
  by (simp add: ucast_minus_one)+



phase NewAnd
  terminating size
begin

optimization redundant_lhs_y_or: "((x | y) & z) \<longmapsto> x & z
                                when (((and (IRExpr_up y) (IRExpr_up z)) = 0))"
  using simple_mask.exp_eliminate_y by blast

optimization redundant_lhs_x_or: "((x | y) & z) \<longmapsto> y & z
                                when (((and (IRExpr_up x) (IRExpr_up z)) = 0))"
  using simple_mask.exp_eliminate_y
  by (meson exp_or_commute mono_binary order_refl order_trans)

optimization redundant_rhs_y_or: "(z & (x | y)) \<longmapsto> z & x
                                when (((and (IRExpr_up y) (IRExpr_up z)) = 0))"
  using simple_mask.exp_eliminate_y
  by (meson exp_and_commute order.trans)

optimization redundant_rhs_x_or: "(z & (x | y)) \<longmapsto> z & y
                                when (((and (IRExpr_up x) (IRExpr_up z)) = 0))"
  using simple_mask.exp_eliminate_y
  by (meson dual_order.trans exp_and_commute exp_or_commute mono_binary order_refl)

(*
optimization redundant_lhs_add: "((x + y) & z) \<longmapsto> x & z
                               when ((and (IRExpr_up y) (IRExpr_down z)) = 0)"
*)

end

end