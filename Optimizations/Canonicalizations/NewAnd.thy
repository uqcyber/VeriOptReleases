subsection \<open>Experimental AndNode Phase\<close>

theory NewAnd
  imports
    Common
    Graph.JavaLong
    Proofs.StampEvalThms
begin


locale stamp_mask_singleton =
  fixes x y :: "IRExpr"
  fixes up :: "IRExpr \<Rightarrow> int64" ("\<up>")
  fixes down :: "IRExpr \<Rightarrow> int64" ("\<down>")
  assumes up_spec: "\<forall>e \<in> {x, y}. (\<forall>m p b v. ([m, p] \<turnstile> e \<mapsto> IntVal b v) \<longrightarrow> ((and v (not (\<up>e))) = 0))"
      and down_spec: "\<forall>e \<in> {x, y}. (\<forall>m p b v. ([m, p] \<turnstile> e \<mapsto> IntVal b v) \<longrightarrow> ((and (not v) (\<down>e)) = 0))"
begin

lemma may_implies_either:
  "\<forall>e \<in> {x, y}. (\<exists>m p b v. ([m, p] \<turnstile> e \<mapsto> IntVal b v) \<longrightarrow> bit (\<up>e) n \<longrightarrow> bit v n = False \<or> bit v n = True)"
  by simp

lemma not_may_implies_false:
  "\<forall>e \<in> {x, y}. (\<forall>m p b v. ([m, p] \<turnstile> e \<mapsto> IntVal b v) \<longrightarrow> \<not>(bit (\<up>e) n) \<longrightarrow> bit v n = False)"
  by (metis (no_types, lifting) bit.double_compl up_spec bit_and_iff bit_not_iff 
      down_spec)

lemma must_implies_true:
  "\<forall>e \<in> {x, y}. (\<forall>m p b v. ([m, p] \<turnstile> e \<mapsto> IntVal b v) \<longrightarrow> bit (\<down>e) n \<longrightarrow> bit v n = True)"
  by (metis bit.compl_one bit_and_iff bit_minus_1_iff bit_not_iff impossible_bit down_spec)

lemma not_must_implies_either:
  "\<forall>e \<in> {x, y}. (\<forall>m p b v. ([m, p] \<turnstile> e \<mapsto> IntVal b v) \<longrightarrow> \<not>(bit (\<down>e) n) \<longrightarrow> bit v n = False \<or> bit v n = True)"
  by simp

lemma must_implies_may:
  "\<forall>e \<in> {x, y}. (\<forall>m p b v. ([m, p] \<turnstile> e \<mapsto> IntVal b v) \<longrightarrow> bit (\<down>e) n \<longrightarrow> bit (\<up>e) n)"
  by (meson must_implies_true not_may_implies_false)

lemma up_mask_and_zero_implies_zero:
  assumes "and (\<up>x) (\<up>y) = 0"
  assumes "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
  assumes "[m, p] \<turnstile> y \<mapsto> IntVal b yv"
  shows "and xv yv = 0"
proof -
  have f1: "and yv (not (\<up> y)) = 0"
    by (meson assms(3) insertCI up_spec)
  have "and xv (not (\<up> x)) = 0"
    by (meson assms(2) insertCI up_spec)
  then show ?thesis
    using f1 by (metis (no_types) and.right_neutral assms(1) bit.compl_zero bit.conj_disj_distrib word_bw_lcs(1) word_log_esimps(1) word_not_dist(2))
qed

lemma not_down_up_mask_and_zero_implies_zero:
  assumes "and (not (\<down>x)) (\<up>y) = 0"
  assumes "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
  assumes "[m, p] \<turnstile> y \<mapsto> IntVal b yv"
  shows "and xv yv = yv"
  proof -
    have f1: "and (not xv) (\<down> x) = 0"
      using assms(2) down_spec by blast
    have "\<And>w. or 0 (and yv w) = and yv w"
      by simp
    have "and xv (not (\<up> x)) = 0"
      by (meson assms(2) insertCI up_spec)
    then show ?thesis
      using f1
    proof -
      have "\<And>w wa. or (and (w::64 word) wa) w = w"
        by simp
      then show ?thesis
        by (metis (no_types) assms(1) assms(3) bit.conj_cancel_right bit.conj_disj_distrib bit.double_compl f1 insertCI up_spec word_bw_comms(1) word_not_dist(2))
    qed
  qed

end


lemma intval_distribute_and_over_or:
  "val[z & (x | y)] = val[(z & x) | (z & y)]"
  by (cases x; cases y; cases z; auto simp add: bit.conj_disj_distrib)

lemma exp_distribute_and_over_or:
  "exp[z & (x | y)] \<ge> exp[(z & x) | (z & y)]"
  apply auto[1]
  by (metis bin_eval.simps(6,7) intval_or.simps(2,6) intval_distribute_and_over_or BinaryExpr)

lemma intval_and_commute:
  "val[x & y] = val[y & x]"
  by (cases x; cases y; auto simp: and.commute)

lemma intval_or_commute:
  "val[x | y] = val[y | x]"
  by (cases x; cases y; auto simp: or.commute)

lemma intval_xor_commute:
  "val[x ^ y] = val[y ^ x]"
  by (cases x; cases y; auto simp: xor.commute)

lemma exp_and_commute:
  "exp[x & z] \<ge> exp[z & x]"
  by (auto simp: intval_and_commute)

lemma exp_or_commute:
  "exp[x | y] \<ge> exp[y | x]"
  by (auto simp: intval_or_commute)

lemma exp_xor_commute:
  "exp[x ^ y] \<ge> exp[y ^ x]"
  by (auto simp: intval_xor_commute)

lemma intval_eliminate_y:
  assumes "val[y & z] = IntVal b 0"
  shows "val[(x | y) & z] = val[x & z]"
  using assms by (cases x; cases y; cases z; auto simp add: bit.conj_disj_distrib2)

lemma intval_and_associative:
  "val[(x & y) & z] = val[x & (y & z)]"
  by (cases x; cases y; cases z; auto simp: and.assoc)

lemma intval_or_associative:
  "val[(x | y) | z] = val[x | (y | z)]"
  by (cases x; cases y; cases z; auto simp: or.assoc) 

lemma intval_xor_associative:
  "val[(x ^ y) ^ z] = val[x ^ (y ^ z)]"
  by (cases x; cases y; cases z; auto simp: xor.assoc)

lemma exp_and_associative:
  "exp[(x & y) & z] \<ge> exp[x & (y & z)]"
  using intval_and_associative by fastforce

lemma exp_or_associative:
  "exp[(x | y) | z] \<ge> exp[x | (y | z)]"
  using intval_or_associative by fastforce

lemma exp_xor_associative:
  "exp[(x ^ y) ^ z] \<ge> exp[x ^ (y ^ z)]"
  using intval_xor_associative by fastforce

lemma intval_and_absorb_or:
  assumes "\<exists>b v . x = new_int b v" (* TODO: required? *)
  assumes "val[x & (x | y)] \<noteq> UndefVal"
  shows "val[x & (x | y)] = val[x]"
  using assms apply (cases x; cases y; auto)
  by (metis (full_types) intval_and.simps(6))

lemma intval_or_absorb_and:
  assumes "\<exists>b v . x = new_int b v" (* TODO: required? *)
  assumes "val[x | (x & y)] \<noteq> UndefVal"
  shows "val[x | (x & y)] = val[x]"
  using assms apply (cases x; cases y; auto)
  by (metis (full_types) intval_or.simps(6))

lemma exp_and_absorb_or:
  "exp[x & (x | y)] \<ge> exp[x]"
  apply auto[1]
  subgoal premises p for m p xa xaa ya
  proof-
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p(1) by auto
    obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> yv"
      using p(4) by auto
    then have lhsDefined: "val[xv & (xv | yv)] \<noteq> UndefVal"
      by (metis evalDet p(1,2,3,4) xv)
    obtain xb xvv where xvv: "xv = IntVal xb xvv"
      by (metis Value.exhaust_sel intval_and.simps(2,3,4,5) lhsDefined)
    obtain yb yvv where yvv: "yv = IntVal yb yvv"
      by (metis Value.exhaust_sel intval_and.simps(6) intval_or.simps(6,7,8,9) lhsDefined)
    then have valEval: "val[xv & (xv | yv)] = val[xv]"
      by (metis eval_unused_bits_zero intval_and_absorb_or lhsDefined new_int.elims xv xvv)
    then show ?thesis
      by (metis evalDet p(1,3,4) xv yv)
  qed
  done

lemma exp_or_absorb_and:
  "exp[x | (x & y)] \<ge> exp[x]"
  apply auto[1]
  subgoal premises p for m p xa xaa ya
  proof-
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p(1) by auto
    obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> yv"
      using p(4) by auto
    then have lhsDefined: "val[xv | (xv & yv)] \<noteq> UndefVal"
      by (metis evalDet p(1,2,3,4) xv)
    obtain xb xvv where xvv: "xv = IntVal xb xvv"
      by (metis Value.exhaust_sel intval_and.simps(3,4,5) intval_or.simps(2,6) lhsDefined)
    obtain yb yvv where yvv: "yv = IntVal yb yvv"
      by (metis Value.exhaust_sel intval_and.simps(6,7,8,9) intval_or.simps(6) lhsDefined)
    then have valEval: "val[xv | (xv & yv)] = val[xv]"
      by (metis eval_unused_bits_zero intval_or_absorb_and lhsDefined new_int.elims xv xvv)
    then show ?thesis
      by (metis evalDet p(1,3,4) xv yv)
  qed
  done

lemma
  assumes "y = 0"
  shows "x + y = or x y"
  by (simp add: assms)

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
  by (metis bit_and_iff bit_xor_iff disjunctive_add xor_self_eq assms)

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

context stamp_mask_singleton
begin

lemma intval_up_and_zero_implies_zero:
  assumes "and (\<up>x) (\<up>y) = 0"
  assumes "[m, p] \<turnstile> x \<mapsto> xv"
  assumes "[m, p] \<turnstile> y \<mapsto> yv"
  assumes "val[xv & yv] \<noteq> UndefVal"
  shows "\<exists> b . val[xv & yv] = new_int b 0"
  using assms apply (cases xv; cases yv; auto)
  using eval_unused_bits_zero up_mask_and_zero_implies_zero apply presburger
  by presburger

lemma exp_eliminate_y:
  "and (\<up>y) (\<up>x) = 0 \<longrightarrow> exp[(z | y) & x] \<ge> exp[z & x]"
  apply simp apply (rule impI; rule allI; rule allI; rule allI) 
  subgoal premises p for m p v apply (rule impI) subgoal premises e
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using e by auto
    obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> yv"
      using e by auto
    obtain zv where zv: "[m,p] \<turnstile> z \<mapsto> zv"
      using e by auto
    have lhs: "v = val[(zv | yv) & xv]" 
      by (smt (verit, best) BinaryExprE bin_eval.simps(6,7) e evalDet xv yv zv)
    then have "v = val[(zv & xv) | (yv & xv)]"
      by (simp add: intval_and_commute intval_distribute_and_over_or)
    also have "\<exists>b. val[yv & xv] = new_int b 0"
      by (metis calculation e eval_thms(77) intval_and_commute p stamp_mask_singleton.intval_up_and_zero_implies_zero stamp_mask_singleton_axioms unfold_binary word_bw_comms(1) xv yv)
    ultimately have rhs: "v = val[zv & xv]"
      by (auto simp: intval_eliminate_y lhs)
    from lhs rhs show ?thesis
      by (metis BinaryExpr BinaryExprE bin_eval.simps(6) e xv zv)
  qed
  done
  done

lemma leadingZeroBounds:
  fixes v :: "'a::len word"
  assumes "n = numberOfLeadingZeros v"
  shows "0 \<le> n \<and> n \<le> Nat.size v"
  by (simp add: MaxOrNeg_def highestOneBit_def nat_le_iff numberOfLeadingZeros_def assms)

lemma above_nth_not_set:
  fixes v :: int64
  assumes "n = 64 - numberOfLeadingZeros v"
  shows "j > n \<longrightarrow> \<not>(bit v j)"
  by (smt (verit, ccfv_SIG) highestOneBit_def int_nat_eq int_ops(6) less_imp_of_nat_less size64 
      max_set_bit zerosAboveHighestOne assms numberOfLeadingZeros_def)

no_notation LogicNegationNotation ("!_")

lemma zero_horner:
  "horner_sum of_bool 2 (map (\<lambda>x. False) xs) = 0"
  by (induction xs; auto)

lemma zero_map:
  assumes "j \<le> n"
  assumes "\<forall>i. j \<le> i \<longrightarrow> \<not>(f i)"
  shows "map f [0..<n] = map f [0..<j] @ map (\<lambda>x. False) [j..<n]"
  by (smt (verit, del_insts) add_diff_inverse_nat atLeastLessThan_iff bot_nat_0.extremum leD assms
      map_append map_eq_conv set_upt upt_add_eq_append)

lemma map_join_horner:
  assumes "map f [0..<n] = map f [0..<j] @ map (\<lambda>x. False) [j..<n]"
  shows "horner_sum of_bool (2::'a::len word) (map f [0..<n]) = horner_sum of_bool 2 (map f [0..<j])"
proof -
  have "horner_sum of_bool (2::'a::len word) (map f [0..<n]) = horner_sum of_bool 2 (map f [0..<j]) + 2 ^ length [0..<j] * horner_sum of_bool 2 (map f [j..<n])"
    using assms apply auto[1]
    by (smt (verit) assms diff_le_self diff_zero le_add_same_cancel2 length_append length_map
        length_upt map_append upt_add_eq_append horner_sum_append)
  also have "... = horner_sum of_bool 2 (map f [0..<j]) + 2 ^ length [0..<j] * horner_sum of_bool 2 (map (\<lambda>x. False) [j..<n])"
    by (metis calculation horner_sum_append length_map assms)
  also have "... = horner_sum of_bool 2 (map f [0..<j])"
    using zero_horner mult_not_zero by auto
  finally show ?thesis 
    by simp
qed

lemma split_horner:
  assumes "j \<le> n"
  assumes "\<forall>i. j \<le> i \<longrightarrow> \<not>(f i)"
  shows "horner_sum of_bool (2::'a::len word) (map f [0..<n]) = horner_sum of_bool 2 (map f [0..<j])"
  by (auto simp: assms zero_map map_join_horner)

lemma transfer_map:
  assumes "\<forall>i. i < n \<longrightarrow> f i = f' i"
  shows "(map f [0..<n]) = (map f' [0..<n])"
  by (simp add: assms)

lemma transfer_horner:
  assumes "\<forall>i. i < n \<longrightarrow> f i = f' i"
  shows "horner_sum of_bool (2::'a::len word) (map f [0..<n]) = horner_sum of_bool 2 (map f' [0..<n])"
  by (smt (verit, best) assms transfer_map)

lemma L1:
  assumes "n = 64 - numberOfLeadingZeros (\<up>x)"
  assumes "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
  shows "and v xv = and (v mod 2^n) xv"
proof -
  have nle: "n \<le> 64"
    using assms diff_le_self by blast
  also have "and v xv = horner_sum of_bool 2 (map (bit (and v xv)) [0..<64])"
    by (metis size_word.rep_eq take_bit_length_eq horner_sum_bit_eq_take_bit size64)
  also have "... = horner_sum of_bool 2 (map (\<lambda>i. bit (and v xv) i) [0..<64])"
    by blast
  also have "... = horner_sum of_bool 2 (map (\<lambda>i. ((bit v i) \<and> (bit xv i))) [0..<64])"
    by (metis bit_and_iff)
  also have "... = horner_sum of_bool 2 (map (\<lambda>i. ((bit v i) \<and> (bit xv i))) [0..<n])"
  proof -
    have "\<forall>i. i \<ge> n \<longrightarrow> \<not>(bit xv i)"
      using  One_nat_def diff_less int_ops(6) leadingZerosAddHighestOne assms
          linorder_not_le nat_int_comparison(2) not_numeral_le_zero size64 zero_less_Suc 
          zerosAboveHighestOne not_may_implies_false
      by (smt (verit, ccfv_threshold) insertCI)
    then have "\<forall>i. i \<ge> n \<longrightarrow> \<not>((bit v i) \<and> (bit xv i))"
      by auto
    then show ?thesis using nle split_horner
      by (metis (no_types, lifting))
  qed
  also have "... = horner_sum of_bool 2 (map (\<lambda>i. ((bit (v mod 2^n) i) \<and> (bit xv i))) [0..<n])"
  proof -
    have "\<forall>i. i < n \<longrightarrow> bit (v mod 2^n) i = bit v i"
      by (metis bit_take_bit_iff take_bit_eq_mod)
    then have "\<forall>i. i < n \<longrightarrow> ((bit v i) \<and> (bit xv i)) = ((bit (v mod 2^n) i) \<and> (bit xv i))"
      by force
    then show ?thesis
      by (rule transfer_horner)
  qed
  also have "... = horner_sum of_bool 2 (map (\<lambda>i. ((bit (v mod 2^n) i) \<and> (bit xv i))) [0..<64])"
  proof -
    have "\<forall>i. i \<ge> n \<longrightarrow> \<not>(bit xv i)"
      using  One_nat_def diff_less int_ops(6) leadingZerosAddHighestOne assms
          linorder_not_le nat_int_comparison(2) not_numeral_le_zero size64 zero_less_Suc 
          zerosAboveHighestOne not_may_implies_false
      by (smt (verit, ccfv_threshold) insertCI)
    then show ?thesis
      by (metis (no_types, lifting) assms(1) diff_le_self split_horner)
  qed
  also have "... = horner_sum of_bool 2 (map (bit (and (v mod 2^n) xv)) [0..<64])"
    by (meson bit_and_iff)
  also have "... = and (v mod 2^n) xv"
    by (metis size_word.rep_eq take_bit_length_eq horner_sum_bit_eq_take_bit size64)
  finally show ?thesis
    using \<open>and (v::64 word) (xv::64 word) = horner_sum of_bool (2::64 word) (map (bit (and v xv)) [0::nat..<64::nat])\<close> \<open>horner_sum of_bool (2::64 word) (map (\<lambda>i::nat. bit ((v::64 word) mod (2::64 word) ^ (n::nat)) i \<and> bit (xv::64 word) i) [0::nat..<64::nat]) = horner_sum of_bool (2::64 word) (map (bit (and (v mod (2::64 word) ^ n) xv)) [0::nat..<64::nat])\<close> \<open>horner_sum of_bool (2::64 word) (map (\<lambda>i::nat. bit ((v::64 word) mod (2::64 word) ^ (n::nat)) i \<and> bit (xv::64 word) i) [0::nat..<n]) = horner_sum of_bool (2::64 word) (map (\<lambda>i::nat. bit (v mod (2::64 word) ^ n) i \<and> bit xv i) [0::nat..<64::nat])\<close> \<open>horner_sum of_bool (2::64 word) (map (\<lambda>i::nat. bit (v::64 word) i \<and> bit (xv::64 word) i) [0::nat..<64::nat]) = horner_sum of_bool (2::64 word) (map (\<lambda>i::nat. bit v i \<and> bit xv i) [0::nat..<n::nat])\<close> \<open>horner_sum of_bool (2::64 word) (map (\<lambda>i::nat. bit (v::64 word) i \<and> bit (xv::64 word) i) [0::nat..<n::nat]) = horner_sum of_bool (2::64 word) (map (\<lambda>i::nat. bit (v mod (2::64 word) ^ n) i \<and> bit xv i) [0::nat..<n])\<close> \<open>horner_sum of_bool (2::64 word) (map (bit (and ((v::64 word) mod (2::64 word) ^ (n::nat)) (xv::64 word))) [0::nat..<64::nat]) = and (v mod (2::64 word) ^ n) xv\<close> \<open>horner_sum of_bool (2::64 word) (map (bit (and (v::64 word) (xv::64 word))) [0::nat..<64::nat]) = horner_sum of_bool (2::64 word) (map (\<lambda>i::nat. bit v i \<and> bit xv i) [0::nat..<64::nat])\<close> by presburger
qed

lemma up_mask_upper_bound:
  assumes "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
  shows "xv \<le> (\<up>x)"
  using  and.right_neutral bit.conj_cancel_left bit.conj_disj_distribs(1)
      bit.double_compl up_spec word_and_le1 word_not_dist(2) assms
  by (metis (no_types, lifting) insertCI)

lemma L2:
  assumes "numberOfLeadingZeros (\<up>x) + numberOfTrailingZeros (\<up>y) \<ge> 64"
  assumes "n = 64 - numberOfLeadingZeros (\<up>x)"
  assumes "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
  assumes "[m, p] \<turnstile> y \<mapsto> IntVal b yv"
  shows "yv mod 2^n = 0"
proof -
  have "yv mod 2^n = horner_sum of_bool 2 (map (bit yv) [0..<n])"
    by (simp add: horner_sum_bit_eq_take_bit take_bit_eq_mod)
  also have "... \<le> horner_sum of_bool 2 (map (bit (\<up>y)) [0..<n])"
    using and.right_neutral bit.conj_cancel_right word_not_dist(2)
        bit.conj_disj_distribs(1) bit.double_compl horner_sum_bit_eq_take_bit take_bit_and ucast_id 
        up_spec word_and_le1 assms(4)
    proof -
      have "0 = and yv (not (\<up> y))"
        using assms(4) up_spec by auto
      then show ?thesis
        by (metis (no_types) and.comm_neutral bit.conj_cancel_right bit.conj_disj_distribs(1) bit.double_compl horner_sum_bit_eq_take_bit take_bit_and word_and_le1 word_not_dist(2))
    qed
  also have "horner_sum of_bool 2 (map (bit (\<up>y)) [0..<n]) = horner_sum of_bool 2 (map (\<lambda>x. False) [0..<n])"
  proof -
    have "\<forall>i < n. \<not>(bit (\<up>y) i)"
      by (metis add.commute add_diff_inverse_nat add_lessD1 leD le_diff_conv zerosBelowLowestOne
          numberOfTrailingZeros_def assms(1,2))
    then show ?thesis
      by (metis (full_types) transfer_map)
  qed
  also have "horner_sum of_bool 2 (map (\<lambda>x. False) [0..<n]) = 0"
    by (auto simp: zero_horner)
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
  using unfold_binary_width by simp

lemma unfold_binary_width_and:
  shows "([m,p] \<turnstile> BinaryExpr BinAnd xe ye \<mapsto> IntVal b val) = (\<exists> x y.
          (([m,p] \<turnstile> xe \<mapsto> IntVal b x) \<and>
           ([m,p] \<turnstile> ye \<mapsto> IntVal b y) \<and>
           (IntVal b val = bin_eval BinAnd (IntVal b x) (IntVal b y)) \<and>
           (IntVal b val \<noteq> UndefVal)
        ))" (is "?L = ?R")
  using unfold_binary_width by simp

lemma mod_dist_over_add_right:
  fixes a b c :: int64
  fixes n :: nat
  assumes "0 < n"
  assumes "n < 64"
  shows "(a + b mod 2^n) mod 2^n = (a + b) mod 2^n"
  using mod_dist_over_add by (simp add: assms add.commute)

lemma numberOfLeadingZeros_range:
  "0 \<le> numberOfLeadingZeros n \<and> numberOfLeadingZeros n \<le> Nat.size n"
  by (simp add: leadingZeroBounds)

lemma improved_opt:
  assumes "numberOfLeadingZeros (\<up>x) + numberOfTrailingZeros (\<up>y) \<ge> 64"
  shows "exp[(z + y) & x] \<ge> exp[z & x]"
  apply simp apply ((rule allI)+; rule impI)
  subgoal premises eval for m p v
proof -
  obtain n where n: "n = 64 - numberOfLeadingZeros (\<up>x)"
    by simp
  obtain b val where val: "[m, p] \<turnstile> exp[(z + y) & x] \<mapsto> IntVal b val"
    by (metis BinaryExprE bin_eval_new_int eval new_int.simps)
  then obtain zv yv where addv: "[m, p] \<turnstile> exp[z + y] \<mapsto> IntVal b (zv + yv)"
    apply (subst (asm) unfold_binary_width_and) by (metis add.right_neutral)
  then obtain yv where yv: "[m, p] \<turnstile> y \<mapsto> IntVal b yv"
    apply (subst (asm) unfold_binary_width_add) by blast
  from addv obtain zv where zv: "[m, p] \<turnstile> z \<mapsto> IntVal b zv"
    apply (subst (asm) unfold_binary_width_add) by blast
  from val obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
    apply (subst (asm) unfold_binary_width_and) by blast
  have addv: "[m, p] \<turnstile> exp[z + y] \<mapsto> new_int b (zv + yv)"
    using zv yv evaltree.BinaryExpr by auto
  have lhs: "[m, p] \<turnstile> exp[(z + y) & x] \<mapsto> new_int b (and (zv + yv) xv)"
    using addv xv apply (rule evaltree.BinaryExpr) by simp+
  have rhs: "[m, p] \<turnstile> exp[z & x] \<mapsto> new_int b (and zv xv)"
    using xv zv evaltree.BinaryExpr by auto
  then show ?thesis
  proof (cases "numberOfLeadingZeros (\<up>x) > 0")
    case True
    have n_bounds: "0 \<le> n \<and> n < 64"
      by (simp add: True n)
    have "and (zv + yv) xv = and ((zv + yv) mod 2^n) xv"
      using L1 n xv by blast
    also have "... = and ((zv + (yv mod 2^n)) mod 2^n) xv"
      by (metis take_bit_0 take_bit_eq_mod zero_less_iff_neq_zero mod_dist_over_add_right n_bounds)
    also have "... = and (((zv mod 2^n) + (yv mod 2^n)) mod 2^n) xv"
      by (metis ValueThms.mod_dist_over_add n_bounds take_bit_0 take_bit_eq_mod zero_less_iff_neq_zero)
    also have "... = and ((zv mod 2^n) mod 2^n) xv"
      using L2 n xv yv assms by auto
    also have "... = and (zv mod 2^n) xv"
      by (smt (verit, best) and.idem take_bit_eq_mask take_bit_eq_mod word_bw_assocs(1) 
          mod_mod_trivial)
    also have "... = and zv xv"
      by (metis L1 n xv)
    finally show ?thesis
      by (metis evalDet eval lhs rhs)
  next
    case False
    then have "numberOfLeadingZeros (\<up>x) = 0"
      by simp
    then have "numberOfTrailingZeros (\<up>y) \<ge> 64"
      using assms by fastforce 
    then have "yv = 0"
      by (metis L2 ValueThms.size64 \<open>numberOfLeadingZeros (\<up> x) = 0\<close> assms diff_zero take_bit_eq_mod take_bit_length_eq wsst_TYs(3) xv yv)
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

lemma noZeros_Count:
  fixes a :: "64 word"
  assumes "zeroCount a = 0"
  shows "i < Nat.size a \<longrightarrow> bit a i"
  using assms unfolding zeroCount_def size64
  using zeroCount_finite by auto

lemma allZeros_Count_imp:
  fixes a :: "64 word"
  assumes "zeroCount a = 64"
  shows "i < Nat.size a \<longrightarrow> \<not>(bit a i)"
  using assms unfolding zeroCount_def
  by (smt (verit) ValueThms.size64 assms bitCount_def bitCount_range card_0_eq diff_diff_cancel empty_iff finite_bit_word intersect_bitCount mem_Collect_eq rel_simps(27) verit_minus_simplify(2) zeroCount_def)

lemma allZeros_Count:
  fixes a :: "64 word"
  assumes "zeroCount a = 64"
  shows "\<not>(bit a i)"
  using assms allZeros_Count_imp max_bit by blast

lemma zeroBits:
  fixes a :: "'a::len word"
  shows "(\<forall>i. \<not>(bit a i)) \<longleftrightarrow> a = 0"
  apply auto
  by (simp add: bit_word_eqI)

lemma mask_bit_iff:
  fixes a :: "'a::len word"
  assumes "n \<le> Nat.size a"
  shows "a = mask n \<Longrightarrow> bit a i \<longleftrightarrow> i < n"
  apply auto
  using Word.bit_mask_iff
   apply auto[1] using assms
  by (simp add: Word.bit_mask_iff wsst_TYs(3))

lemma maskBitCount:
  fixes a :: "'a::len word"
  assumes "n \<le> Nat.size a"
  shows "a = mask n \<Longrightarrow> card {i. bit a i} = n"
  using mask_bit_iff assms
  by fastforce

(*
lemma packedMask:
  fixes a :: "64 word"
  assumes "numberOfLeadingZeros a = zeroCount a"
  shows "a = mask (64 - numberOfLeadingZeros a)"
  using assms
proof (induction "64 - numberOfLeadingZeros a")
  case 0
  have "numberOfLeadingZeros a = 64"
    by (metis "0.hyps" local.numberOfLeadingZeros_range nat_less_le size64 zero_less_diff)
  then have "zeroCount a = 64"
    using assms by fastforce
  then have "a = 0"
    using allZeros_Count zeroBits by blast
  then show ?case
    by (simp add: "0.hyps")
next
  case (Suc x)
  then have "numberOfLeadingZeros a = 64 - Suc x"
    by (metis add_diff_cancel_right' add_diff_inverse_nat less_numeral_extra(3) nat_diff_split zero_less_Suc)
  then have "zeroCount a = 64 - Suc x"
    using assms by presburger
  from Suc show ?case sorry
qed
(*
proof (induction a)
  case zero
  then show ?case
    by (simp add: MaxOrNeg_neg highestOneBit_def numberOfLeadingZeros_def size64)
next
  case (suc a)
  then show ?case unfolding MaxOrNeg_neg highestOneBit_def numberOfLeadingZeros_def zeroCount_def
    using size64 apply auto sorry
qed
*)

lemma zerosAboveOnly:
  fixes a :: "64 word"
  assumes "numberOfLeadingZeros a = zeroCount a"
  shows "\<not>(bit a i) \<longrightarrow> i \<ge> (64 - numberOfLeadingZeros a)"
proof -
  obtain n where n: "n = 64 - numberOfLeadingZeros a"
    by simp
  then have n_range: "n \<le> Nat.size a"
    using size64
    by presburger
  then have "a = (mask n)"
    using packedMask
    using assms n by blast
  then have "\<not> bit a i \<longrightarrow> i \<ge> n"
    using Word.bit_mask_iff
    by (metis (mono_tags) le_antisym linorder_le_less_linear min_def n_range word_size)
  then show ?thesis using n
    by blast
qed



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
    using assms(1) sorry
    (*using \<open>(n::nat) = (64::nat) - numberOfLeadingZeros (\<up> (z::IRExpr))\<close> by blast*)
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
*)

end

lemma
  shows "stampConditions ((Expr u)..stamp()) ((Stamp (stamp_expr u)))"
  using stamp_Method by blast

lemma down_mask_wf_stamp:
  assumes "wf_stamp x"
  assumes "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
  shows "and (not xv) (stpi_down (stamp_expr x)) = 0"
  using assms unfolding wf_stamp_def using valid_value.simps(1)
  using valid_int_gives by fastforce

lemma up_mask_wf_stamp:
  assumes "wf_stamp x"
  assumes "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
  shows "and xv (stpi_up (stamp_expr x)) = xv"
  using assms unfolding wf_stamp_def using valid_value.simps(1)
  using valid_int_gives by fastforce

(*
lemma stamp_upMask_eq:
  assumes "evalCondition cond[(((Expr u)..stamp()..upMask()) & ((Expr v)..stamp()..upMask())) eq (const 0)]" (is "evalCondition cond[?lhs eq ?rhs]")
  shows "and (stpi_upper (stamp_expr x)) (stpi_upper (stamp_expr y)) = 0"
proof -
  obtain res where resdef: "stampConditions cond[?lhs eq ?rhs] (Value res)"
    using assms evalCondition_def
    by (metis cond_Binary)
  obtain xv where xvdef: "stampConditions ?lhs (Value xv)"
    using assms by (meson BinaryCool evalCondition_def)
  obtain yv where yvdef: "stampConditions ?rhs (Value yv)"
    using assms by (meson BinaryCool evalCondition_def)
  have "res = intval_equals xv yv"
    using assms
    by (smt (verit) Condition.inject(4) bin_eval.simps(13) cond_Binary resdef stampConditions_det xvdef yvdef)
  also have "res = IntVal 32 1"
    using calculation resdef
    by (smt (verit, ccfv_threshold) assms coerce_to_bool.intros(1) coerce_to_bool_det evalCondition_def intval_equals_result stampConditions_det val_to_bool.simps(1) val_to_bool.simps(2))
  ultimately have "xv = yv"
    using resdef intval_equals.simps
    by (smt (verit) Value.inject(1) bool_to_val.simps(2) bool_to_val_bin.simps wf_bool.elims(2) wf_bool.elims(3) zero_neq_one)
  have "yv = IntVal 64 0"
    by (meson Condition.inject(4) cond_Const yvdef)
  obtain uv where uvdef: "stampConditions ((Expr u)..stamp()..upMask()) (Value uv)"
    by (meson cond_Binary xvdef)
  also have "stampConditions ((Stamp (stamp_expr u))..upMask()) (Value uv)"
    by (smt (verit, ccfv_threshold) cond_Method_cases(2) stampConditions.intros(13) stampConditions.intros(6) stampConditions_det stamp_Method uvdef)
  have "uv = IntVal 64 0"
    sorry
  obtain vv where vvdef: "stampConditions ((Expr v)..stamp()..upMask()) (Value vv)"
    by (meson cond_Binary xvdef)
  have "xv = intval_and uv vv"
    using xvdef uvdef vvdef
    by (smt (verit, ccfv_SIG) Condition.inject(4) bin_eval.simps(6) cond_Binary stampConditions_det)
  have "evalCondition cond[(((Stamp (stamp_expr u))..upMask()) & ((Stamp (stamp_expr v))..upMask())) eq (const 0)]"
    using assms stamp_Method sorry
  then show ?thesis sorry
qed
end
*)


locale wf_expr =
  fixes x y :: IRExpr
  assumes wf: "wf_stamp x \<and> wf_stamp y"

sublocale wf_expr \<subseteq>
  stamp_mask_singleton x y "stpi_up o stamp_expr" "stpi_down o stamp_expr"
  apply standard using wf down_mask_wf_stamp defer
  apply auto[1]
  by (metis (no_types, opaque_lifting) and_zero_eq insertE local.wf o_def singletonD up_mask_wf_stamp word_and_not word_bw_assocs(1))


definition UpMaskCancels where
  "UpMaskCancels x y = (and ((stpi_up o stamp_expr) x) ((stpi_up o stamp_expr) y) = 0)"

lemma (in wf_expr) RedundantLHSYOr:
  assumes "UpMaskCancels y x"
  shows "exp[((z | y) & x)] \<ge> exp[(z & x)]"
  using assms UpMaskCancels_def exp_eliminate_y
  by blast

lemma (in wf_expr) RedundantLHSXOr:
  assumes "UpMaskCancels x y"
  shows "exp[((x | z) & y)] \<ge> exp[z & y]"
  using assms
  by (meson basic_trans_rules(23) equal_refines exp_or_commute local.wf mono_binary wf_expr.RedundantLHSYOr wf_expr.intro)

phase NewAnd
  terminating size
begin


optimization RedundantLHSYOr:
  when "wf_stamp x \<and> wf_stamp y \<and> wf_stamp z"
  when "UpMaskCancels y z"
  "((x | y) & z) \<longmapsto> (x & z)"
  apply (cases z; auto)
  apply (simp add: size_binary_lhs)+
   using wf_expr.RedundantLHSYOr by (meson le_expr_def wf_expr.intro)

optimization RedundantLHSXOr:
  when "wf_stamp x \<and> wf_stamp y \<and> wf_stamp z"
  when "UpMaskCancels x z"
  "((x | y) & z) \<longmapsto> y & z"
  apply (cases z; auto)
          apply (simp add: size_binary_rhs)+
  by (meson le_expr_def wf_expr.RedundantLHSXOr wf_expr.intro)

optimization RedundantRHSYOr: 
  when "wf_stamp x \<and> wf_stamp y \<and> wf_stamp z"
  when "UpMaskCancels y z"
  "(z & (x | y)) \<longmapsto> z & x"
   apply (cases z; cases x; cases y; auto)
  apply (simp add: size_binary_rhs size_binary_lhs)+
  by (metis exp_and_commute le_expr_def wf_expr.RedundantLHSYOr wf_expr.intro)

optimization RedundantRHSXOr: 
  when "wf_stamp x \<and> wf_stamp y \<and> wf_stamp z"
  when "UpMaskCancels x z"
  "(z & (x | y)) \<longmapsto> z & y"
  apply (cases z; cases x; cases y; auto)
  apply (simp add: size_binary_rhs size_binary_lhs)+
  by (meson exp_and_commute le_expr_def wf_expr.RedundantLHSXOr wf_expr.intro)

thm_oracles RedundantLHSYOr RedundantLHSXOr RedundantRHSYOr RedundantRHSXOr
(*
optimization redundant_lhs_add: "((x + y) & z) \<longmapsto> x & z
                               when ((and (IRExpr_up y) (IRExpr_down z)) = 0)"
*)

(*
value "
  (optimized_export
    ((RedundantLHSYOr_code else
      RedundantLHSXOr_code) else
      (RedundantRHSYOr_code else
      RedundantRHSXOr_code)
    ))"
*)

end

end