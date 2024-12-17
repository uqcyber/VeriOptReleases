section \<open>java.lang.Long\<close>

text \<open>
Utility functions from the Java Long class that Graal occasionally makes use of.
\<close>

theory JavaLong
  imports JavaWords
          "HOL-Library.FSet"
begin

lemma negative_all_set_32:
  "n < 32 \<Longrightarrow> bit (-1::int32) n"
  apply transfer by auto

(* TODO: better handle empty *)
definition MaxOrNeg :: "nat set \<Rightarrow> int" where
  "MaxOrNeg s = (if s = {} then -1 else Max s)"

definition MinOrHighest :: "nat set \<Rightarrow> nat \<Rightarrow> nat" where
  "MinOrHighest s m = (if s = {} then m else Min s)"

lemma MaxOrNegEmpty:
  "MaxOrNeg s = -1 \<longleftrightarrow> s = {}"
  unfolding MaxOrNeg_def by auto


subsection Long.highestOneBit

(* This is a different definition to Long.highestOneBit *)
definition highestOneBit :: "('a::len) word \<Rightarrow> int" where
  "highestOneBit v = MaxOrNeg {n. bit v n}"

lemma highestOneBitInvar:
  "highestOneBit v = j \<Longrightarrow> (\<forall>i::nat. (int i > j \<longrightarrow> \<not> (bit v i)))"
  apply (induction "size v"; auto) unfolding highestOneBit_def
  by (metis linorder_not_less MaxOrNeg_def empty_iff finite_bit_word mem_Collect_eq of_nat_mono
      Max_ge)

lemma highestOneBitNeg:
  "highestOneBit v = -1 \<longleftrightarrow> v = 0"
  unfolding highestOneBit_def MaxOrNeg_def
  by (metis Collect_empty_eq_bot bit_0_eq bit_word_eqI int_ops(2) negative_eq_positive one_neq_zero)

lemma higherBitsFalse:
  fixes v :: "'a :: len word"
  shows "i > size v \<Longrightarrow> \<not> (bit v i)"
  by (simp add: bit_word.rep_eq size_word.rep_eq)

lemma highestOneBitN:
  assumes "bit v n"
  assumes "\<forall>i::nat. (int i > n \<longrightarrow> \<not> (bit v i))"
  shows "highestOneBit v = n"
  unfolding highestOneBit_def MaxOrNeg_def
  by (metis Max_ge Max_in all_not_in_conv assms(1) assms(2) finite_bit_word mem_Collect_eq of_nat_less_iff order_less_le)

lemma highestOneBitSize:
  assumes "bit v n"
  assumes "n = size v"
  shows "highestOneBit v = n"
  by (metis assms(1) assms(2) not_bit_length wsst_TYs(3))

lemma highestOneBitMax:
  "highestOneBit v < size v"
  unfolding highestOneBit_def MaxOrNeg_def
  using higherBitsFalse
  by (simp add: bit_imp_le_length size_word.rep_eq)

lemma highestOneBitAtLeast:
  assumes "bit v n"
  shows "highestOneBit v \<ge> n"
proof (induction "size v")
  case 0
  then show ?case by simp
next
  case (Suc x)
  then have "\<forall>i. bit v i \<longrightarrow> i < Suc x"
    by (simp add: bit_imp_le_length wsst_TYs(3))
  then show ?case
    unfolding highestOneBit_def MaxOrNeg_def
    using assms by auto
qed

lemma highestOneBitElim:
  "highestOneBit v = n
     \<Longrightarrow> ((n = -1 \<and> v = 0) \<or> (n \<ge> 0 \<and> bit v n))"
  unfolding highestOneBit_def MaxOrNeg_def
  by (metis Max_in finite_bit_word le0 le_minus_one_simps(3) mem_Collect_eq of_nat_0_le_iff of_nat_eq_iff)


text \<open>A recursive implementation of highestOneBit that is suitable for code generation.\<close>

fun highestOneBitRec :: "nat \<Rightarrow> ('a::len) word \<Rightarrow> int" where
  "highestOneBitRec n v =
    (if bit v n then n 
     else if n = 0 then -1
     else highestOneBitRec (n - 1) v)"

lemma highestOneBitRecTrue:
  "highestOneBitRec n v = j \<Longrightarrow> j \<ge> 0 \<Longrightarrow> bit v j"
proof (induction "n")
  case 0
  then show ?case
    by (metis diff_0 highestOneBitRec.simps leD of_nat_0_eq_iff of_nat_0_le_iff zle_diff1_eq) 
next
  case (Suc n)
  then show ?case
    by (metis diff_Suc_1 highestOneBitRec.elims nat.discI nat_int) 
qed

lemma highestOneBitRecN:
  assumes "bit v n"
  shows "highestOneBitRec n v = n"
  by (simp add: assms)

lemma highestOneBitRecMax:
  "highestOneBitRec n v \<le> n"
  by (induction n; simp)

lemma highestOneBitRecElim:
  assumes "highestOneBitRec n v = j"
  shows "((j = -1 \<and> v = 0) \<or> (j \<ge> 0 \<and> bit v j))"
  using assms highestOneBitRecTrue by blast

lemma highestOneBitRecZero:
  "v = 0 \<Longrightarrow> highestOneBitRec (size v) v = -1"
  by (induction rule: "highestOneBitRec.induct"; simp)

lemma highestOneBitRecLess:
  assumes "\<not> bit v n"
  shows "highestOneBitRec n v = highestOneBitRec (n - 1) v"
  using assms by force


text \<open>Some lemmas that use masks to restrict highestOneBit
  and relate it to highestOneBitRec.\<close>

lemma highestOneBitMask:
  assumes "size v = n"
  shows "highestOneBit v = highestOneBit (and v (mask n))"
  by (metis assms dual_order.refl lt2p_lem mask_eq_iff size_word.rep_eq)

lemma maskSmaller:
  fixes v :: "'a :: len word"
  assumes "\<not> bit v n"
  shows "and v (mask (Suc n)) = and v (mask n)" 
  unfolding bit_eq_iff
  by (metis assms bit_and_iff bit_mask_iff less_Suc_eq) 

lemma highestOneBitSmaller:
  assumes "size v = Suc n"
  assumes "\<not> bit v n"
  shows "highestOneBit v = highestOneBit (and v (mask n))"
  by (metis assms highestOneBitMask maskSmaller)

lemma highestOneBitRecMask:
  shows "highestOneBit (and v (mask (Suc n))) = highestOneBitRec n v"
proof (induction n)
  case 0
  then have "highestOneBit (and v (mask (Suc 0))) = highestOneBitRec 0 v"
    apply auto
    apply (smt (verit, ccfv_threshold) neg_equal_zero negative_eq_positive bit_1_iff bit_and_iff
           highestOneBitN)
    by (simp add: bit_iff_and_push_bit_not_eq_0 highestOneBitNeg)
  then show ?case
    by presburger
next
  case (Suc n)
  then show ?case 
  proof (cases "bit v (Suc n)")
    case True
    have 1: "highestOneBitRec (Suc n) v = Suc n"
      by (simp add: True)
    have "\<forall>i::nat. (int i > (Suc n) \<longrightarrow> \<not> (bit (and v (mask (Suc (Suc n)))) i))"
      by (simp add: bit_and_iff bit_mask_iff)
    then have 2: "highestOneBit (and v (mask (Suc (Suc n)))) = Suc n"
      using True highestOneBitN
      by (metis bit_take_bit_iff lessI take_bit_eq_mask) 
    then show ?thesis 
      using 1 2 by auto
  next
    case False
    then show ?thesis
      by (simp add: Suc maskSmaller) 
  qed
qed


text \<open>Finally - we can use the mask lemmas to relate highestOneBitRec to its spec.\<close>

lemma highestOneBitImpl[code]:
  "highestOneBit v = highestOneBitRec (size v) v"
  by (metis highestOneBitMask highestOneBitRecMask maskSmaller not_bit_length wsst_TYs(3))

lemma "highestOneBit (0x5 :: int8) = 2" by code_simp

subsection \<open>Long.lowestOneBit\<close>

definition lowestOneBit :: "('a::len) word \<Rightarrow> nat" where
  "lowestOneBit v = MinOrHighest {n . bit v n} (size v)"

lemma max_bit: "bit (v::('a::len) word) n \<Longrightarrow> n < size v"
  by (simp add: bit_imp_le_length size_word.rep_eq)

lemma max_set_bit: "MaxOrNeg {n . bit (v::('a::len) word) n} < Nat.size v"
  using max_bit unfolding MaxOrNeg_def
  by force

subsection \<open>Long.numberOfLeadingZeros\<close>

definition numberOfLeadingZeros :: "('a::len) word \<Rightarrow> nat" where
  "numberOfLeadingZeros v = nat (Nat.size v - highestOneBit v - 1)"

lemma MaxOrNeg_neg: "MaxOrNeg {} = -1"
  by (simp add: MaxOrNeg_def)

lemma MaxOrNeg_max: "s \<noteq> {} \<Longrightarrow> MaxOrNeg s = Max s"
  by (simp add: MaxOrNeg_def)

lemma zero_no_bits:
  "{n . bit 0 n} = {}"
  by simp

lemma "highestOneBit (0::64 word) = -1"
  by (simp add: MaxOrNeg_neg highestOneBit_def)

lemma "numberOfLeadingZeros (0::64 word) = 64"
  unfolding numberOfLeadingZeros_def by (simp add: highestOneBitImpl size64)

lemma highestOneBit_top: "Max {highestOneBit (v::64 word)} < 64"
  unfolding highestOneBit_def
  by (metis Max_singleton int_eq_iff_numeral max_set_bit size64)

lemma numberOfLeadingZeros_top: "Max {numberOfLeadingZeros (v::64 word)} \<le> 64"
  unfolding numberOfLeadingZeros_def
  using size64
  by (simp add: MaxOrNeg_def highestOneBit_def nat_le_iff)

lemma numberOfLeadingZeros_range: "0 \<le> numberOfLeadingZeros a \<and> numberOfLeadingZeros a \<le> Nat.size a"
  unfolding numberOfLeadingZeros_def apply auto
  apply (induction "highestOneBit a") apply (simp add: numberOfLeadingZeros_def)
  by (metis (mono_tags, opaque_lifting) leD negative_zless  int_eq_iff diff_right_commute diff_self
      diff_zero nat_le_iff le_iff_diff_le_0  minus_diff_eq nat_0_le nat_le_linear of_nat_0_le_iff
      MaxOrNeg_def highestOneBit_def)

lemma leadingZerosAddHighestOne: "numberOfLeadingZeros v + highestOneBit v = Nat.size v - 1"
  unfolding numberOfLeadingZeros_def highestOneBit_def
  using MaxOrNeg_def int_nat_eq int_ops(6) max_bit order_less_irrefl by fastforce

subsection \<open>Long.numberOfTrailingZeros\<close>

definition numberOfTrailingZeros :: "('a::len) word \<Rightarrow> nat" where
  "numberOfTrailingZeros v = lowestOneBit v"

lemma lowestOneBit_bot: "lowestOneBit (0::64 word) = 64"
  unfolding lowestOneBit_def MinOrHighest_def
  by (simp add: size64)

lemma bit_zero_set_in_top: "bit (-1::'a::len word) 0"
  by auto

lemma nat_bot_set: "(0::nat) \<in> xs \<longrightarrow> (\<forall>x \<in> xs . 0 \<le> x)"
  by fastforce

lemma "numberOfTrailingZeros (0::64 word) = 64"
  unfolding numberOfTrailingZeros_def
  using lowestOneBit_bot by simp

subsection \<open>Long.reverseBytes\<close>

(* Recursive version of reverseBytes for code generation *)
fun reverseBytes_fun :: "('a::len) word \<Rightarrow> nat \<Rightarrow> ('a::len) word \<Rightarrow> ('a::len) word" where
  "reverseBytes_fun v b flip = (if (b = 0) then (flip) else
                       (reverseBytes_fun (v >>[b] 8) (b - 8) (or (flip << 8) (take_bit 8 v))))"

subsection \<open>Long.bitCount\<close>

definition bitCount :: "('a::len) word \<Rightarrow> nat" where
  "bitCount v = card {n . bit v n}"

(* Recursive version of bitCount for code generation *)
fun bitCount_fun :: "('a::len) word \<Rightarrow> nat \<Rightarrow> nat" where
  "bitCount_fun v n = (if (n = 0) then
                          (if (bit v n) then 1 else 0) else
                       if (bit v n) then (1 + bitCount_fun (v) (n - 1))
                                    else (0 + bitCount_fun (v) (n - 1)))"

lemma "bitCount 0 = 0"
  unfolding bitCount_def
  by (metis card.empty zero_no_bits)

subsection \<open>Long.zeroCount\<close>

definition zeroCount :: "('a::len) word \<Rightarrow> nat" where
  "zeroCount v = card {n. n < Nat.size v \<and> \<not>(bit v n)}"

lemma zeroCount_finite: "finite {n. n < Nat.size v \<and> \<not>(bit v n)}"
  using finite_nat_set_iff_bounded by blast

lemma negone_set:
  "bit (-1::('a::len) word) n \<longleftrightarrow> n < LENGTH('a)"
  by simp

lemma negone_all_bits:
  "{n . bit (-1::('a::len) word) n} = {n . 0 \<le> n \<and> n < LENGTH('a)}"
  using negone_set
  by auto

lemma bitCount_finite:
  "finite {n . bit (v::('a::len) word) n}"
  by simp

lemma card_of_range:
  "x = card {n . 0 \<le> n \<and> n < x}"
  by simp

lemma range_of_nat:
  "{(n::nat) . 0 \<le> n \<and> n < x} = {n . n < x}"
  by simp

lemma finite_range:
  "finite {n::nat . n < x}"
  by simp


lemma range_eq:
  fixes x y :: nat
  shows "card {y..<x} = card {y<..x}"
  using card_atLeastLessThan card_greaterThanAtMost by presburger

lemma card_of_range_bound:
  fixes x y :: nat
  assumes "x > y"
  shows "x - y = card {n . y < n \<and> n \<le> x}"
proof -
  have finite: "finite {n . y \<le> n \<and> n < x}"
    by auto
  have nonempty: "{n . y \<le> n \<and> n < x} \<noteq> {}"
    using assms by blast
  have simprep: "{n . y < n \<and> n \<le> x} = {y<..x}"
    by auto
  have "x - y = card {y<..x}"
    by auto
  then show ?thesis
    unfolding simprep by blast
qed

lemma "bitCount (-1::('a::len) word) = LENGTH('a)"
  unfolding bitCount_def using card_of_range
  by (metis (no_types, lifting) Collect_cong negone_all_bits)

lemma bitCount_range:
  fixes n :: "('a::len) word"
  shows "0 \<le> bitCount n \<and> bitCount n \<le> Nat.size n"
  unfolding bitCount_def
  by (metis atLeastLessThan_iff bot_nat_0.extremum max_bit mem_Collect_eq subsetI subset_eq_atLeast0_lessThan_card)

lemma zerosAboveHighestOne:
  "n > highestOneBit a \<Longrightarrow> \<not>(bit a n)"
  unfolding highestOneBit_def MaxOrNeg_def
  by (metis (mono_tags, opaque_lifting) Collect_empty_eq Max_ge finite_bit_word less_le_not_le mem_Collect_eq of_nat_le_iff)

lemma zerosBelowLowestOne:
  assumes "n < lowestOneBit a"
  shows "\<not>(bit a n)"
proof (cases "{i. bit a i} = {}")
  case True
  then show ?thesis by simp
next
  case False
  have "n < Min (Collect (bit a)) \<Longrightarrow> \<not> bit a n"
    using False by auto
  then show ?thesis
    by (metis False MinOrHighest_def assms lowestOneBit_def)
qed

lemma union_bit_sets:
  fixes a :: "('a::len) word"
  shows "{n . n < Nat.size a \<and> bit a n} \<union> {n . n < Nat.size a \<and> \<not>(bit a n)} = {n . n < Nat.size a}"
  by fastforce

lemma disjoint_bit_sets:
  fixes a :: "('a::len) word"
  shows "{n . n < Nat.size a \<and> bit a n} \<inter> {n . n < Nat.size a \<and> \<not>(bit a n)} = {}"
  by blast

lemma qualified_bitCount:
  "bitCount v = card {n . n < Nat.size v \<and> bit v n}"
  by (metis (no_types, lifting) Collect_cong bitCount_def max_bit)

lemma card_eq:
  assumes "finite x \<and> finite y \<and> finite z"
  assumes "x \<union> y = z"
  assumes "y \<inter> x = {}"
  shows "card z - card y = card x"
  using assms add_diff_cancel_right' card_Un_disjoint
  by (metis inf.commute)

lemma card_add:
  assumes "finite x \<and> finite y \<and> finite z"
  assumes "x \<union> y = z"
  assumes "y \<inter> x = {}"
  shows "card x + card y = card z"
  using assms card_Un_disjoint
  by (metis inf.commute)


lemma card_add_inverses:
  assumes "finite {n. Q n \<and> \<not>(P n)} \<and> finite {n. Q n \<and> P n} \<and> finite {n. Q n}"
  shows "card {n. Q n \<and> P n} + card {n. Q n \<and> \<not>(P n)} = card {n. Q n}"
  apply (rule card_add)
  using assms apply simp
  apply auto[1]
  by auto

lemma ones_zero_sum_to_width:
  "bitCount a + zeroCount a = Nat.size a"
proof -
  have add_cards: "card {n. (\<lambda>n. n < size a) n \<and> (bit a n)} + card {n. (\<lambda>n. n < size a) n \<and> \<not>(bit a n)} = card {n. (\<lambda>n. n < size a) n}"
    apply (rule card_add_inverses) by simp
  then have "... = Nat.size a"
    by auto
 then show ?thesis 
    unfolding bitCount_def zeroCount_def using max_bit
    by (metis (mono_tags, lifting) Collect_cong add_cards)
qed

lemma intersect_bitCount_helper:
  "card {n . n < Nat.size a} - bitCount a = card {n . n < Nat.size a \<and> \<not>(bit a n)}"
proof -
  have size_def: "Nat.size a = card {n . n < Nat.size a}"
    using card_of_range by simp
  have bitCount_def: "bitCount a = card {n . n < Nat.size a \<and> bit a n}"
    using qualified_bitCount by auto
  have disjoint: "{n . n < Nat.size a \<and> bit a n} \<inter> {n . n < Nat.size a \<and> \<not>(bit a n)} = {}"
    using disjoint_bit_sets by auto
  have union: "{n . n < Nat.size a \<and> bit a n} \<union> {n . n < Nat.size a \<and> \<not>(bit a n)} = {n . n < Nat.size a}"
    using union_bit_sets by auto
  show ?thesis
    unfolding bitCount_def
    apply (rule card_eq)
    using finite_range apply simp
    using union apply blast
    using disjoint by simp
qed

lemma intersect_bitCount:
  "Nat.size a - bitCount a = card {n . n < Nat.size a \<and> \<not>(bit a n)}"
  using card_of_range intersect_bitCount_helper by auto

hide_fact intersect_bitCount_helper

end

