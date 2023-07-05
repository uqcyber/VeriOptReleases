section \<open>Integer Stamp Functions from GraalVM Java Code\<close>

text \<open>
This theory corresponds as closely as possible to IntegerStamp.java
in the GraalVM source code.

An IntegerStamp defines the number of bits in an integer value,
the allowable min-max range of that value,
and additional range information in the form of bit masks.
Each IntegerStamp has an up mask and a down mask,
corresponding to a the bits that may be set and the bits that must be set.

Examples:
  A stamp where no range information is known will have;
    an up mask of -1 as all bits may be set, and
    a down mask of 0 as no bits must be set.

  A stamp known to be one should have;
    an up mask of 1 as only the first bit may be set, no others, and
    a down mask of 1 as the first bit must be set and no others.

NOTE 1: like the Java, we use int64 for the min-max ranges.
So any large unsigned range with upper bound above
$2^63-1$ is converted into the universal range: $(- 2^63, 2^63 - 1)$.

NOTE 2: we do not yet model the canBeZero flag.
\<close>

theory JavaIntegerStamp
  imports JavaLong
begin

context
  includes bit_operations_syntax
begin


subsection \<open>The bit-subset relationship between values or masks\<close>

text \<open>The Java code often has 'm2 & ~m1 == 0' to check that word w1 is a subset (or equal) of w2.
  To improve readability, we define this pattern as the following infix abbreviation.
\<close>  
definition word_subseteq :: "'a :: len word \<Rightarrow> 'a :: len word \<Rightarrow> bool" (infix "\<subseteq>w" 70) where
  "word_subseteq w1 w2 \<equiv> (w1 AND NOT w2 = 0)"

lemma word_subseteq_implies:
  assumes "m1 \<subseteq>w m2"
  assumes "bit m1 b"
  shows "bit m2 b"
  by (metis assms word_subseteq_def bit_and_iff bit_int_code(1) bit_not_iff impossible_bit bit_0_eq)

lemma word_subseteq_implies_rev:
  assumes "word_subseteq m1 m2"
  assumes "\<not> bit m2 b"
  shows "\<not> bit m1 b"
  using assms word_subseteq_implies by blast

lemma word_subseteq_transitive:
  "m1 \<subseteq>w m2 \<Longrightarrow> m2 \<subseteq>w m3 \<Longrightarrow> m1 \<subseteq>w m3"
  unfolding word_subseteq_def by (rule bit_word_eqI; metis bit_and_iff bit_not_iff)

lemma word_subseteq_antisym:
  "a \<subseteq>w b \<Longrightarrow> b \<subseteq>w a \<Longrightarrow> a = b"
  by (rule bit_word_eqI; auto simp: word_subseteq_implies)

definition word_subset :: "'a :: len word \<Rightarrow> 'a :: len word \<Rightarrow> bool" (infix "\<subset>w" 70) where
  "word_subset w1 w2 \<equiv> (word_subseteq w1 w2 \<and> w1 \<noteq> w2)"

interpretation word_subset_order: ordering \<open>(\<subseteq>w)\<close> \<open>(\<subset>w)\<close>
  by (smt (verit, best) ordering_strictI word_and_not word_subseteq_def word_subset_def
      word_subseteq_antisym word_subseteq_transitive)

text \<open>Some partial monotonicity properties.\<close>

lemma word_subseteq_mono_and:
  "m1 \<subseteq>w m2 \<Longrightarrow> (m1 AND m) \<subseteq>w (m2 AND m)"
  unfolding word_subseteq_def
  by (metis (no_types, opaque_lifting) bit.compl_zero bit.de_Morgan_conj or.commute word_oa_dist
      word_bitwise_m1_simps(2) word_bw_assocs(1) word_not_not word_or_not)

lemma word_subseteq_mono_or:
  "m1 \<subseteq>w m2 \<Longrightarrow> (m1 OR m) \<subseteq>w (m2 OR m)"
  unfolding word_subseteq_def
  by (metis (no_types, lifting) bit.conj_disj_distrib2 bit.de_Morgan_disj word_and_not
      word_ao_absorbs(6) word_bw_lcs(1))

lemma word_subseteq_antimono_not:
  "NOT m1 \<subseteq>w NOT m2 \<Longrightarrow> m2 \<subseteq>w m1"
  unfolding word_subseteq_def by (simp add: and.commute)

lemma word_subseteq_ge:
  assumes "m1 \<subseteq>w m2"
  shows "m1 \<le> m2"
  by (metis assms disjunctive_diff word_subseteq_implies_rev uint_minus_simple_alt word_and_le2
      uint_minus_simple_iff)

subsection \<open>Java Integer Stamps and Invariants\<close>

text \<open>These Stamp values simulate the Java IntegerStamp class closely.\<close>

datatype JavaIntegerStamp = 
  JIS
    (jis_bits: nat)
    (jis_lowerBound: int64)
    (jis_upperBound: int64)
    (jis_downMask: int64)
    (jis_upMask: int64)

text \<open>These stamp invariants are from the IntegerStamp.java constructor,
  plus we add the check that $0 < bits <= 64$.
  TODO: add canBeZero and its invariant.
\<close>
fun JIS_valid :: "JavaIntegerStamp \<Rightarrow> bool" where
  "JIS_valid (JIS bits lo hi downMask upMask) =
    (0 < bits \<and> bits \<le> 64 \<and>
     int_signed_value bits lo \<ge> fst (bit_bounds bits) \<and>
     int_signed_value bits hi \<le> snd (bit_bounds bits) \<and>
     downMask AND mask bits = downMask \<and>
     upMask AND mask bits = upMask \<and>
     (downMask \<subseteq>w upMask \<or> (upMask = 0 \<and> downMask = mask bits)))"

fun isEmpty :: "JavaIntegerStamp \<Rightarrow> bool" where
  "isEmpty (JIS bits lo hi downMask upMask) =
    (hi <s lo \<or>
     \<not> (downMask \<subseteq>w upMask) \<or>
     (upMask = 0 \<and> (0 <s lo \<or> hi <s 0)))"

subsection \<open>Significant bit\<close>

text \<open>Returns the most significant bit of a given width, as either 0 or 1.\<close>
definition significantBit :: "nat \<Rightarrow> int64 \<Rightarrow> int64" where
  "significantBit bits value = ((value >>> (bits - 1)) AND 1)"

corollary "significantBit 8 0x80 = 1" by code_simp

lemma significantBitValue:
  "significantBit bits value = (if bit value (bits - 1) then 1 else 0)"
  by (simp add: and_one_eq bit_word_iff_drop_bit_and shiftr_def significantBit_def)

lemma significantBitFalse[simp]:
  "(significantBit bits value = 0) = (\<not> bit value (bits - (Suc 0)))"
  using significantBitValue significantBit_def by force

lemma significantBitTrue[simp]:
  "(significantBit bits value = 1) = (bit value (bits - (Suc 0)))"
  using significantBitValue significantBit_def by force

lemma word_subseteq_pos64_ge_signed:
  fixes m1 m2 :: "int64"
  assumes "m1 \<subseteq>w m2"
  assumes "significantBit 64 m2 = 0"
  shows "m1 \<le>s m2"
proof -
  have 3: "m1 AND NOT m2 = 0"
    using assms(1) word_subseteq_def by auto
  have 4: "0 \<le> sint m2"
    by (metis assms(2) bit_unsigned_iff signed_take_bit_nonnegative_iff significantBitFalse
        sint_uint size64 wsst_TYs(3))
  have "significantBit 64 m1 = 0"
    using assms word_subseteq_implies significantBitValue by fastforce
  then have "0 \<le> sint m1"
    by (metis bit_unsigned_iff signed_take_bit_nonnegative_iff significantBitFalse sint_uint size64
        wsst_TYs(3))
  then show ?thesis
    by (metis (no_types, opaque_lifting) 3 4 AND_upper2 bit.conj_disj_distrib or.right_neutral
        signed_and_eq word_and_max word_or_not word_sle_eq)
qed

lemma word_subseteq_neg64_ge_signed:
  fixes m1 m2 :: "int64"
  assumes "m1 \<subseteq>w m2"
  assumes "significantBit 64 m1 = 1"
  shows "m1 \<le>s m2"
proof -
  have 3: "m1 AND NOT m2 = 0"
    using assms(1) word_subseteq_def by auto
  have 4: "sint m1 < 0"
    using assms(2) bit_last_iff significantBitValue by fastforce
  then have "sint m2 < 0"
    using assms(1) bit_last_iff word_subseteq_implies by blast
  then show ?thesis
    by (metis (no_types, lifting) 3 4 and.commute and_less_eq bit.conj_disj_distrib word_and_max
        or.right_neutral signed_and_eq word_or_not word_sle_eq)
qed

lemma pos_implies_sint_leq:
  fixes a b :: "'a :: len word"
  assumes "a \<le> b"
  assumes "0 \<le> sint a"
  assumes "0 \<le> sint b"
  shows "sint a \<le> sint b"
  by (smt (verit) One_nat_def Suc_pred' assms(1) assms(3) len_gt_0 signed_take_bit_int_eq_self
      signed_take_bit_int_less_eq sint_uint unsigned_greater_eq unsigned_less word_sle_eq
      word_less_eq_iff_unsigned)

text \<open>Now we generalise the above results for any bit size, using int_signed_value.\<close>
lemma word_subseteq_pos_ge_signed:
  fixes m1 m2 :: "int64"
  assumes "m1 \<subseteq>w m2"
  assumes "0 < bits"
  assumes "bits \<le> 64"
  assumes "significantBit bits m2 = 0"
  shows "int_signed_value bits m1 \<le> int_signed_value bits m2"
proof -
  have m1f: "\<not> bit m1 (bits - 1)"
    by (metis assms(1,4) word_subseteq_implies significantBitFalse One_nat_def)
  then have m1pos: "0 \<le> sint(signed_take_bit (bits - 1) m1)"
    by (metis Suc_le_lessD Suc_pred' assms(2,3) signed_take_bit_eq_if_positive size64 wsst_TYs(3)
        take_bit_smaller_range)
  have m2f: "\<not> bit m2 (bits - 1)"
    using assms significantBitFalse by auto
  then have m2pos: "0 \<le> sint(signed_take_bit (bits - 1) m2)"
    by (metis Suc_le_lessD Suc_pred' assms(2,3) signed_take_bit_eq_if_positive size64 wsst_TYs(3)
        take_bit_smaller_range)
  then have "signed_take_bit (bits - 1) m1 \<le> signed_take_bit (bits - 1) m2"
    by (metis assms(1) m1f m2f word_subseteq_ge signed_take_bit_eq_if_positive take_bit_eq_mask
        word_subseteq_mono_and)
  then show ?thesis
    by (metis m1pos m2pos int_signed_value.simps pos_implies_sint_leq)
qed

lemma bit_not_iff_word:
  fixes w :: "'a :: len word"
  assumes "n < LENGTH('a)"
  shows "bit (NOT w) n = (\<not> bit w n)"
  by (simp add: assms bit_not_iff)

lemma bit_subset_and_or_not:
  "((a AND m) OR (NOT m)) \<subseteq>w ((b AND m) OR (NOT m)) = ((a AND m) \<subseteq>w (b AND m))"
  apply auto
  apply (smt (verit, del_insts) and.commute and.left_commute and_zero_eq bit.de_Morgan_disj
      bit.double_compl word_ao_absorbs(7) word_subseteq_def)
  by (simp add: word_subseteq_mono_or)

lemma word_subseteq_neg_ge_signed:
  fixes m1 m2 :: "int64"
  assumes "m1 \<subseteq>w m2"
  assumes "0 < bits"
  assumes "bits \<le> 64"
  assumes "significantBit bits m1 = 1"
  shows "int_signed_value bits m1 \<le> int_signed_value bits m2"
proof -
  have 1: "of_bool (bit m1 (bits - 1)) = 1"
    using assms(4) by fastforce
  then have 2: "signed_take_bit (bits - 1) m1 = (take_bit (bits - 1) m1 OR NOT (mask (bits - 1)))"
    by (simp add: signed_take_bit_def)
  then have "int_signed_value bits m1 < 0"
    by (metis Suc_le_eq Suc_pred' assms(2,3) diff_0 dual_order.refl not_less or_negative_int_iff
        signed_or_eq sint_n1 size64 take_bit_minus_one_eq_mask take_bit_smaller_range word_or_not
        wsst_TYs(3) zle_diff1_eq int_signed_value.simps)
  then have "significantBit bits (signed_take_bit (bits - 1) m1) = 1"
    unfolding significantBitTrue
    by (metis "1" One_nat_def bit_1_0 bit_and_iff bit_not_iff bit_of_bool_iff bit_or_iff 2
        impossible_bit take_bit_eq_mask)
  then have "bits - 1 < 64"
    using assms by arith
  then have "\<not> bit (mask (bits - 1) :: int64) (64 - 1)"
    by (simp add: bit_mask_iff)
  then have "bit (NOT (mask (bits - 1) :: int64)) (64 - 1)"
    by (metis bit_not_iff_word diff_less len_gt_0 less_numeral_extra(1) size64 wsst_TYs(3))
  then have 64: "significantBit 64 (signed_take_bit (bits - 1) m1) = 1"
    by (metis One_nat_def bit_or_iff significantBitTrue 2)
  have 2: "of_bool (bit m2 (bits - 1)) = 1"
    using "1" assms(1) word_subseteq_implies by auto
  then have "signed_take_bit (bits - 1) m1 \<subseteq>w signed_take_bit (bits - 1) m2"
    unfolding signed_take_bit_def 1 2 mult_1 take_bit_eq_mask bit_subset_and_or_not
    using word_subseteq_mono_and assms(1) by blast
  then have "signed_take_bit (bits - 1) m1 \<le>s signed_take_bit (bits - 1) m2"
    using 64 word_subseteq_neg64_ge_signed by blast
  then show ?thesis
    by (simp add: word_sle_eq)
qed

(*
fun sf_contains:: "Stamp \<Rightarrow> Value \<Rightarrow> bool" where
  "sf_contains (IntegerStamp b l h d u) (IntVal64 val) = ((sint val \<ge> l) \<and> (sint val \<le> h))" |
  "sf_contains _ _ = False"

fun sf_is_positive:: "Stamp \<Rightarrow> bool" where
  "sf_is_positive (IntegerStamp b l h d u) = (l \<ge> 0) " |
  "sf_is_positive _ = False"

fun sf_is_negative:: "Stamp \<Rightarrow> bool" where
  "sf_is_negative (IntegerStamp b l h d u) = (h \<le> 0) " |
  "sf_is_negative _ = False"

fun sf_is_strictly_positive:: "Stamp \<Rightarrow> bool" where
  "sf_is_strictly_positive (IntegerStamp b l h d u) = (l > 0) " |
  "sf_is_strictly_positive _ = False"

fun sf_is_strictly_negative:: "Stamp \<Rightarrow> bool" where
  "sf_is_strictly_negative (IntegerStamp b l h d u) = (h < 0) " |
  "sf_is_strictly_negative _ = False"

fun sf_can_be_positive:: "Stamp \<Rightarrow> bool" where
  "sf_can_be_positive (IntegerStamp b l h d u) = (h > 0) " |
  "sf_can_be_positive _ = False"

fun sf_can_be_negative:: "Stamp \<Rightarrow> bool" where
  "sf_can_be_negative (IntegerStamp b l h d u) = (l < 0) " |
  "sf_can_be_negative _ = False"

fun sf_is_compatible1:: "Stamp \<Rightarrow> Stamp \<Rightarrow> bool" where 
  "sf_is_compatible1 (IntegerStamp b1 l1 h1 d1 u1) (IntegerStamp b2 l2 h2 d2 u2) = (b1 = b2)" |
  "sf_is_compatible1 _ _ = False"

fun sf_is_compatible2:: "Stamp \<Rightarrow> Value \<Rightarrow> bool" where 
  "sf_is_compatible2 this (IntVal32 val) = True" |
  "sf_is_compatible2 this (IntVal64 val) = True" |
  "sf_is_compatible2 _ _ = False"

fun sf_same_sign_bounds:: "Stamp \<Rightarrow> bool" where 
  "sf_same_sign_bounds (IntegerStamp b l h d u) = ((l < 0) = (h < 0))" |
  "sf_same_sign_bounds _ = False"




fun stamp_for_mask:: "Value \<Rightarrow> Value \<Rightarrow> Value \<Rightarrow> Stamp" where
  "stamp_for_mask (IntVal64 bits) (IntVal64 down) (IntVal64 up) = (
    let lo = (minValueForMasks (IntVal64 bits) (IntVal64 down) (IntVal64 up)) in
    let hi = (maxValueForMasks (IntVal64 bits) (IntVal64 down) (IntVal64 up)) in 
    IntegerStamp (unat bits) (val_to_int lo) (val_to_int hi))" | 
  "stamp_for_mask _ _ _ = IllegalStamp"

value "val_to_int (minValueForMasks (IntVal64 1) (IntVal64 2) (IntVal64 3))"

value " 2::int64"

value "max (42::nat) 3"
*)

value "sint ((-1 :: int8) << 2)"

subsection \<open>Calculate minimum bound from masks\<close>

text \<open>If the sign bit MUST be zero, then the value is positive and $downMask$ bits give us a
  minimum (positive) value.  
  Otherwise, the sign bit MIGHT be set, so the minimum value is $- 2^{bits-1}$
  plus all the bits (in $downMask$) that are known to be set.
  Precondition: $significantBit upMark = 0 \<longrightarrow> significantBit downMask = 1$
  Precondition: $\<forall>i. bit downMask i \<longrightarrow> i < bits$.\<close>
definition minValueForMasks:: "nat \<Rightarrow> int64 \<Rightarrow> int64 \<Rightarrow> int64" where
  "minValueForMasks bits downMask upMask = (
    if significantBit bits upMask = (0::int64)
    then downMask
    else downMask OR ((-1) << (bits - 1))
  )"

text \<open>A sanity check is that minValueForMasks is the same as $signed_take_bit$,
  at least when $upMask$ and $downMask$ agree on the sign.\<close>
lemma minValueForMasksIsSignedTakeBit:
  assumes "0 < bits"
  assumes "downMask AND (mask bits) = downMask"
  assumes "significantBit bits downMask = significantBit bits upMask"
  shows "minValueForMasks bits downMask upMask = signed_take_bit (bits - 1) downMask"
proof (cases "significantBit bits upMask = 0")
  case True
  then have "minValueForMasks bits downMask upMask = downMask"
    using minValueForMasks_def by presburger
  then show ?thesis
    by (metis (no_types, lifting) Suc_pred' True assms maskSmaller one_neq_zero take_bit_eq_mask
        signed_take_bit_eq_if_positive significantBitValue)
next
  case False
  then have "minValueForMasks bits downMask upMask = downMask OR ((-1) << (bits - 1))"
    using minValueForMasks_def by presburger
  then show ?thesis
    by (metis (no_types, lifting) False One_nat_def assms(3) push_bit_minus_one_eq_not_mask
        shiftl_def signed_take_bit_eq_if_negative significantBitFalse take_bit_eq_mask word_and_max
        word_oa_dist word_or_not)
qed

lemma less_bits_leq_unsigned:
  fixes down val :: "'a :: len word"
  assumes "down \<subseteq>w val"
  shows "down \<le> val"
  by (metis assms disjunctive_diff word_subseteq_implies word_and_le2 word_sub_le_iff)

lemma top_bit_false_if_le:
  fixes a b :: "'a :: len word"
  assumes "a \<le> b"
  assumes "\<not> bit b (LENGTH('a) - Suc 0)"
  shows "\<not> bit a (LENGTH('a) - Suc 0)"
proof (induction "LENGTH('a)")
  case 0
  then show ?case by auto
next
  case (Suc x)
  then have "uint b < 2 ^ (LENGTH('a) - (Suc 0))"
    by (smt (verit, ccfv_threshold) One_nat_def assms bit_last_iff diff_Suc_1 unsigned_less
        signed_take_bit_int_less_eq sint_uint)
  then have "uint a < 2 ^ (LENGTH('a) - (Suc 0))"
    by (smt (verit) assms(1) word_less_eq_iff_unsigned)
  then show ?case
    by (smt (verit) bit_last_iff signed_take_bit_int_eq_self sint_uint unsigned_greater_eq) 
qed

text \<open>When we have a subset relation between the bits of two words, we can show signed
  less-than-or-equal when they are both positive, or both negative.\<close>

lemma less_bits_signed_leq_pos:
  fixes down val :: "'a :: len word"
  assumes "down \<subseteq>w val"
  assumes "\<not> bit val (LENGTH('a) - Suc 0)"
  shows "down \<le>s val"
proof -
  have uval: "sint val = uint val"
    by (metis (no_types, lifting) assms(2) bintr_uint bit_unsigned_iff le_eq_less_or_eq
        signed_take_bit_eq_if_positive sint_uint uint_sint unsigned_take_bit_eq)
  have "\<not> bit down (LENGTH('a) - Suc 0)"
    using assms word_subseteq_implies by blast
  then have udown: "sint down = uint down"
    by (smt (verit, ccfv_threshold) bit_last_iff signed_take_bit_int_eq_self sint_less sint_uint
        take_bit_int_greater_self_iff uint_sint unsigned_greater_eq)
  then show ?thesis
    unfolding word_sle_eq udown uval word_less_eq_iff_unsigned[symmetric]
    using assms(1) less_bits_leq_unsigned by simp 
qed

lemma less_bits_signed_leq_neg:
  fixes down val :: "'a :: len word"
  assumes "down \<subseteq>w val"
  assumes "bit down (LENGTH('a) - Suc 0)"
  shows "down \<le>s val"
proof -
  have "bit val (LENGTH('a) - Suc 0)"
    using assms word_subseteq_implies by auto
  then show ?thesis
    unfolding word_sle_eq sint_uint signed_take_bit_eq_take_bit_minus
    using assms bit_uint_iff word_subseteq_ge word_of_int_less_eq_iff by fastforce
qed

value "of_bool False :: 1 word"
value "horner_sum of_bool 2 (map (\<lambda>x. True) [0 :: int64, 1, 0, 1]) :: int64"
value "map (bit (0x14 :: int8)) [0 ..< 8]"

(* Just an experiment with horner_sum *)
lemma to_bits_test:
  assumes "w < 2 ^ a"
  shows "(w :: nat) = of_nat (horner_sum of_bool 2 (map (bit w) [0..<a]))"
  by (simp add: assms horner_sum_bit_eq_take_bit take_bit_nat_eq_self)

lemma signed_leq_if_pos_leq:
  fixes a b :: "'a :: len word"
  assumes "a \<le> b"
  assumes "0 < LENGTH('a)"
  assumes "\<not> bit b (LENGTH('a) - Suc 0)"
  shows "a \<le>s b"
proof -
  have b: "0 \<le> sint b"
    using assms(3) bit_last_iff by fastforce
  then have "\<not> bit a (LENGTH('a) - Suc 0)"
    using assms(1,3) top_bit_false_if_le by fastforce
  then have a: "0 \<le> sint a"
    by (simp add: bit_last_iff)
  then show ?thesis
    unfolding word_sle_eq
    by (smt (verit) Suc_diff_Suc assms(1,2) b diff_zero signed_take_bit_int_eq_self sint_uint
        signed_take_bit_int_less_eq uint_add_lem unsigned_greater_eq word_le_exists')
qed

lemma neg1_shifted_is_not_mask:
  "((-1) << n) = NOT (mask n)"
  by (simp add: shiftl_def)

(* Maybe not needed, since it is just neg1_shifted_is_not_mask plus minus_exp_eq_not_mask *)
lemma neg1_shifted_is_min_value:
  "((-1 :: int64) << bits) = - (2 ^ bits)"
  by (simp add: minus_exp_eq_not_mask neg1_shifted_is_not_mask)

text \<open>This is a helper lemma for when minValueForMasks returns a negative value.
  In that case the bits above $n$ are all true, and we only need a subset
  relationship on the bits below $n$ in order to prove signed less-than-or-equal.\<close>
lemma neg_subset_leq:
  fixes a b :: int64
  assumes "0 \<le> n"
  assumes "n < 64"
  assumes "a = (((-1) << n) OR aLow)"
  assumes "aLow \<subseteq>w b"
  shows "signed_take_bit n a \<le>s signed_take_bit n b"
proof -
  have an: "bit a n"
    by (simp add: assms(2,3) bit_mask_iff bit_not_iff bit_or_iff shiftl_def)
  then have a: "signed_take_bit n a = (take_bit n a OR NOT (mask n))"
    unfolding signed_take_bit_def by simp
  then have a63: "bit (signed_take_bit n a) (64 - 1)"
    by (smt (z3) One_nat_def Suc_leI Suc_pred' assms(1,2) bit.compl_zero bit_last_iff bit_mask_iff
        bit_not_iff_eq bit_or_iff linorder_not_le order_le_less_trans sint_n1 size64 wsst_TYs(3))
  then have a0: "signed_take_bit n a \<le>s 0"
    by (metis One_nat_def bit_last_iff dual_order.strict_iff_not sint_0 size64 word_sle_eq
        wsst_TYs(3))
  then show ?thesis
  proof (cases "bit b n")
    case True
    then have b: "signed_take_bit n b = (take_bit n b OR NOT (mask n))"
      by (simp add: signed_take_bit_eq_if_negative)
    then have "signed_take_bit n a \<subseteq>w signed_take_bit n b"
      by (metis (no_types, lifting) a assms(3,4) bit.conj_cancel_left neg1_shifted_is_not_mask
          or.left_neutral take_bit_eq_mask take_bit_or word_subseteq_mono_and word_subseteq_mono_or)
    then show ?thesis
      using a63 One_nat_def word_subseteq_neg64_ge_signed significantBitTrue by presburger
  next
    case False
    then have b: "signed_take_bit n b = take_bit n b"
      by (simp add: signed_take_bit_eq_if_positive)
    then have "0 \<le>s signed_take_bit n b"
      by (metis an bit_imp_le_length signed_0 take_bit_smaller_range word_sle_eq)
    then show ?thesis
      using a0 by auto
  qed
qed

text \<open>The main correctness result for minValueForMasks is that all values that have
  the required bits set will be greater than (or equal to) the lower bound that
  minValueForMasksCorrect returns.\<close> 
lemma minValueForMasksCorrect:
  assumes "minValueForMasks bits downMask upMask = m"
  assumes "0 < bits"
  assumes "bits \<le> 64"
  assumes "val \<subseteq>w upMask"
  assumes "downMask \<subseteq>w val"
  shows "int_signed_value bits m \<le> int_signed_value bits val"
proof (cases "significantBit bits upMask = 0")
  case True
  then have 10: "\<not> bit upMask (bits - Suc 0)"
    using significantBitFalse by simp
  then have 11: "\<not> bit val (bits - Suc 0)"
    using assms(4) word_subseteq_implies by blast
  then have 12: "\<not> bit downMask (bits - Suc 0)"
    using assms(5) word_subseteq_implies by blast
  then have m: "m = downMask"
    using True assms(1) minValueForMasks_def by fastforce
  then have mval: "m \<le> val"
    using assms(5) less_bits_leq_unsigned by blast
(* strange that unsigned is easier to prove here than signed! *)
  then have "0 \<le> signed_take_bit (bits - Suc 0) val"
    using word_zero_le by blast
  then have valpos: "0 \<le> int_signed_value bits val"
    by (metis (mono_tags, opaque_lifting) "11" assms(3) bit_uint_iff less_imp_diff_less nat_less_le
        signed_take_bit_eq_if_positive sint_uint size64 take_bit_nonnegative take_bit_smaller_range
        wsst_TYs(3) One_nat_def int_signed_value.simps)
  then have "0 \<le> int_signed_value bits m"
    by (smt (verit, best) "11" "12" One_nat_def valpos mval bit_last_iff bit_take_bit_iff
        int_signed_value.simps m signed_take_bit_eq_if_positive top_bit_false_if_le)
  then show ?thesis
    using "11" assms(2,3,5) m word_subseteq_pos_ge_signed significantBitFalse by blast
next
  case False
  then have 10: "bit upMask (bits - Suc 0)"
    using significantBitFalse by simp
  then have m1: "m = (downMask OR ((-1) << (bits - Suc 0)))"
    using assms(1) minValueForMasks_def by fastforce
  then have 11: "bit ((-1 :: int64) << (bits - Suc 0)) (bits - Suc 0)"
    unfolding neg1_shifted_is_not_mask
    using "10" bit_mask_iff bit_not_iff impossible_bit by blast
  then have 12: "bit m (bits - 1)"
    by (metis m1 bit_or_iff One_nat_def)
  then have 13: "of_bool (bit m (bits - 1)) = 1"
    by simp
  then have m2: "int_signed_value bits m = 
     sint (take_bit (bits - (1::nat)) m OR (NOT (mask (bits - (1::nat)))))"
    by (simp add: signed_take_bit_def)
  then have "bit (int_signed_value bits m) (size m - Suc 0)"
    by (smt (z3) "12" bit_imp_le_length bit_last_iff bit_not_iff bit_or_iff bit_sint_iff wsst_TYs(3)
        impossible_bit sint_n1 take_bit_minus_one_eq_mask take_bit_smaller_range)
  then have "int_signed_value bits m < 0"
    by (metis One_nat_def bit_last_iff bit_sint_iff int_signed_value.simps wsst_TYs(3))
  then have m3: "m = (((-1) << (bits - Suc 0)) OR downMask)"
    using m1 or.commute by blast
  then show ?thesis
    using assms(2,3,5) neg_subset_leq by (simp add: word_sle_eq)
qed

lemma minValueForMasksLowerBound:
  assumes "0 < bits"
  assumes "bits \<le> 64"
  assumes "downMask \<subseteq>w upMask"
  assumes "upMask \<subseteq>w mask bits"
  assumes "minValueForMasks bits downMask upMask = m"
  shows "fst (bit_bounds bits) \<le> int_signed_value bits m"
  using assms(1,2) int_signed_value_bounds by blast

subsection \<open>Calculate maximum bound from masks\<close>

text \<open>Precondition: $significantBit downMask = 1 \<longrightarrow> significantBit upMask = 1$.\<close>
definition maxValueForMasks:: "nat \<Rightarrow> int64 \<Rightarrow> int64 \<Rightarrow> int64" where
  "maxValueForMasks bits downMask upMask = (
    if significantBit bits downMask = (1::int64)
    then (signed_take_bit (bits - 1) upMask)
    else (upMask AND (mask bits >>> 1))
  )"

text \<open>Some examples:\<close>

corollary "maxValueForMasks 32 0 5 = 5" by eval
corollary "sint(maxValueForMasks 32 (-3) (-5)) = -5" by eval

corollary "maxValueForMasks 32 0 (2^32 - 1) = 2^31 - 1" by eval
corollary "sint(maxValueForMasks 32 (-1) 4294967295) = -1" by eval

corollary "numberOfLeadingZeros (5 :: int64) = 61" by eval

text \<open>This is just a translation to Word of the Bit Operations
  lemma $drop\_bit\_mask\_eq$, but was annoyingly hard to prove.\<close>
lemma word_drop_bit_mask_eq:
  fixes n bits :: nat
  assumes "n \<le> bits"
  assumes "bits \<le> LENGTH('a)"
  shows "drop_bit n (mask bits :: 'a :: len word) = (mask (bits - n) :: 'a :: len word)"
proof (rule bit_word_eqI)
  fix na
  assume na: "na < LENGTH('a)"
  then show "bit (drop_bit n (mask bits :: 'a :: len word)) na = bit (mask (bits - n) :: 'a :: len word) na"
  proof (cases "na < bits - n")
    case True
    then have R: "bit (mask (bits - n) :: 'a :: len word) na"
      unfolding bit_mask_iff
      by (simp add: True assms na)
    then have L: "bit (drop_bit n (mask bits :: 'a :: len word) :: 'a :: len word) na"
      by (metis assms(2) drop_bit_mask_eq drop_bit_word.abs_eq mask_word.abs_eq min.commute min_def
          of_int_mask_eq uint_mask_eq uint_word_of_int_eq)
    then show ?thesis
      using L R by auto
  next
    case False
    then show ?thesis
      by (smt (verit, best) assms(2) drop_bit_mask_eq drop_bit_word.abs_eq mask_word.abs_eq min_def
          min.commute take_bit_length_eq uint_mask_eq unsigned_take_bit_eq)
  qed
qed

text \<open>This is a helper lemma for when maxValueForMasks returns a positive value.
  In that case the bits above $n$ are all false, and we only need a subset
  relationship on the bits below $n$ in order to prove signed less-than-or-equal.\<close>
lemma pos_subset_leq:
  fixes a b bLow :: "'a :: len word"
  assumes "0 \<le> n"
  assumes "n < LENGTH('a)"
  assumes "b = bLow AND (mask n :: 'a :: len word)"
  assumes "a \<subseteq>w bLow"
  shows "sint (signed_take_bit n a) \<le> sint (signed_take_bit n b)"
proof -
  have "of_bool (bit b n) = 0"
    by (simp add: assms(3) bit_and_iff bit_mask_iff)
  then have b: "signed_take_bit n b = take_bit n b"
    by (simp add: signed_take_bit_eq_if_positive)
  then have bpos: "0 \<le> sint (signed_take_bit n b)"
      using assms(2) take_bit_smaller_range by auto
  then show ?thesis
  proof (cases "bit a n")
    case True
    then have "of_bool (bit a n) = 1"
      by simp
    then have aneg: "sint (signed_take_bit n a) < 0"
      by (smt (verit, del_insts) True bit_1_iff bit_imp_le_length bit_last_iff diff_Suc_less
          dual_order.strict_iff_not or_negative_int_iff signed_or_eq take_bit_smaller_range
          signed_take_bit_eq_if_negative signed_take_bit_of_minus_1 negone_set)
    then show ?thesis 
      using aneg bpos by arith
  next
    case False
    then have a: "signed_take_bit n a = take_bit n a"
      by (simp add: signed_take_bit_eq_if_positive)
    then have apos: "0 \<le> sint (signed_take_bit n a)"
      using assms(2) take_bit_smaller_range by auto
    then show ?thesis
      by (metis a and.right_idem assms(3,4) b bpos less_bits_leq_unsigned pos_implies_sint_leq
          take_bit_eq_mask word_subseteq_mono_and)
  qed
qed

lemma maxValueForMasksCorrect:
  assumes "maxValueForMasks bits downMask upMask = m"
  assumes "0 < bits"
  assumes "bits \<le> 64"
  assumes "val \<subseteq>w upMask"
  assumes "downMask \<subseteq>w val"
  shows "int_signed_value bits val \<le> int_signed_value bits m" (is "?L \<le> ?R")
proof (cases "significantBit bits downMask = 1")
  case True
  then have 10: "bit upMask (bits - Suc 0)"
    using significantBitTrue assms(4,5) word_subseteq_implies by blast
  then have m: "m = signed_take_bit (bits - 1) upMask"
    using True assms(1) maxValueForMasks_def by fastforce
  then have m': "signed_take_bit (bits - 1) m = signed_take_bit (bits - 1) upMask"
    by simp
  then have 11: "bit val (bits - Suc 0)"
    using True assms(5) word_subseteq_implies_rev by auto
  then have "signed_take_bit (bits - 1) val \<subseteq>w signed_take_bit (bits - 1) upMask"
    by (simp add: "10" assms(4) signed_take_bit_def take_bit_eq_mask word_subseteq_mono_and
        word_subseteq_mono_or)
  then show ?thesis
    unfolding int_signed_value.simps m'
    using "11" assms(2,3,4) word_subseteq_neg_ge_signed by auto
next
  case False
  then have m: "m = upMask AND (drop_bit 1 (mask bits))" 
    by (metis assms(1) maxValueForMasks_def shiftr_def)
  then have "\<not> bit (drop_bit 1 (mask bits)) (bits - Suc 0)"
    by (metis One_nat_def assms(2) bit_iff_and_drop_bit_eq_1 bit_mask_iff drop_bit_drop_bit
        le_add_diff_inverse2 less_not_refl less_one linorder_not_less)
  then have "\<not> bit m (bits - Suc 0)"
    using m bit_and_iff by blast 
  then show ?thesis
    by (metis One_nat_def Suc_pred' assms(2,3,4) linorder_not_le m not_less_eq size64 wsst_TYs(3)
        word_drop_bit_mask_eq pos_subset_leq int_signed_value.simps)
qed

lemma maxValueForMasksUpperBound:
  assumes "0 < bits"
  assumes "bits \<le> 64"
  assumes "downMask \<subseteq>w upMask"
  assumes "upMask \<subseteq>w mask bits"
  assumes "maxValueForMasks bits downMask upMask = m"
  shows "int_signed_value bits m \<le> snd (bit_bounds bits)"
  using assms(1,2) int_signed_value_bounds by blast

subsection \<open>Constructor functions for JavaIntegerStamp\<close>

definition neg_one64 :: "int64" where
  "neg_one64 = ((-1) :: int64)"

definition createJIS:: "nat \<Rightarrow> int64 \<Rightarrow> int64 \<Rightarrow> int64 \<Rightarrow> int64 \<Rightarrow> JavaIntegerStamp" where
  "createJIS bits lo hi down up = (
    let minValue = minValueForMasks bits down up in
    let loTemp = javaMax64 lo minValue :: int64 in
    let maxValue = maxValueForMasks bits down up in
    let hiTemp = javaMin64 hi maxValue :: int64 in
    let defaultMask = mask bits :: int64 in
    let (boundedUpMask, boundedDownMask) = (
      if loTemp = hiTemp then
        (loTemp, loTemp)
      else
        if loTemp \<ge> 0 then
          let upperBoundLeadingZeros = numberOfLeadingZeros hiTemp in
          let differentBits = (loTemp XOR hiTemp) in
          let sameBitCount = numberOfLeadingZeros (differentBits >> upperBoundLeadingZeros) in
          let x = (neg_one64 >>> nat (upperBoundLeadingZeros + sameBitCount)) in
          (hiTemp OR x, hiTemp AND (NOT x))
        else
          if hiTemp \<ge> 0 then
            (defaultMask, 0 :: int64)
          else
            let lowerBoundLeadingOnes = numberOfLeadingZeros (NOT loTemp) in
            let differentBits = (loTemp XOR hiTemp) in
            let sameBitCount = numberOfLeadingZeros (differentBits >> lowerBoundLeadingOnes) in
            let x = (neg_one64 >>> nat (lowerBoundLeadingOnes + sameBitCount)) in
            let y = (NOT (neg_one64 >>> nat lowerBoundLeadingOnes)) in
            (loTemp OR x OR y, loTemp AND (NOT x) OR y)
    ) in
    JIS bits loTemp hiTemp (defaultMask AND down OR boundedDownMask) (defaultMask AND up AND boundedUpMask)
  )"

fun create_without_masks:: "nat \<Rightarrow> int64 \<Rightarrow> int64 \<Rightarrow> JavaIntegerStamp" where
  "create_without_masks bits lo hi = (createJIS bits lo hi 0 (mask bits))"

text \<open>We start by proving that createJIS always gives lo/hi bounds at least as tight as the input
  bounds and up/down masks that are at least as good as the input masks (restricted to bits).\<close>

lemma JIS_bits_same:
  "jis_bits (createJIS bits lo hi down up) = bits"
  by (smt (z3) JavaIntegerStamp.sel(1) old.prod.case createJIS_def)

lemma JIS_lower_bound_better:
  "lo \<le>s jis_lowerBound (createJIS bits lo hi down up)"
  by (smt (z3) JavaIntegerStamp.sel(2) old.prod.case signed.order_refl createJIS_def)

lemma JIS_upper_bound_better:
  "jis_upperBound (createJIS bits lo hi down up) \<le>s hi"
  by (smt (z3) JavaIntegerStamp.sel(3) old.prod.case signed.linear word_zero_le createJIS_def)

lemma word_subseteq_or:
  "a \<subseteq>w (a OR b)"
  by (metis or.left_neutral word_bw_comms(2) word_subseteq_def word_subseteq_mono_or zero_and_eq)

lemma word_subseteq_and:
  "(a AND b) \<subseteq>w a"
  by (metis word_ao_absorbs(8) word_subseteq_or)

lemma JIS_down_mask_better:
  assumes "(mask bits AND down) = down"
  shows  "down \<subseteq>w jis_downMask (createJIS bits lo hi down up)"
  by (smt (z3) assms word_subseteq_or JavaIntegerStamp.case old.prod.case jis_downMask_def
      createJIS_def)

lemma JIS_up_mask_better:
  shows "jis_upMask (createJIS bits lo hi down up) \<subseteq>w up"
  by (smt (z3) word_subseteq_and JavaIntegerStamp.sel(5) and.left_commute jis_upMask_def
      prod.case_eq_if createJIS_def)

value "JIS_valid (createJIS 32 (-1000) 10000 0xF0F 0x3FFF)"
value "JIS_valid (create_without_masks 32 (-1000) 10000)"

lemma and_or_mask_simp:
  fixes m a b :: "'a :: len word"
  shows "((((m AND a) OR b) AND m) = ((m AND a) OR b)) \<longleftrightarrow> ((b AND m) = b)"
  by (metis (no_types, opaque_lifting) bit.disj_conj_distrib or.commute word_ao_absorbs(2,3))

text \<open>These are the preconditions of every valid JIS constructor call.\<close>
abbreviation createJISpre :: "nat \<Rightarrow> int64 \<Rightarrow> int64 \<Rightarrow> int64 \<Rightarrow> int64 \<Rightarrow> bool" where
  "createJISpre bits lo hi down up \<equiv> (
    0 < bits \<and> bits \<le> 64 \<and>
    fst (bit_bounds bits) \<le> sint lo \<and>
    lo \<le> hi \<and>
    sint hi \<le> fst (bit_bounds bits) \<and>
    down \<subseteq>w up)"

text \<open>Now we want to prove that given valid inputs, the JIS constructor returns a
  stamp that is valid.
  A simple case first, where the inferred lower and upper bounds are equal.\<close>
lemma createJIS_is_valid1:
  fixes lo hi down up :: int64
  assumes "createJISpre bits lo hi down up"
  assumes "minValueForMasks bits down up = minValue"
  assumes "javaMax64 lo minValue = loTemp"
  assumes "maxValueForMasks bits down up = maxValue"
  assumes "javaMin64 hi maxValue = hiTemp"
  assumes "(mask bits :: int64) = defaultMask"
  assumes "loTemp = hiTemp"
  shows "JIS_valid (createJIS bits lo hi down up)"
proof -
  have r: "createJIS bits lo hi down up =
    JIS bits loTemp loTemp ((defaultMask AND down) OR loTemp) (defaultMask AND up AND loTemp)"
    unfolding createJIS_def by (smt (verit, best) assms case_prod_conv)
  then have lo: "- ((2::int) ^ bits div 2) \<le> sint (signed_take_bit (bits - Suc 0) hiTemp)"
    using One_nat_def assms(1) int_signed_value.simps int_signed_value_range two_exp_div by presburger
  then have hi: "sint (signed_take_bit (bits - Suc 0) hiTemp) < (2::int) ^ bits div 2"
    using One_nat_def assms(1) int_signed_value.simps int_signed_value_range two_exp_div by presburger
  then have 10: "(defaultMask AND down OR hiTemp) AND defaultMask = defaultMask AND down OR hiTemp"
    unfolding and_or_mask_simp
    sorry
(*
  proof -
    have "hiTemp <s (2::int64) ^ (bits - 1)"
    unfolding and_or_mask_simp

    by (smt (z3) One_nat_def Suc_pred assms bit_take_bit_iff less_irrefl maskSmaller mask_eq_iff maxValueForMasks_def min_def signed_take_bit_eq_if_positive take_bit_eq_mask word_ao_absorbs(3) word_ao_absorbs(8) word_less_eq_iff_unsigned)
*)
  then have 11: "(defaultMask AND up AND hiTemp) AND defaultMask =
    defaultMask AND up AND hiTemp"
    by (simp add: and.commute)
  then have 12: "(defaultMask AND down OR hiTemp) \<subseteq>w (defaultMask AND up AND hiTemp)"
    sorry
  then show ?thesis
    unfolding r JIS_valid.simps
    by (simp add: assms lo hi 10 11 12)
qed

(* TODO:
fun create_integer_stamp:: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> JavaIntegerStamp" where
  "create_integer_stamp bits lo hi down up = (
    if lo > hi \<or> ~ ((down AND (NOT up)) = 0) \<or> (up = 0 \<and> (lo > 0 \<or> hi < 0))
    then empty_stamp (IntegerStamp bits 0 0 0 0)
    else createJIS bits lo hi down up
  ) "
*)

value "~(nat 2 = 3) "
value "~ nat 3 AND NOT 2 = 0 "

(* Call with an integer stamp, and a new constant value. *) 
(* TODO:
fun sf_constant :: "JavaIntegerStamp \<Rightarrow> int \<Rightarrow> Value \<Rightarrow> JavaIntegerStamp" where
  "sf_constant this bits (IntVal64 val) = (
    if bits = 1 \<and> val = 1
    then create_without_masks (IntVal64 (word_of_int (stp_bits this))) (IntVal64 (-1)) (IntVal64 (-1))
    else create_without_masks (IntVal64 (word_of_int (stp_bits this))) (IntVal64 val) (IntVal64 val)
  )" |
  "sf_constant this _ _ = this"

value "sf_constant (IntegerStamp 32 1 2 1 2) 1  UndefVal"

value "sf_constant (IntegerStamp 32 1 2 1 2) 64 (IntVal64 5)"


fun sf_contains:: "JavaInJavaIntegerStamptStamp \<Rightarrow> Value \<Rightarrow> bool" where
  "sf_contains (IntegerStamp b l h d u) (IntVal64 val) = ((sint val \<ge> l) \<and> (sint val \<le> h))" |
  "sf_contains _ _ = False"
*)

fun sf_is_positive:: "JavaIntegerStamp \<Rightarrow> bool" where
  "sf_is_positive (JIS b l h d u) = (l \<ge> 0) "

fun sf_is_negative:: "JavaIntegerStamp \<Rightarrow> bool" where
  "sf_is_negative (JIS b l h d u) = (h \<le> 0) "

fun sf_is_strictly_positive:: "JavaIntegerStamp \<Rightarrow> bool" where
  "sf_is_strictly_positive (JIS b l h d u) = (l > 0) "

fun sf_is_strictly_negative:: "JavaIntegerStamp \<Rightarrow> bool" where
  "sf_is_strictly_negative (JIS b l h d u) = (h < 0) "

fun sf_can_be_positive:: "JavaIntegerStamp \<Rightarrow> bool" where
  "sf_can_be_positive (JIS b l h d u) = (h > 0) "

fun sf_can_be_negative:: "JavaIntegerStamp \<Rightarrow> bool" where
  "sf_can_be_negative (JIS b l h d u) = (l < 0) "

fun sf_is_compatible1:: "JavaIntegerStamp \<Rightarrow> JavaIntegerStamp \<Rightarrow> bool" where 
  "sf_is_compatible1 (JIS b1 l1 h1 d1 u1) (JIS b2 l2 h2 d2 u2) = (b1 = b2)"

(* TODO:
fun sf_is_compatible2:: "JavaIntegerStamp \<Rightarrow> Value \<Rightarrow> bool" where 
  "sf_is_compatible2 this (IntVal32 val) = True" |
  "sf_is_compatible2 this (IntVal64 val) = True" |
  "sf_is_compatible2 _ _ = False"
*)

fun sf_same_sign_bounds:: "JavaIntegerStamp \<Rightarrow> bool" where 
  "sf_same_sign_bounds (JIS b l h d u) = ((l < 0) = (h < 0))"

(* TODO:
fun stamp_for_mask:: "Value \<Rightarrow> Value \<Rightarrow> Value \<Rightarrow> JavaIntegerStamp" where
  "stamp_for_mask (IntVal64 bits) (IntVal64 down) (IntVal64 up) = (
    let lo = (minValueForMasks (IntVal64 bits) (IntVal64 down) (IntVal64 up)) in
    let hi = (maxValueForMasks (IntVal64 bits) (IntVal64 down) (IntVal64 up)) in 
    IntegerStamp (unat bits) (val_to_int lo) (val_to_int hi))" | 
  "stamp_for_mask _ _ _ = IllegalStamp"

value "val_to_int (minValueForMasks (IntVal64 1) (IntVal64 2) (IntVal64 3))"
*)

value "javaMax64 42 0xffffffffffffff2c :: int64"

end (* bit_operations_syntax for infix AND, OR, XOR, and prefix NOT *)
end
