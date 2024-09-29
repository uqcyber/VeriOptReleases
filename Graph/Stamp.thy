section \<open>Stamp Typing\<close>

theory Stamp
  imports Values
begin

text \<open>
The GraalVM compiler uses the Stamp class to store range and type information
for a given node in the IR graph.
We model the Stamp class as a datatype, Stamp, and provide a number of functions
on the datatype which correspond to the class methods within the compiler.

Stamp information is used in a variety of ways in optimizations, and so, we
additionally provide a number of lemmas which help to prove future optimizations.
\<close>

datatype Stamp =
  VoidStamp
  | IntegerStamp (stp_bits: nat) (stpi_lower: int64) (stpi_upper: int64) (stpi_down: int64) (stpi_up: int64)
  (* | FloatStamp (stp_bits: nat) (stpf_lower: float) (stpf_upper: float) *)
  | KlassPointerStamp (stp_nonNull: bool) (stp_alwaysNull: bool)
  | MethodCountersPointerStamp (stp_nonNull: bool) (stp_alwaysNull: bool)
  | MethodPointersStamp (stp_nonNull: bool) (stp_alwaysNull: bool)
  | ObjectStamp (stp_type: string) (stp_exactType: bool) (stp_nonNull: bool) (stp_alwaysNull: bool)
  | RawPointerStamp (stp_nonNull: bool) (stp_alwaysNull: bool)
  | IllegalStamp


text \<open>To help with supporting masks in future, this constructor allows masks but ignores them.\<close>
abbreviation IntegerStampM :: "nat \<Rightarrow> int64 \<Rightarrow> int64 \<Rightarrow> int64 \<Rightarrow> int64 \<Rightarrow> Stamp" where
  "IntegerStampM b lo hi down up \<equiv> IntegerStamp b lo hi down up"


abbreviation javaLT :: "nat \<Rightarrow> int64 \<Rightarrow> int64 \<Rightarrow> bool" ("_ \<turnstile> _ <j _" 50) where
  "javaLT b x y \<equiv> (int_signed_value b x < int_signed_value b y)"

abbreviation javaLTE :: "nat \<Rightarrow> int64 \<Rightarrow> int64 \<Rightarrow> bool" ("_ \<turnstile> _ \<le>j _" 50) where
  "javaLTE b x y \<equiv> (int_signed_value b x \<le> int_signed_value b y)"


fun is_stamp_empty :: "Stamp \<Rightarrow> bool" where
  "is_stamp_empty (IntegerStamp b lower upper down up) = (b \<turnstile> upper <j lower)" |
  (* "is_stamp_empty (FloatStamp b lower upper) = (upper < lower)" | *)
  "is_stamp_empty x = False"


text \<open>Just like the IntegerStamp class, we need to know that our lo/hi bounds
  fit into the given number of bits (either signed or unsigned).
  Our integer stamps have infinite lo/hi bounds, so if the lower
  bound is non-negative, we can assume that all values are positive,
  and the integer bits of a related value can be interpreted as unsigned.
  This is similar (but slightly more general) to what IntegerStamp.java
  does with its test: if (sameSignBounds()) in the unsignedUpperBound() method.

  Note that this is a bit different and more accurate than what
  StampFactory.forUnsignedInteger does (it widens large unsigned ranges to the
  max signed range to allow all bit patterns) because its lo/hi values are only 64-bit.
\<close>
(* TODO: should we have tight bounds for empty stamp, or just hi<lo?
   We could have: (lo = snd (bit_bounds bits) \<and> hi = fst (bit_bounds bits) 
 *)
context includes bit_operations_syntax begin
definition min_int :: "nat \<Rightarrow> int64" where
  "min_int bits = (NOT (mask (bits-1)))"
end

value "(min_int 32)"
value "signed_take_bit 31 (min_int 32)"
value "signed_take_bit 32 (min_int 32)"
value "signed_take_bit 36 (min_int 32)"

value "signed_take_bit 2 5::int64"
value "signed_take_bit 2 (13)::int64"
value "sint (signed_take_bit 2 5::int64)"
value "sint (signed_take_bit 2 (13)::int64)"


lemma min_int_push_bit:
  assumes "0 < b \<and> b \<le> 64"
  shows "-(2 ^ (b - 1)) = ((push_bit (b-1) (-1))::int64)" (is "?lhs = ?rhs")
proof -
  have "?rhs = -1 * (2 ^ (b-1))"
    using push_bit_eq_mult by blast
  also have "... = -(2 ^ (b-1))"
    using mult_minus1 by blast
  ultimately show ?thesis by simp
qed

lemma min_int_signed_neg2pow_signed:
  assumes "0 < b \<and> b \<le> 64"
  shows "int_signed_value b (min_int b) = int_signed_value b (-(2^(b-1)))"
  using assms unfolding min_int_def
  by (smt (verit, del_insts) Word.bit_mask_iff bit.compl_zero bit_mask_iff bit_push_bit_iff diff_is_0_eq less_numeral_extra(1) linorder_not_less mask_0 mask_eq_take_bit_minus_one min_int_push_bit min_less_iff_conj minus_1_eq_mask minus_exp_eq_not_mask neg_0_equal_iff_equal one_neq_zero or.idem or.left_neutral set_bit_eq_idem_iff set_bit_eq_or take_bit_not_mask_eq_0 word_bw_comms(2))

context includes bit_operations_syntax begin
lemma set_bit_not_eqv:
  "set_bit (b-1) 0 OR (NOT (mask (b-1))) = NOT (mask (b-1))"
  by (metis bit.disj_one_right or.left_neutral push_bit_minus_one_eq_not_mask push_bit_or set_bit_eq_or)

lemma min_int_signed_neg2pow:
  "(min_int b) = (-(2^(b-1)))"
proof -
  have "-(2^(b-1)) = NOT ((2^(b-1)) - 1)"
    using minus_eq_not_minus_1 by simp
  also have "... = NOT (mask (b-1))"
    using mask_eq_exp_minus_1 by metis
  also have "... = min_int b"
    using min_int_def by simp
  ultimately show ?thesis
    by metis
qed

end

definition max_int :: "nat \<Rightarrow> int64" where
  "max_int bits = mask (bits - 1)"

lemma max_int_mask:
  assumes "0 < b \<and> b \<le> 64"
  shows "(2 ^ (b - 1)) - 1 = ((mask (b-1))::int64)" (is "?lhs = ?rhs")
  using assms
  by (simp add: mask_eq_decr_exp)

lemma max_int_signed_2pow:
  "(max_int b) = ((2 ^ (b - 1)) - 1)"
  by (simp add: mask_eq_exp_minus_1 max_int_def)

lemma max_int_signed_2pow_signed:
  assumes "0 < b \<and> b \<le> 64"
  shows "int_signed_value b (max_int b) = int_signed_value b ((2 ^ (b - 1)) - 1)"
  using assms
  by (simp add: mask_eq_exp_minus_1 max_int_def)

lemma raise_lt:
  assumes "0 < b \<and> b \<le> 64"
  assumes "b \<turnstile> x <j y"
  shows "64 \<turnstile> (signed_take_bit (b-1) x) <j (signed_take_bit (b-1) y)"
  using assms unfolding int_signed_value.simps
  by fastforce

lemma
  assumes "signed_take_bit (b-1) v = v"
  assumes "signed_take_bit (b-1) x = x"
  assumes "0 < b \<and> b \<le> 64"
  assumes "b \<turnstile> x <j v"
  shows "64 \<turnstile> x <j v"
  using assms
  by (metis raise_lt)

lemma max_int_signed_take_bit:
  assumes "0 < b \<and> b \<le> 64"
  shows "signed_take_bit (b-1) (max_int b) = max_int b" (is "signed_take_bit ?b ?m = ?m")
proof -
  have "max_int b = take_bit (b-1) (-1)"
    using take_bit_minus_one_eq_mask unfolding max_int_def by simp
  also have "signed_take_bit (b-1) (take_bit (b-1) (-1)) = take_bit (b-1) (-1)"
    using signed_take_bit_take_bit eq_imp_le
    by (metis (mono_tags, lifting))
  ultimately show ?thesis
    by simp
qed

context includes bit_operations_syntax begin

lemma push_bit_bit_set_:
  assumes "b < LENGTH('a)"
  shows "bit (push_bit b (1::'a::len word)) b" (is "bit ?pb ?b")
  using assms
  by (simp add: bit_exp_iff)

lemma push_bit_bit_set:
  assumes "0 < b \<and> b \<le> 64"
  shows "bit (push_bit (b-1) (1::int64)) (b-1)" (is "bit ?pb ?b")
proof -
  have "?pb = 1 * 2 ^ ?b"
    using push_bit_eq_mult by blast
  also have "... = 2 ^ ?b"
    using calculation by simp
  also have "... \<noteq> 0" 
    using assms
    by (metis (mono_tags, lifting) diff_less exp_eq_zero_iff nat_less_le nle_le order_trans size64 wsst_TYs(3) zero_less_one)
  ultimately have "?pb \<noteq> 0"
    using assms by simp
  then have "(push_bit (b-1) (1::int64)) AND (push_bit (b-1) (1::int64)) \<noteq> 0"
    by simp
  then show ?thesis using bit_iff_and_push_bit_not_eq_0
    by blast
qed

lemma min_int_signed_take_bit:
  assumes "0 < b \<and> b \<le> 64"
  shows "signed_take_bit (b-1) (min_int b) = min_int b" (is "signed_take_bit ?b ?m = ?m")
proof -
  have "signed_take_bit ?b ?m = take_bit ?b ?m OR (of_bool (bit ?m ?b) * NOT (mask ?b))"
    using signed_take_bit_def by blast
  have "bit (push_bit (b-1) (1::int64)) (b-1)"
    using assms bit_iff_and_push_bit_not_eq_0
    using push_bit_bit_set by presburger
  then have "bit (set_bit (b-1) (0::64 word)) (b-1)"
    using assms
    using bit_push_bit_iff bit_set_bit_iff by blast
  then have "bit ?m ?b"
    unfolding min_int_def
    using bit_or_iff
    by (metis set_bit_not_eqv)
  then have "signed_take_bit ?b ?m = take_bit ?b ?m OR (NOT (mask ?b))"
    by (simp add: signed_take_bit_eq_if_negative)
  then show ?thesis
    by (metis (no_types, lifting) bit.disj_one_right min_int_def or.left_neutral push_bit_minus_one_eq_not_mask push_bit_or set_bit_eq_or take_bit_minus_one_eq_mask take_bit_not_take_bit take_bit_of_0 word_bitwise_m1_simps(1))
qed

thm_oracles min_int_signed_take_bit
end

fun valid_stamp :: "Stamp \<Rightarrow> bool" where
  "valid_stamp (IntegerStamp bits lo hi down up) = 
     (0 < bits \<and> bits \<le> 64 \<and>
     signed_take_bit (bits-1) lo = lo \<and> (bits \<turnstile> (min_int bits) \<le>j lo) \<and> (bits \<turnstile> lo \<le>j (max_int bits)) \<and>
     signed_take_bit (bits-1) hi = hi \<and> (bits \<turnstile> (min_int bits) \<le>j hi) \<and> (bits \<turnstile> hi \<le>j (max_int bits)))" |
  "valid_stamp s = True"

(* Note: we could support 32/64-bit unsigned values by relaxing this definition to:
     (is_stamp_empty (IntegerStamp bits lo hi)
     \<or> lo < 0 \<and> fst (bit_bounds bits) \<le> lo \<and> lo \<le> hi \<and> hi \<le> snd (bit_bounds bits)
     \<or> 0 \<le> lo \<and> lo \<le> hi \<and> hi < 2 ^ bits))"
*)

experiment begin
corollary "min_int 1 = -1 \<and> max_int 1 = 0" by eval  (* this matches the compiler stamps. *)
end

(* NOTE: the FloatStamp has been commented out to allow use of code generation facilities *)
(*
definition pos_infinity :: "float" where
  "pos_infinity = float_of (0 * 2 powr 255)"

definition neg_infinity :: "float" where
  "neg_infinity = -pos_infinity"
*)

\<comment> \<open>A stamp which includes the full range of the type\<close>
fun unrestricted_stamp :: "Stamp \<Rightarrow> Stamp" where
  "unrestricted_stamp VoidStamp = VoidStamp" |
  "unrestricted_stamp (IntegerStamp bits lower upper down up) = (IntegerStamp bits (min_int bits) (max_int bits) 0 (mask bits))" | 
  (* "unrestricted_stamp (FloatStamp bits lower upper) = (FloatStamp bits neg_infinity pos_infinity)" |  *)
  "unrestricted_stamp (KlassPointerStamp nonNull alwaysNull) = (KlassPointerStamp False False)" |
  "unrestricted_stamp (MethodCountersPointerStamp nonNull alwaysNull) = (MethodCountersPointerStamp False False)" |
  "unrestricted_stamp (MethodPointersStamp nonNull alwaysNull) = (MethodPointersStamp False False)" |
  "unrestricted_stamp (ObjectStamp type exactType nonNull alwaysNull) = (ObjectStamp '''' False False False)" |
  "unrestricted_stamp _ = IllegalStamp"

fun is_stamp_unrestricted :: "Stamp \<Rightarrow> bool" where
  "is_stamp_unrestricted s = (s = unrestricted_stamp s)"

\<comment> \<open>A stamp which provides type information but has an empty range of values\<close>
fun empty_stamp :: "Stamp \<Rightarrow> Stamp" where
  "empty_stamp VoidStamp = VoidStamp" |
  "empty_stamp (IntegerStamp bits lower upper down up) = (IntegerStamp bits (max_int bits) (min_int bits) (mask bits) 0)" |
  (* "empty_stamp (FloatStamp bits lower upper) = (FloatStamp bits pos_infinity neg_infinity)" | *)
  "empty_stamp (KlassPointerStamp nonNull alwaysNull) = (KlassPointerStamp nonNull alwaysNull)" |
  "empty_stamp (MethodCountersPointerStamp nonNull alwaysNull) = (MethodCountersPointerStamp nonNull alwaysNull)" |
  "empty_stamp (MethodPointersStamp nonNull alwaysNull) = (MethodPointersStamp nonNull alwaysNull)" |
  "empty_stamp (ObjectStamp type exactType nonNull alwaysNull) = (ObjectStamp '''' True True False)" |
  "empty_stamp stamp = IllegalStamp"

definition smin :: "nat \<Rightarrow> int64 \<Rightarrow> int64 \<Rightarrow> int64" where
  "smin b x y = (if b \<turnstile> x \<le>j y then x else y)"

definition smax :: "nat \<Rightarrow> int64 \<Rightarrow> int64 \<Rightarrow> int64" where
  "smax b x y = (if b \<turnstile> x \<le>j y then y else x)"


lemma signed_value_eq:
  assumes "take_bit b x = x"
  assumes "take_bit b y = y"
  shows "int_signed_value b x = int_signed_value b y \<Longrightarrow> x = y"
  unfolding int_signed_value.simps
  by (smt (verit, best) Suc_pred' assms(1) assms(2) cancel_comm_monoid_add_class.diff_cancel less_imp_diff_less not_less signed_take_bit_eq_iff_take_bit_eq signed_take_bit_take_bit signed_word_eqI)

lemma smin_commute:
  assumes "take_bit b x = x"
  assumes "take_bit b y = y"
  shows "smin b x y = smin b y x"
  unfolding smin_def
  by (meson assms(1) assms(2) nle_le signed_value_eq)

lemma smax_commute:
  assumes "take_bit b x = x"
  assumes "take_bit b y = y"
  shows "smax b x y = smax b y x"
  unfolding smax_def
  by (meson assms(1) assms(2) nle_le signed_value_eq)

lemma smin_signed_commute:
  assumes "signed_take_bit (b-1) x = x"
  assumes "signed_take_bit (b-1) y = y"
  shows "smin b x y = smin b y x"
  unfolding smin_def
  using assms(1) assms(2) signed_word_eqI by auto

lemma smax_signed_commute:
  assumes "signed_take_bit (b-1) x = x"
  assumes "signed_take_bit (b-1) y = y"
  shows "smax b x y = smax b y x"
  unfolding smax_def
  using assms(1) assms(2) signed_word_eqI by auto


\<comment> \<open>Calculate the meet stamp of two stamps\<close>
fun meet :: "Stamp \<Rightarrow> Stamp \<Rightarrow> Stamp" where
  "meet VoidStamp VoidStamp = VoidStamp" |
  "meet (IntegerStamp b1 l1 u1 d1 up1) (IntegerStamp b2 l2 u2 d2 up2) = (
    if b1 \<noteq> b2 then IllegalStamp else 
    (IntegerStamp b1 (smin b1 l1 l2) (smax b1 u1 u2) (and d1 d2) (or up1 up2))
  )" |
  (* "meet (FloatStamp b1 l1 u1) (FloatStamp b2 l2 u2) = (
    if b1 \<noteq> b2 then IllegalStamp else 
    (FloatStamp b1 (min l1 l2) (max u1 u2))
  )" | *)
  "meet (KlassPointerStamp nn1 an1) (KlassPointerStamp nn2 an2) = (
    KlassPointerStamp (nn1 \<and> nn2) (an1 \<and> an2)
  )" |
  "meet (MethodCountersPointerStamp nn1 an1) (MethodCountersPointerStamp nn2 an2) = (
    MethodCountersPointerStamp (nn1 \<and> nn2) (an1 \<and> an2)
  )" |
  "meet (MethodPointersStamp nn1 an1) (MethodPointersStamp nn2 an2) = (
    MethodPointersStamp (nn1 \<and> nn2) (an1 \<and> an2)
  )" |
  "meet s1 s2 = IllegalStamp"

\<comment> \<open>Calculate the join stamp of two stamps\<close>
fun join :: "Stamp \<Rightarrow> Stamp \<Rightarrow> Stamp" where
  "join VoidStamp VoidStamp = VoidStamp" |
  "join (IntegerStamp b1 l1 u1 d1 up1) (IntegerStamp b2 l2 u2 d2 up2) = (
    if b1 \<noteq> b2 then IllegalStamp else 
    (IntegerStamp b1 (smax b1 l1 l2) (smin b2 u1 u2) (or d1 d2) (and up1 up2))
  )" |
  (* "join (FloatStamp b1 l1 u1) (FloatStamp b2 l2 u2) = (
    if b1 \<noteq> b2 then IllegalStamp else 
    (FloatStamp b1 (max l1 l2) (min u1 u2))
  )" | *)
  "join (KlassPointerStamp nn1 an1) (KlassPointerStamp nn2 an2) = (
    if ((nn1 \<or> nn2) \<and> (an1 \<or> an2)) 
    then (empty_stamp (KlassPointerStamp nn1 an1))
    else (KlassPointerStamp (nn1 \<or> nn2) (an1 \<or> an2))
  )" |
  "join (MethodCountersPointerStamp nn1 an1) (MethodCountersPointerStamp nn2 an2) = (
    if ((nn1 \<or> nn2) \<and> (an1 \<or> an2)) 
    then (empty_stamp (MethodCountersPointerStamp nn1 an1))
    else (MethodCountersPointerStamp (nn1 \<or> nn2) (an1 \<or> an2))
  )" |
  "join (MethodPointersStamp nn1 an1) (MethodPointersStamp nn2 an2) = (
    if ((nn1 \<or> nn2) \<and> (an1 \<or> an2)) 
    then (empty_stamp (MethodPointersStamp nn1 an1))
    else (MethodPointersStamp (nn1 \<or> nn2) (an1 \<or> an2))
  )" |
  "join s1 s2 = IllegalStamp"

\<comment> \<open>
In certain circumstances a stamp provides enough information to evaluate a value as a stamp,
the asConstant function converts the stamp to a value where one can be inferred.
\<close>
(* NOTE: we could also add a 32-bit version of this if needed. *)
fun asConstant :: "Stamp \<Rightarrow> Value" where
  "asConstant (IntegerStamp b l h d u) = (if l = h then new_int b l else UndefVal)" |
  "asConstant _ = UndefVal"

\<comment> \<open>Determine if two stamps never have value overlaps i.e. their join is empty\<close>
fun alwaysDistinct :: "Stamp \<Rightarrow> Stamp \<Rightarrow> bool" where
  "alwaysDistinct stamp1 stamp2 = is_stamp_empty (join stamp1 stamp2)"

\<comment> \<open>Determine if two stamps must always be the same value i.e. two equal constants\<close>
fun neverDistinct :: "Stamp \<Rightarrow> Stamp \<Rightarrow> bool" where
  "neverDistinct stamp1 stamp2 = (asConstant stamp1 = asConstant stamp2 \<and> asConstant stamp1 \<noteq> UndefVal)"

fun constantAsStamp :: "Value \<Rightarrow> Stamp" where
  "constantAsStamp (IntVal b v) = (IntegerStamp b (signed_take_bit (b-1) v) (signed_take_bit (b-1) v) v v)" |
  "constantAsStamp (ObjRef (None)) = ObjectStamp '''' False False True" |
  "constantAsStamp (ObjRef (Some n)) = ObjectStamp '''' False True False" |
  (* TODO: float *)
  "constantAsStamp _ = IllegalStamp"

\<comment> \<open>Define when a runtime value is valid for a stamp.
    The stamp bounds must be valid, and val must be zero-extended.\<close>
fun valid_value :: "Value \<Rightarrow> Stamp \<Rightarrow> bool" where
  "valid_value (IntVal b1 val) (IntegerStamp b l h d u) =
     (if b1 = b then
       valid_stamp (IntegerStamp b l h d u) \<and>
       take_bit b val = val \<and>
       (b \<turnstile> l \<le>j val) \<and> (b \<turnstile> val \<le>j h) \<and>
       (and (not val) d) = 0 \<and>
       (and val u) = val
      else False)" |
  (* "valid_value (FloatStamp b1 l h) (FloatVal b2 v) = ((b1 = b2) \<and> (v \<ge> l) \<and> (v \<le> h))" | *)
  "valid_value (ObjRef ref) (ObjectStamp klass exact nonNull alwaysNull) = 
     ((alwaysNull \<longrightarrow> ref = None) \<and> (ref=None \<longrightarrow> \<not> nonNull))" |
  "valid_value stamp val = False"
(* NOTE: we could allow for unsigned interpretations too, like this:
       (if l < 0
        then (l \<le> int_signed_value b val \<and> int_signed_value b val \<le> h)
        else (l \<le> int_unsigned_value b val \<and> int_unsigned_value b val \<le> h))
   but that is only necessary for handling unsigned long, so we take the
   simpler always-signed approach here.  In Java, the only unsigned stamps
   we see are for char, but they are 32-bit: IntegerStamp 32 0 65535.
*)
(* TODO: add the other stamps:
  | KlassPointerStamp (stp_nonNull: bool) (stp_alwaysNull: bool)
  | MethodCountersPointerStamp (stp_nonNull: bool) (stp_alwaysNull: bool)
  | MethodPointersStamp (stp_nonNull: bool) (stp_alwaysNull: bool)
  | RawPointerStamp (stp_nonNull: bool) (stp_alwaysNull: bool)
*)

(* A preferable wf_value definition
fun wf_value :: "Value \<Rightarrow> bool" where
  "wf_value (IntVal b v) = (0 < b \<and> b \<le> 64 \<and> take_bit b v = v 
    \<and> sint v \<le> snd (bit_bounds b)
    \<and> fst (bit_bounds b) \<le> sint v)" |
  "wf_value _ = False"
*)

definition wf_value :: "Value \<Rightarrow> bool" where
  "wf_value v = valid_value v (constantAsStamp v)"

lemma unfold_wf_value[simp]:
  "wf_value v \<Longrightarrow> valid_value v (constantAsStamp v)"
  by (simp add: wf_value_def)

declare [[linarith_split_limit=20]] (* TODO: worrying *)
fun compatible :: "Stamp \<Rightarrow> Stamp \<Rightarrow> bool" where
  "compatible (IntegerStamp b1 lo1 hi1 d1 u1) (IntegerStamp b2 lo2 hi2 d2 u2) =
     (b1 = b2 \<and> valid_stamp (IntegerStamp b1 lo1 hi1 d1 u1) \<and> valid_stamp (IntegerStamp b2 lo2 hi2 d2 u2))" |
  "compatible (VoidStamp) (VoidStamp) = True" |
  "compatible _ _ = False"
declare [[linarith_split_limit=9]]

fun stamp_under :: "Stamp \<Rightarrow> Stamp \<Rightarrow> bool" where
  "stamp_under (IntegerStamp b1 lo1 hi1 d1 u1) (IntegerStamp b2 lo2 hi2 d2 u2) = ((b1 = b2) \<and> (b1 \<turnstile> hi1 <j lo2))" |
  "stamp_under _ _ = False"

\<comment> \<open>
The most common type of stamp within the compiler (apart from the VoidStamp) is a 32 bit
integer stamp with an unrestricted range. We use @{text default_stamp} as it is a frequently used stamp.
\<close>
definition default_stamp :: "Stamp" where
  "default_stamp = (unrestricted_stamp (IntegerStamp 32 0 0 0 0))"

value "valid_value (IntVal 8 (255)) (IntegerStamp 8 (-128) 127 (mask 8) 0)"
value "default_stamp"
value "sint (min_int 32)"
value "255 \<le>s max_int 32"
value "min_int 32 \<le>s 255"
value "mask 32::int64"
value "and (not 255) (0::64 word) = 0"
value "((and 255 (not (mask 32)))::int64) = 0"
value "valid_stamp default_stamp"
value "valid_value (IntVal 32 (255)) default_stamp"

context includes bit_operations_syntax begin
value "bit (5::int64) 0"
value "bit (5::int64) 1"
value "bit (5::int64) 2"
value "(1::int64) AND (3::int64)"
value "(5::int64) AND (5::int64)"
value "(5::int64) OR (3::int64)"
value "(5::int64) OR (5::int64)"
value "(5::int64) XOR (3::int64)"
value "(5::int64) XOR (5::int64)"
value "(mask 2::int64)"
value "(mask 3::int64)"
value "(set_bit 2 5::int64)"
value "(set_bit 1 5::int64)"
value "(unset_bit 2 5::int64)"
value "(unset_bit 1 5::int64)"
value "(flip_bit 2 5::int64)"
value "(flip_bit 1 5::int64)"
value "(push_bit 1 1::int64)"
value "(push_bit 1 3::int64)"
value "(push_bit 2 1::int64)"
value "(drop_bit 1 5::int64)"
value "(drop_bit 1 7::int64)"
value "(drop_bit 2 5::int64)"
value "(take_bit 1 3::int64)"
value "(take_bit 2 3::int64)"
end
end
