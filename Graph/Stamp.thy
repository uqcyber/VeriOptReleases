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
  | IntegerStamp (stp_bits: nat) (stpi_lower: int) (stpi_upper: int)
  (* | FloatStamp (stp_bits: nat) (stpf_lower: float) (stpf_upper: float) *)
  | KlassPointerStamp (stp_nonNull: bool) (stp_alwaysNull: bool)
  | MethodCountersPointerStamp (stp_nonNull: bool) (stp_alwaysNull: bool)
  | MethodPointersStamp (stp_nonNull: bool) (stp_alwaysNull: bool)
  | ObjectStamp (stp_type: string) (stp_exactType: bool) (stp_nonNull: bool) (stp_alwaysNull: bool)
  | RawPointerStamp (stp_nonNull: bool) (stp_alwaysNull: bool)
  | IllegalStamp


text \<open>To help with supporting masks in future, this constructor allows masks but ignores them.\<close>
abbreviation IntegerStampM :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int64 \<Rightarrow> int64 \<Rightarrow> Stamp" where
  "IntegerStampM b lo hi down up \<equiv> IntegerStamp b lo hi"


fun is_stamp_empty :: "Stamp \<Rightarrow> bool" where
  "is_stamp_empty (IntegerStamp b lower upper) = (upper < lower)" |
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
fun valid_stamp :: "Stamp \<Rightarrow> bool" where
  "valid_stamp (IntegerStamp bits lo hi) = 
     (0 < bits \<and> bits \<le> 64 \<and>
     fst (bit_bounds bits) \<le> lo \<and> lo \<le> snd (bit_bounds bits) \<and>
     fst (bit_bounds bits) \<le> hi \<and> hi \<le> snd (bit_bounds bits))" |
  "valid_stamp s = True"

(* Note: we could support 32/64-bit unsigned values by relaxing this definition to:
     (is_stamp_empty (IntegerStamp bits lo hi)
     \<or> lo < 0 \<and> fst (bit_bounds bits) \<le> lo \<and> lo \<le> hi \<and> hi \<le> snd (bit_bounds bits)
     \<or> 0 \<le> lo \<and> lo \<le> hi \<and> hi < 2 ^ bits))"
*)

experiment begin
corollary "bit_bounds 1 = (-1, 0)" by simp  (* this matches the compiler stamps. *)
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
  "unrestricted_stamp (IntegerStamp bits lower upper) = (IntegerStamp bits (fst (bit_bounds bits)) (snd (bit_bounds bits)))" | 
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
  "empty_stamp (IntegerStamp bits lower upper) = (IntegerStamp bits (snd (bit_bounds bits)) (fst (bit_bounds bits)))" |
  (* "empty_stamp (FloatStamp bits lower upper) = (FloatStamp bits pos_infinity neg_infinity)" | *)
  "empty_stamp (KlassPointerStamp nonNull alwaysNull) = (KlassPointerStamp nonNull alwaysNull)" |
  "empty_stamp (MethodCountersPointerStamp nonNull alwaysNull) = (MethodCountersPointerStamp nonNull alwaysNull)" |
  "empty_stamp (MethodPointersStamp nonNull alwaysNull) = (MethodPointersStamp nonNull alwaysNull)" |
  "empty_stamp (ObjectStamp type exactType nonNull alwaysNull) = (ObjectStamp '''' True True False)" |
  "empty_stamp stamp = IllegalStamp"


\<comment> \<open>Calculate the meet stamp of two stamps\<close>
fun meet :: "Stamp \<Rightarrow> Stamp \<Rightarrow> Stamp" where
  "meet VoidStamp VoidStamp = VoidStamp" |
  "meet (IntegerStamp b1 l1 u1) (IntegerStamp b2 l2 u2) = (
    if b1 \<noteq> b2 then IllegalStamp else 
    (IntegerStamp b1 (min l1 l2) (max u1 u2))
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
  "join (IntegerStamp b1 l1 u1) (IntegerStamp b2 l2 u2) = (
    if b1 \<noteq> b2 then IllegalStamp else 
    (IntegerStamp b1 (max l1 l2) (min u1 u2))
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
  "asConstant (IntegerStamp b l h) = (if l = h then IntVal b (word_of_int l) else UndefVal)" |
  "asConstant _ = UndefVal"

\<comment> \<open>Determine if two stamps never have value overlaps i.e. their join is empty\<close>
fun alwaysDistinct :: "Stamp \<Rightarrow> Stamp \<Rightarrow> bool" where
  "alwaysDistinct stamp1 stamp2 = is_stamp_empty (join stamp1 stamp2)"

\<comment> \<open>Determine if two stamps must always be the same value i.e. two equal constants\<close>
fun neverDistinct :: "Stamp \<Rightarrow> Stamp \<Rightarrow> bool" where
  "neverDistinct stamp1 stamp2 = (asConstant stamp1 = asConstant stamp2 \<and> asConstant stamp1 \<noteq> UndefVal)"

fun constantAsStamp :: "Value \<Rightarrow> Stamp" where
  "constantAsStamp (IntVal b v) = (IntegerStamp b (int_signed_value b v) (int_signed_value b v))" |
  "constantAsStamp (ObjRef (None)) = ObjectStamp '''' False False True" |
  "constantAsStamp (ObjRef (Some n)) = ObjectStamp '''' False True False" |
  (* TODO: float *)
  "constantAsStamp _ = IllegalStamp"

\<comment> \<open>Define when a runtime value is valid for a stamp.
    The stamp bounds must be valid, and val must be zero-extended.\<close>
fun valid_value :: "Value \<Rightarrow> Stamp \<Rightarrow> bool" where
  "valid_value (IntVal b1 val) (IntegerStamp b l h) =
     (if b1 = b then
       valid_stamp (IntegerStamp b l h) \<and>
       take_bit b val = val \<and>
       l \<le> int_signed_value b val \<and> int_signed_value b val \<le> h
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

fun compatible :: "Stamp \<Rightarrow> Stamp \<Rightarrow> bool" where
  "compatible (IntegerStamp b1 lo1 hi1) (IntegerStamp b2 lo2 hi2) =
     (b1 = b2 \<and> valid_stamp (IntegerStamp b1 lo1 hi1) \<and> valid_stamp (IntegerStamp b2 lo2 hi2))" |
  "compatible (VoidStamp) (VoidStamp) = True" |
  "compatible _ _ = False"

fun stamp_under :: "Stamp \<Rightarrow> Stamp \<Rightarrow> bool" where
  "stamp_under (IntegerStamp b1 lo1 hi1) (IntegerStamp b2 lo2 hi2) = (hi1 < lo2)" |
  "stamp_under _ _ = False"

\<comment> \<open>
The most common type of stamp within the compiler (apart from the VoidStamp) is a 32 bit
integer stamp with an unrestricted range. We use @{text default_stamp} as it is a frequently used stamp.
\<close>
definition default_stamp :: "Stamp" where
  "default_stamp = (unrestricted_stamp (IntegerStamp 32 0 0))"

value "valid_value (IntVal 8 (255)) (IntegerStamp 8 (-128) 127)"
end
