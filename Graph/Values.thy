section \<open>Operator Semantics\<close>

theory Values
  imports
    JavaLong
begin

text \<open>
In order to properly implement the IR semantics we first introduce
a type that represents runtime values.
These runtime values represent the full range of primitive types
currently allowed by our semantics, ranging from basic integer types
to object references and arrays.

Note that Java supports 64, 32, 16, 8 signed ints, plus 1 bit (boolean)
ints, and char is 16-bit unsigned.
E.g. an 8-bit stamp has a default range of -128..+127.
And a 1-bit stamp has a default range of -1..0, surprisingly.

During calculations the smaller sizes are sign-extended to 32 bits, but explicit 
widening nodes will do that, so most binary calculations should see equal input sizes.

An object reference is an option type where the @{term None} object reference
points to the static fields. This is examined more closely in our
definition of the heap.
\<close>

type_synonym objref = "nat option"
type_synonym length = "nat"

datatype (discs_sels) Value  =
  UndefVal |
  (* IntVal32 "32 word" | *)  (* also used for 16, 8, and 1-bit (boolean) values *)
  (* IntVal64 "64 word" | *)
  (* IntVal IntType int64 |  -- all types smaller than 64 bits are zero-extended *)
  (* or widths: IntVal (ibits:IntWidth) (ival:int64) | *)
  (* or just:   IntVal (ibits:nat) (ival:int64) ? *)
  (* or         IntVal IntWord where IntWord = (nat,int64)? *)
  (* IntValv2 nat bool int64 |   bits, signed, word *)
  IntVal iwidth int64 | (* bits and word because we cannot know sign until do compare! *)
  (* FloatVal float | not supported *)
  ObjRef objref |
  ObjStr string |
  ArrayVal length "Value list"  (* Length characteristic not currently enforced in Value list *)

fun intval_bits :: "Value \<Rightarrow> nat" where
  "intval_bits (IntVal b v) = b"

fun intval_word :: "Value \<Rightarrow> int64" where
  "intval_word (IntVal b v) = v"

text \<open>Converts an integer word into a Java value.\<close>
fun new_int :: "iwidth \<Rightarrow> int64 \<Rightarrow> Value" where
  "new_int b w = IntVal b (take_bit b w)"

text \<open>Converts an integer word into a Java value, iff the two types are equal.\<close>
fun new_int_bin :: "iwidth \<Rightarrow> iwidth \<Rightarrow> int64 \<Rightarrow> Value" where
  "new_int_bin b1 b2 w = (if b1=b2 then new_int b1 w else UndefVal)"

fun array_length :: "Value \<Rightarrow> Value" where
  "array_length (ArrayVal len list) = new_int 32 (word_of_nat len)"

fun wf_bool :: "Value \<Rightarrow> bool" where
  "wf_bool (IntVal b w) = (b = 1)" |
  "wf_bool _ = False" 

fun val_to_bool :: "Value \<Rightarrow> bool" where
  "val_to_bool (IntVal b val) = (if val = 0 then False else True)" |
  "val_to_bool val = False"

fun bool_to_val :: "bool \<Rightarrow> Value" where
  "bool_to_val True = (IntVal 32 1)" |
  "bool_to_val False = (IntVal 32 0)"

text \<open>Converts an Isabelle bool into a Java value, iff the two types are equal.\<close>
fun bool_to_val_bin :: "iwidth \<Rightarrow> iwidth \<Rightarrow> bool \<Rightarrow> Value" where
  "bool_to_val_bin t1 t2 b = (if t1 = t2 then bool_to_val b else UndefVal)"

(* Deprecated - just for backwards compatibility. *)
fun is_int_val :: "Value \<Rightarrow> bool" where
  "is_int_val v = is_IntVal v"

lemma neg_one_value[simp]: "new_int b (neg_one b) = IntVal b (mask b)"
  by simp

lemma neg_one_signed[simp]: 
  assumes "0 < b"
  shows "int_signed_value b (neg_one b) = -1"
  using assms apply auto[1]
  by (metis (no_types, lifting) Suc_pred diff_Suc_1 signed_take_take_bit assms signed_minus_1
      int_signed_value.simps mask_eq_take_bit_minus_one signed_take_bit_of_minus_1)

lemma word_unsigned:
  shows "\<forall> b1 v1. (IntVal b1 (word_of_int (int_unsigned_value b1 v1))) = IntVal b1 v1"
  by simp

subsection \<open>Arithmetic Operators\<close>

text \<open>
We need to introduce arithmetic operations which agree with the JVM.

Within the JVM, bytecode arithmetic operations are performed on 32
or 64 bit integers, unboxing where appropriate.

The following collection of intval functions correspond to the JVM
arithmetic operations.  We merge the 32 and 64 bit operations into
a single function, even though the stamp of each IRNode tells us
exactly what the bit widths will be.  These merged functions 
make it easier to do the instantiation of Value as 'plus', etc.
It might be worse for reasoning, because it could cause more case analysis,
but this does not seem to be a problem in practice.
\<close>

(* Corresponds to JVM iadd and ladd instructions. *)
fun intval_add :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_add (IntVal b1 v1) (IntVal b2 v2) = 
    (if b1 = b2 then IntVal b1 (take_bit b1 (v1+v2)) else UndefVal)" |
  "intval_add _ _ = UndefVal"

(* Corresponds to JVM isub and lsub instructions. *)
fun intval_sub :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_sub (IntVal b1 v1) (IntVal b2 v2) = new_int_bin b1 b2 (v1-v2)" |
  "intval_sub _ _ = UndefVal"

(* Corresponds to JVM imul and lmul instructions. *)
fun intval_mul :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_mul (IntVal b1 v1) (IntVal b2 v2) = new_int_bin b1 b2 (v1*v2)" |
  "intval_mul _ _ = UndefVal"

(* Java division rounds towards 0, so we use sdiv, not div. *)
(* TODO: find a signed division operator in the Word library? *)
fun intval_div :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_div (IntVal b1 v1) (IntVal b2 v2) = 
        new_int_bin b1 b2 (word_of_int
           ((int_signed_value b1 v1) sdiv (int_signed_value b2 v2)))" |
  "intval_div _ _ = UndefVal"

(* Java % is a modulo operator that can give negative results, since div rounds towards 0. *)
fun intval_mod :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_mod (IntVal b1 v1) (IntVal b2 v2) = 
        new_int_bin b1 b2 (word_of_int
           ((int_signed_value b1 v1) smod (int_signed_value b2 v2)))" |
  "intval_mod _ _ = UndefVal"

(* Corresponds to Math.multiplyHigh(L,L) and ExactMath.multiplyHigh(I,I) *)
fun intval_mul_high :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_mul_high (IntVal b1 v1) (IntVal b2 v2) = (
    if (b1 = b2 \<and> b1 = 64) then (
      if (((int_signed_value b1 v1) < 0) \<or> ((int_signed_value b2 v2) < 0))
         then (

       let x1 = (v1 >> 32)              in
       let x2 = (and v1 4294967295)     in
       let y1 = (v2 >> 32)              in
       let y2 = (and v2 4294967295)     in
       let z2 = (x2 * y2)               in
       let t  = (x1 * y2 + (z2 >>> 32)) in
       let z1 = (and t 4294967295)      in
       let z0 = (t >> 32)               in
       let z1 = (z1 + (x2 * y1))        in

       let result = (x1 * y1 + z0 + (z1 >> 32)) in

       (new_int b1 result)
      ) else (

       let x1 = (v1 >>> 32)             in
       let y1 = (v2 >>> 32)             in
       let x2 = (and v1 4294967295)     in
       let y2 = (and v2 4294967295)     in
       let A  = (x1 * y1)               in
       let B  = (x2 * y2)               in
       let C  = ((x1 + x2) * (y1 + y2)) in
       let K  = (C - A - B)             in

       let result = ((((B >>> 32) + K) >>> 32) + A) in

       (new_int b1 result)
      )
    ) else (
      if (b1 = b2 \<and> b1 = 32) then (

      let newv1 = (word_of_int (int_signed_value b1 v1)) in
      let newv2 = (word_of_int (int_signed_value b1 v2)) in
      let r = (newv1 * newv2)                            in

      let result = (r >> 32) in

       (new_int b1 result)
      ) else UndefVal)
   )" |
  "intval_mul_high _ _ = UndefVal"

fun intval_reverse_bytes :: "Value \<Rightarrow> Value" where
  "intval_reverse_bytes (IntVal b1 v1) = (new_int b1 (reverseBytes_fun v1 b1 0))" |
  "intval_reverse_bytes _ = UndefVal"

(* Corresponds to Integer.bitCount(I) and Long.bitCount(L) *)
fun intval_bit_count :: "Value \<Rightarrow> Value" where
  "intval_bit_count (IntVal b1 v1) = (new_int 32 (word_of_nat (bitCount_fun v1 64)))" |
  "intval_bit_count _ = UndefVal"

fun intval_negate :: "Value \<Rightarrow> Value" where
  "intval_negate (IntVal t v) = new_int t (- v)" |
  "intval_negate _ = UndefVal"

fun intval_abs :: "Value \<Rightarrow> Value" where
  "intval_abs (IntVal t v) = new_int t (if int_signed_value t v < 0 then - v else v)" |
  "intval_abs _ = UndefVal"

text \<open>TODO: clarify which widths this should work on: just 1-bit or all?\<close>
fun intval_logic_negation :: "Value \<Rightarrow> Value" where
  "intval_logic_negation (IntVal b v) = new_int b (logic_negate v)" |
  "intval_logic_negation _ = UndefVal"

subsection \<open>Bitwise Operators\<close>

fun intval_and :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_and (IntVal b1 v1) (IntVal b2 v2) = new_int_bin b1 b2 (and v1 v2)" |
  "intval_and _ _ = UndefVal"

fun intval_or :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_or (IntVal b1 v1) (IntVal b2 v2) = new_int_bin b1 b2 (or v1 v2)" |
  "intval_or _ _ = UndefVal"

fun intval_xor :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_xor (IntVal b1 v1) (IntVal b2 v2) = new_int_bin b1 b2 (xor v1 v2)" |
  "intval_xor _ _ = UndefVal"

fun intval_not :: "Value \<Rightarrow> Value" where
  "intval_not (IntVal t v) = new_int t (not v)" |
  "intval_not _ = UndefVal"

subsection \<open>Comparison Operators\<close>

fun intval_short_circuit_or :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_short_circuit_or (IntVal b1 v1) (IntVal b2 v2) = bool_to_val_bin b1 b2 (((v1 \<noteq> 0) \<or> (v2 \<noteq> 0)))" |
  "intval_short_circuit_or _ _ = UndefVal"

fun intval_equals :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_equals (IntVal b1 v1) (IntVal b2 v2) = bool_to_val_bin b1 b2 (v1 = v2)" |
  "intval_equals _ _ = UndefVal"

fun intval_less_than :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_less_than (IntVal b1 v1) (IntVal b2 v2) = 
    bool_to_val_bin b1 b2 (int_signed_value b1 v1 < int_signed_value b2 v2)" |
  "intval_less_than _ _ = UndefVal"

fun intval_below :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_below (IntVal b1 v1) (IntVal b2 v2) = bool_to_val_bin b1 b2 (v1 < v2)" |
  "intval_below _ _ = UndefVal"

fun intval_conditional :: "Value \<Rightarrow> Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_conditional cond tv fv = (if (val_to_bool cond) then tv else fv)"

fun intval_is_null :: "Value \<Rightarrow> Value" where
  "intval_is_null (ObjRef (v)) = (if (v=(None)) then bool_to_val True else bool_to_val False)" |
  "intval_is_null _ = UndefVal"

fun intval_test :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_test (IntVal b1 v1) (IntVal b2 v2) = bool_to_val_bin b1 b2 ((and v1 v2) = 0)" |
  "intval_test _ _ = UndefVal"

(* Corresponds to Integer.compareUnsigned and Long.compareUnsigned *)
fun intval_normalize_compare :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_normalize_compare (IntVal b1 v1) (IntVal b2 v2) =
   (if (b1 = b2) then new_int 32 (if (v1 < v2) then -1 else (if (v1 = v2) then 0 else 1))
                 else UndefVal)" |
  "intval_normalize_compare _ _ = UndefVal"

(* Array-related operators and helper functions *)

(* Yoinked from https://www.isa-afp.org/browser_info/Isabelle2012/HOL/List-Index/List_Index.html*)
fun find_index :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "find_index _ [] = 0" |
  "find_index v (x # xs) = (if (x=v) then 0 else find_index v xs + 1)"

definition default_values :: "Value list" where
  "default_values = [new_int 32 0, new_int 64 0, ObjRef None]"

definition short_types_32 :: "string list" where
  "short_types_32 = [''[Z'', ''[I'', ''[C'', ''[B'', ''[S'']"

definition short_types_64 :: "string list" where
  "short_types_64 = [''[J'']"

fun default_value :: "string \<Rightarrow> Value" where
  "default_value n = (if (find_index n short_types_32) < (length short_types_32)
                      then (default_values!0) else
                     (if (find_index n short_types_64) < (length short_types_64)
                      then (default_values!1)
                      else (default_values!2)))"

fun populate_array :: "nat \<Rightarrow> Value list \<Rightarrow> string \<Rightarrow> Value list" where
  "populate_array len a s = (if (len = 0) then (a)
                             else (a @ (populate_array (len-1) [default_value s] s)))"

fun intval_new_array :: "Value \<Rightarrow> string \<Rightarrow> Value" where
  "intval_new_array (IntVal b1 v1) s = (ArrayVal (nat (int_signed_value b1 v1))
                                        (populate_array (nat (int_signed_value b1 v1)) [] s))" |
  "intval_new_array _ _ = UndefVal"

fun intval_load_index :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_load_index (ArrayVal len cons) (IntVal b1 v1) = (if (v1 \<ge> (word_of_nat len)) then (UndefVal)
                                                          else (cons!(nat (int_signed_value b1 v1))))" |
  "intval_load_index _ _ = UndefVal"

fun intval_store_index :: "Value \<Rightarrow> Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_store_index (ArrayVal len cons) (IntVal b1 v1) val =
                      (if (v1 \<ge> (word_of_nat len)) then (UndefVal)
                        else (ArrayVal len (list_update cons (nat (int_signed_value b1 v1)) (val))))" |
  "intval_store_index _ _ _ = UndefVal"

lemma intval_equals_result:
  assumes "intval_equals v1 v2 = r"
  assumes "r \<noteq> UndefVal"
  shows "r = IntVal 32 0 \<or> r = IntVal 32 1"
proof -
  obtain b1 i1 where i1: "v1 = IntVal b1 i1"
    by (metis assms intval_bits.elims intval_equals.simps(2,3,4,5))
  obtain b2 i2 where i2: "v2 = IntVal b2 i2"
    by (smt (z3) assms intval_equals.elims)
  then have "b1 = b2"
    by (metis i1 assms bool_to_val_bin.elims intval_equals.simps(1))
  then show ?thesis
    using assms(1) bool_to_val.elims i1 i2 by auto
qed

subsection \<open>Narrowing and Widening Operators\<close>

text \<open>Note: we allow these operators to have inBits=outBits, because the Graal compiler
  also seems to allow that case, even though it should rarely / never arise in practice.\<close>

text \<open>Some sanity checks that $take\_bit N$ and $signed\_take\_bit (N-1)$ match up as expected.\<close>
corollary "sint (signed_take_bit 0 (1 :: int32)) = -1" by code_simp
corollary "sint (signed_take_bit 7 ((256 + 128) :: int64)) = -128" by code_simp
corollary "sint (take_bit 7 ((256 + 128 + 64) :: int64)) = 64" by code_simp
corollary "sint (take_bit 8 ((256 + 128 + 64) :: int64)) = 128 + 64" by code_simp

fun intval_narrow :: "nat \<Rightarrow> nat \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_narrow inBits outBits (IntVal b v) =
     (if inBits = b \<and> 0 < outBits \<and> outBits \<le> inBits \<and> inBits \<le> 64
      then new_int outBits v
      else UndefVal)" |
  "intval_narrow _ _ _ = UndefVal"

fun intval_sign_extend :: "nat \<Rightarrow> nat \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_sign_extend inBits outBits (IntVal b v) =
     (if inBits = b \<and> 0 < inBits \<and> inBits \<le> outBits \<and> outBits \<le> 64
      then new_int outBits (signed_take_bit (inBits - 1) v)
      else UndefVal)" |
  "intval_sign_extend _ _ _ = UndefVal"

fun intval_zero_extend :: "nat \<Rightarrow> nat \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_zero_extend inBits outBits (IntVal b v) =
     (if inBits = b \<and> 0 < inBits \<and> inBits \<le> outBits \<and> outBits \<le> 64
      then new_int outBits (take_bit inBits v)
      else UndefVal)" |
  "intval_zero_extend _ _ _ = UndefVal"

text \<open>Some well-formedness results to help reasoning about narrowing and widening operators\<close>

lemma intval_narrow_ok:
  assumes "intval_narrow inBits outBits val \<noteq> UndefVal"
  shows "0 < outBits \<and> outBits \<le> inBits \<and> inBits \<le> 64 \<and> outBits \<le> 64 \<and>
        is_IntVal val \<and>
        intval_bits val = inBits"
  using assms apply (cases val; auto) apply (meson le_trans)+ by presburger

lemma intval_sign_extend_ok:
  assumes "intval_sign_extend inBits outBits val \<noteq> UndefVal"
  shows "0 < inBits \<and>
        inBits \<le> outBits \<and> outBits \<le> 64 \<and>
        is_IntVal val \<and>
        intval_bits val = inBits"
  by (metis intval_bits.simps intval_sign_extend.elims is_IntVal_def assms)

lemma intval_zero_extend_ok:
  assumes "intval_zero_extend inBits outBits val \<noteq> UndefVal"
  shows "0 < inBits \<and>
        inBits \<le> outBits \<and> outBits \<le> 64 \<and>
        is_IntVal val \<and>
        intval_bits val = inBits"
  by (metis intval_bits.simps intval_zero_extend.elims is_IntVal_def assms)

subsection \<open>Bit-Shifting Operators\<close>

text \<open>Note that Java shift operators use unary numeric promotion, unlike other binary 
  operators, which use binary numeric promotion (see the Java language reference manual).
  This means that the left-hand input determines the output size, while the 
  right-hand input can be any size.\<close>

fun shift_amount :: "iwidth \<Rightarrow> int64 \<Rightarrow> nat" where
  "shift_amount b val = unat (and val (if b = 64 then 0x3F else 0x1f))"

fun intval_left_shift :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_left_shift (IntVal b1 v1) (IntVal b2 v2) = new_int b1 (v1 << shift_amount b1 v2)" |
  "intval_left_shift _ _ = UndefVal"

text \<open>Signed shift is more complex, because we sometimes have to insert 1 bits
  at the correct point, which is at b1 bits.\<close>
fun intval_right_shift :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_right_shift (IntVal b1 v1) (IntVal b2 v2) = 
     (let shift = shift_amount b1 v2 in
      let ones = and (mask b1) (not (mask (b1 - shift) :: int64)) in
      (if int_signed_value b1 v1 < 0
       then new_int b1 (or ones (v1 >>> shift))
       else new_int b1 (v1 >>> shift)))" |
  "intval_right_shift _ _ = UndefVal"

fun intval_uright_shift :: "Value \<Rightarrow> Value \<Rightarrow> Value" where
  "intval_uright_shift (IntVal b1 v1) (IntVal b2 v2) = new_int b1 (v1 >>> shift_amount b1 v2)" |
  "intval_uright_shift _ _ = UndefVal"

subsubsection \<open>Examples of Narrowing / Widening Functions\<close>

experiment begin
corollary "intval_narrow 32 8 (IntVal 32 (256 + 128)) = IntVal 8 128" by simp
corollary "intval_narrow 32 8 (IntVal 32 (-2)) = IntVal 8 254" by simp
corollary "intval_narrow 32 1 (IntVal 32 (-2)) = IntVal 1 0"    by simp
corollary "intval_narrow 32 1 (IntVal 32 (-3)) = IntVal 1 1" by simp

(* now test some 64 bit inputs and outputs *)
corollary "intval_narrow 32 8 (IntVal 64 (-2)) = UndefVal" by simp
corollary "intval_narrow 64 8 (IntVal 32 (-2)) = UndefVal" by simp
corollary "intval_narrow 64 8 (IntVal 64 254) = IntVal 8 254" by simp
corollary "intval_narrow 64 8 (IntVal 64 (256+127)) = IntVal 8 127" by simp
corollary "intval_narrow 64 64 (IntVal 64 (-2)) = IntVal 64 (-2)" by simp
end

experiment begin
corollary "intval_sign_extend 8 32 (IntVal 8 (256 + 128)) = IntVal 32 (2^32 - 128)" by simp
corollary "intval_sign_extend 8 32 (IntVal 8 (-2)) = IntVal 32 (2^32 - 2)" by simp
corollary "intval_sign_extend 1 32 (IntVal 1 (-2)) = IntVal 32 0"    by simp
corollary "intval_sign_extend 1 32 (IntVal 1 (-3)) = IntVal 32 (mask 32)" by simp

(* now test some 64 bit inputs and outputs *)
corollary "intval_sign_extend 8 32 (IntVal 64 254) = UndefVal" by simp
corollary "intval_sign_extend 8 64 (IntVal 32 254) = UndefVal" by simp
corollary "intval_sign_extend 8 64 (IntVal 8 254) = IntVal 64 (-2)" by simp
corollary "intval_sign_extend 32 64 (IntVal 32 (2^32 - 2)) = IntVal 64 (-2)" by simp
corollary "intval_sign_extend 64 64 (IntVal 64 (-2)) = IntVal 64 (-2)" by simp
end

experiment begin
corollary "intval_zero_extend 8 32 (IntVal 8 (256 + 128)) = IntVal 32 128" by simp
corollary "intval_zero_extend 8 32 (IntVal 8 (-2)) = IntVal 32 254" by simp
corollary "intval_zero_extend 1 32 (IntVal 1 (-1)) = IntVal 32 1"   by simp
corollary "intval_zero_extend 1 32 (IntVal 1 (-2)) = IntVal 32 0"   by simp

(* now test some 64 bit inputs and outputs *)
corollary "intval_zero_extend 8 32 (IntVal 64 (-2)) = UndefVal" by simp
corollary "intval_zero_extend 8 64 (IntVal 64 (-2)) = UndefVal" by simp
corollary "intval_zero_extend 8 64 (IntVal 8 254) = IntVal 64 254" by simp
corollary "intval_zero_extend 32 64 (IntVal 32 (2^32 - 2)) = IntVal 64 (2^32 - 2)" by simp
corollary "intval_zero_extend 64 64 (IntVal 64 (-2)) = IntVal 64 (-2)" by simp
end

experiment begin
corollary "intval_right_shift (IntVal 8 128) (IntVal 8 0) = IntVal 8 128" by eval
corollary "intval_right_shift (IntVal 8 128) (IntVal 8 1) = IntVal 8 192" by eval
corollary "intval_right_shift (IntVal 8 128) (IntVal 8 2) = IntVal 8 224" by eval
corollary "intval_right_shift (IntVal 8 128) (IntVal 8 8) = IntVal 8 255" by eval
corollary "intval_right_shift (IntVal 8 128) (IntVal 8 31) = IntVal 8 255" by eval
end

(* ========================================================================
   Commutative and Associative results.  (Not used yet).
   ======================================================================== *)

(* commutative rules to be used when needed. *)
lemma intval_add_sym:
  shows "intval_add a b = intval_add b a"
  by (induction a; induction b; auto simp: add.commute)

(* view dependency graph of code definitions:
code_deps intval_add
*)
(* print all code definitions used by intval_add:
code_thms intval_add
*)

(* Some example tests. *)
lemma "intval_add (IntVal 32 (2^31-1)) (IntVal 32 (2^31-1)) = IntVal 32 (2^32 - 2)"
  by eval
lemma "intval_add (IntVal 64 (2^31-1)) (IntVal 64 (2^31-1)) = IntVal 64 4294967294"
  by eval

end