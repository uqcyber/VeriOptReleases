theory NarrowPhase
  imports
    Common
begin

nitpick_params [sat_solver = smart, max_threads = 1, verbose=true]

(*
lemma eval_not_undef:
  "([m,p] \<turnstile> e \<mapsto> v) \<longrightarrow> v \<noteq> UndefVal"
  by (induction e; auto)
*)

section \<open>Optimizations for Narrow/Widen Nodes\<close>

text \<open>Our first goal in this section is to explore the known (fixed) bug
  in narrowing / widening within equality comparisons, in Issue 2011.\<close>

context
  includes bit_operations_syntax
begin


text \<open>Some of the CodeUtil methods from the GraalVM compiler"\<close>

(*
//    public static long signExtend(long value, int inputBits) {
//        if (inputBits < 64) {
//            return (value >>> inputBits - 1 & 1L) == 1L 
//                   ? value | -1L << inputBits 
//                   : value & ~(-1L << inputBits);
//        } else {
//            return value;
//        }
//    }
*)
definition CodeUtil_signExtend :: "int64 \<Rightarrow> nat \<Rightarrow> int64" where
  "CodeUtil_signExtend value inputBits =
    (if inputBits < 64
     then (if ((value >>> (inputBits - 1)) AND 1) = 1
          then value OR ((-1) << inputBits)
          else value AND NOT((-1) << inputBits))
     else value)"

(* TODO? prove that this is equal to: 
       (value << (64 - inputBits)) >>> (64 - inputBits)
*)

(* temporary version for 32-bit in and out. *)
definition CodeUtil_signExtend32 :: "int32 \<Rightarrow> nat \<Rightarrow> int32" where
  "CodeUtil_signExtend32 value inputBits =
    (if inputBits < 64
     then (if ((value >>> (inputBits - 1)) AND 1) = 1
          then value OR ((-1) << inputBits)
          else value AND NOT((-1) << inputBits))
     else value)"

(*
//     public static long zeroExtend(long value, int inputBits) {
//         return inputBits < 64 ? value & ~(-1L << inputBits) : value;
//     }
*)
definition CodeUtil_zeroExtend :: "int64 \<Rightarrow> nat \<Rightarrow> int64" where
  "CodeUtil_zeroExtend value inputBits =
    (if inputBits < 64
     then value AND NOT((-1) << inputBits)
     else value)"

(* temporary version for 32-bit in and out. *)
definition CodeUtil_zeroExtend32 :: "int32 \<Rightarrow> nat \<Rightarrow> int32" where
  "CodeUtil_zeroExtend32 value inputBits =
    (if inputBits < 64
     then value AND NOT((-1) << inputBits)
     else value)"

(*
//     public static long narrow(long value, int resultBits) {
//         long ret = value & mask(resultBits);
//         return signExtend(ret, resultBits);
//     }
*)
definition CodeUtil_narrow :: "int64 \<Rightarrow> nat \<Rightarrow> int64" where
  "CodeUtil_narrow value resultBits =
    signed_take_bit (resultBits - 1) (value AND mask resultBits)"

definition CodeUtil_narrow32 :: "int32 \<Rightarrow> nat \<Rightarrow> int32" where
  "CodeUtil_narrow32 value resultBits =
    signed_take_bit (resultBits - 1) (value AND mask resultBits)"

end

lemma dummy: "(0 :: int32) + 1 = 1"
  by simp


subsection \<open>Example tests of the CodeUtil narrow and widen operators\<close>

experiment begin
corollary "sint(CodeUtil_signExtend 0x00FF 64) = 255" by code_simp
corollary "sint(CodeUtil_signExtend 0x007F 8)  = 127" by code_simp
corollary "sint(CodeUtil_signExtend 0x00FF 8)  = -1" by code_simp
corollary "sint(CodeUtil_signExtend 0x0000 1)  = 0" by code_simp
corollary "sint(CodeUtil_signExtend 0x0001 1)  = -1" by code_simp

corollary "sint(CodeUtil_zeroExtend 0x00FF 64) = 255" by code_simp
corollary "sint(CodeUtil_zeroExtend 0x007F 8)  = 127" by code_simp
corollary "sint(CodeUtil_zeroExtend 0x00FF 8)  = 255" by code_simp
corollary "sint(CodeUtil_zeroExtend 0x0000 1)  = 0" by code_simp
corollary "sint(CodeUtil_zeroExtend 0x0001 1)  = 1" by code_simp

corollary "sint(CodeUtil_narrow 0xFFFF 8) = -1" by code_simp
corollary "sint(CodeUtil_narrow 0xFF7F 8) = 127" by code_simp
corollary "sint(CodeUtil_narrow 0x00FF 8) = -1" by code_simp
corollary "sint(CodeUtil_narrow 0x0000 1) = 0" by code_simp
corollary "sint(CodeUtil_narrow 0x0001 1) = -1" by code_simp
end


(* nitpick demo: gives kodkod warning:
    Kodkod warning: cannot launch SAT solver, falling back on "DefaultSAT4J" 

lemma "P \<longleftrightarrow> Q"
  nitpick
*)

phase Issue2011Phase 
  terminating size
begin

fun isDefaultForKind :: "Value \<Rightarrow> bool" where
  "isDefaultForKind (IntVal b val) = (val = 0)" |
  "isDefaultForKind _ = False"

value "not(-1 << 8 :: int32)"
value "mask 7 :: int32"

lemma shift_n_eq_bit_n:
  fixes val :: \<open>'a::len word\<close>
  shows "(and (val >>> n) 1 = 1) = bit val n"
  by (simp add: bit_iff_and_drop_bit_eq_1 shiftr_def)

declare [[show_types=true]]
lemma neg1_shift_eq_mask:
  fixes val :: \<open>'a::len word\<close>
  fixes n :: nat
  assumes "n < LENGTH('a)"
  assumes "0 < n"
  shows "((- 1 << n) :: 'a::len word) = not (mask n)" (is "?A = ?B")
  by (simp add: shiftl_def)

lemma take_bit_suc:
  fixes v :: int32
  assumes "\<not> bit v (n::nat)"
  shows "take_bit (Suc n::nat) v = take_bit (n::nat) v"
  by (smt (verit, best) assms bit_take_bit_iff le_eq_less_or_eq less_Suc_eq_le linorder_not_less
      signed_take_bit_eq_if_positive signed_take_bit_take_bit take_bit_signed_take_bit)

lemma narrow_reverse_pos:
  assumes 1: "and (val32 >>> 7) 1 \<noteq> 1"
  assumes pos: "\<not> bit val32 7"
  assumes 4: "revKonst = and konst (not (- 1 << 8))"
  assumes 5: "intval_narrow 32 8 (IntVal32 revKonst) = IntVal32 konst"
  shows "IntVal32 konst = intval_narrow 32 8 (IntVal32 val32)
        \<longleftrightarrow>
         revKonst = val32"
  oops

(* this is where the Issue2011 bug should appear. *)
lemma narrow_reverse_neg:
  assumes "and (val32 >>> 7) 1 = 1"
  assumes neg: "bit val32 7"  (* 8-bit val32 is negative *)
  assumes "val32 = 0xC0"     (* example value from bug report *)
  shows "IntVal 32 i32 = intval_narrow 32 8 (IntVal 32 val32)
        \<longleftrightarrow> 
         IntVal 32 (or i32 (- 1 << 8)) = (IntVal 32 val32)"
  oops


lemma unfold_ex_let: "(\<exists>x. x=E \<and> P) = (let x=E in P)"
  by force
  
lemma unfold_ex2_let: "(\<exists>x y. x=E \<and> P x y) = (let x=E in (\<exists>y. P x y))"
  by force

lemma unfold_ex2_ex_let: "(\<exists>y. (\<exists>x. (R x y \<and> y=E x \<and> Q x y)) \<and> P y) = (\<exists>x'. (let y=E x' in (R x' y \<and> Q x' y \<and> P y)))"
  by metis

lemma unfold_ex_bubble_out: "(P \<and> (\<exists>x. Q x) \<and> R) = (\<exists>x. (Q x \<and> P \<and> R))"
  by auto

(* TODO: make this more general, but still usable in unfolding?
lemma unfold_intval_eq32: 
  "((intval_equals (IntVal32 v1) v2 = intval_equals (IntVal32 v3) v4) \<and>
   (intval_equals (IntVal32 v1) v2 \<noteq> UndefVal))
   = ((v1 = un_IntVal32 v2) = (v3 = un_IntVal32 v4) \<and>
      is_IntVal32 v2 \<and> is_IntVal32 v4)" (is "?A = (?B = ?C \<and> ?I2 \<and> ?I4)")
  proof (intro iffI)
    assume ?A
    show "?B = ?C \<and> ?I2 \<and> ?I4"
      by (smt (verit, best) Value.sel(1) \<open>intval_equals (IntVal32 (v1::32 word)) (v2::Value) = intval_equals (IntVal32 (v3::32 word)) (v4::Value) \<and> intval_equals (IntVal32 v1) v2 \<noteq> UndefVal\<close> bool_to_val.elims intval_eq32 intval_eq32_simp zero_neq_one)
  next
    assume "?B = ?C \<and> ?I2 \<and> ?I4"
    show ?A
      by (smt (verit, best) Value.collapse(1) Value.disc(1) Value.discI(1) \<open>((v1::32 word) = un_IntVal32 (v2::Value)) = ((v3::32 word) = un_IntVal32 (v4::Value)) \<and> is_IntVal32 v2 \<and> is_IntVal32 v4\<close> bool_to_val.simps(1) bool_to_val.simps(2) intval_equals.simps(1))
  qed
*)

(* TODO: update!  use context assumptions about definedness to deduce int size
lemma eq_must_be_int32:
  assumes "intval_equals (IntVal32 a) b \<noteq> UndefVal"
  shows "(intval_equals (IntVal32 a) b = intval_equals (IntVal32 c) d)
         = ((a = un_IntVal32 b) \<longleftrightarrow> (c = un_IntVal32 d))"
proof (rule iffI)
  assume 1: "(intval_equals (IntVal32 a) b = intval_equals (IntVal32 c) d)"
  obtain bv where "b = IntVal32 bv" 
    using assms intval_eq32 is_IntVal32_def by blast 
  then show "(a = un_IntVal32 b) \<longleftrightarrow> (c = un_IntVal32 d)"
    using 1 assms intval_eq32 is_IntVal32_def by fastforce 
next
  assume 2: "(a = un_IntVal32 b) \<longleftrightarrow> (c = un_IntVal32 d)"
  then have 3: "bool_to_val (a = un_IntVal32 b) = bool_to_val (c = un_IntVal32 d)"
    by simp
  obtain bv where "b = IntVal32 bv" 
    using assms intval_eq32 is_IntVal32_def by blast
  then have "intval_equals (IntVal32 c) d \<noteq> UndefVal"
    using assms sorry
  then have "intval_equals (IntVal32 a) b = intval_equals (IntVal32 c) d"
    using 3 assms sorry
  
  then show "(intval_equals (IntVal32 a) b = intval_equals (IntVal32 c) d)"
    using 2 
    oops
*)

(* we first investigate the case of narrowing from 32 to 8 bits.
Input: Constant constant == ValueNode nonConstant
       ConvertNode convert = (ConvertNode) nonConstant;  // actually a NarrowNode
  TODO: add some of these side conditions:
  if isConstantConversionSupported(convert, view, smallestCompareWidth)
  ConstantNode newConstant = canonicalConvertConstant(constantReflection, metaAccess, 
                                      condition, convert, constant, view);
  i.e. {
     if (convert.preservesOrder(condition, constant, constantReflection)) {
        Constant reverseConverted = convert.reverse(constant, constantReflection);
              i.e. = table.getSignExtend().foldConstant(getResultBits(), getInputBits(), constant)
        if (reverseConverted != null && 
            convert.convert(reverseConverted, constantReflection).equals(constant))
                     i.e.  = narrow(reverseConverted) = constant
      return ConstantNode.forConstant(convert.getValue().stamp(view), reverseConverted, metaAccess);
     }
  if newConstant != null
  return newConstant == convert.getValue()
*)
optimization Issue2011_Bug:
  "((const (IntVal32 value)) eq
      (UnaryExpr (UnaryNarrow inBits outBits) expr))
   \<longmapsto>
   ((const (IntVal32 (CodeUtil_signExtend32 value outBits)))
      eq expr)
   when (inBits = 32 \<and> outBits = 8)"
  apply (rule impI)
  subgoal premises 1 
  unfolding le_expr_def unfold_evaltree bin_eval.simps unary_eval.simps
   apply (rule allI impI)+
  unfolding ex_neg_all_pos unfold_ex_bubble_out
  subgoal premises 2 for m p v x y ev
    apply (rule exI[of _ "IntVal32 (CodeUtil_signExtend32 value outBits)"];
           rule exI[of _ ev])
      unfolding CodeUtil_signExtend32_def 
 (*     apply (simp add: 1 2 unfold_intval_eq32)
      this gives two conjuncts, which are similar to above lemmas:
1. (and (value >>> (7::nat)) (1::32 word) = (1::32 word) \<longrightarrow>
     (value = un_IntVal32 (intval_narrow (32::nat) (8::nat) ev)) =
     (or value (- (1::32 word) << (8::nat)) = un_IntVal32 ev) \<and>
     is_IntVal32 (intval_narrow (32::nat) (8::nat) ev) \<and> is_IntVal32 ev)
2.  (and (value >>> (7::nat)) (1::32 word) \<noteq> (1::32 word) \<longrightarrow>
     (value = un_IntVal32 (intval_narrow (32::nat) (8::nat) ev)) =
     (and value (not (- (1::32 word) << (8::nat))) = un_IntVal32 ev) \<and>
     is_IntVal32 (intval_narrow (32::nat) (8::nat) ev) \<and> is_IntVal32 ev)
 *)
      print_facts
      oops


optimization Issue2011_Fix:
  "(BinaryExpr BinIntegerEquals
      (ConstantExpr (IntVal32 value))
      (UnaryExpr (UnaryNarrow inBits outBits) expr))
   \<longmapsto>
   (BinaryExpr BinIntegerEquals
      (ConstantExpr (IntVal32 (CodeUtil_zeroExtend32 value outBits)))
      expr)
   when (inBits = 32 \<and> outBits = 8)"
  apply (rule impI)
  subgoal premises 1 
  unfolding le_expr_def unfold_evaltree bin_eval.simps unary_eval.simps
   apply (rule allI impI)+
  unfolding ex_neg_all_pos unfold_ex_bubble_out
  subgoal premises 2 for m p v x y ev
      apply (rule exI[of _ "IntVal32 (CodeUtil_zeroExtend32 value outBits)"]; rule exI[of _ ev])
      unfolding CodeUtil_zeroExtend32_def 
(*      apply (simp add: 1 2 unfold_intval_eq32)
      apply (rule conjI)
 this gives two goals (first one is false, e.g. ev=0x100):
 1. (value = un_IntVal32 (intval_narrow (32::nat) (8::nat) ev)) =
    (and value (not (- (1::32 word) << (8::nat))) = un_IntVal32 ev)
 2. is_IntVal32 (intval_narrow (32::nat) (8::nat) ev) \<and> is_IntVal32 ev
*) 
      print_facts
      oops


  
(* other side-conditions in the code:
  NB. 'convert' and narrowNode are the unary narrow expr.

  !(narrowNode.getInputBits() > 32 && !constant.isDefaultForKind())
   smallestCompareWidth != null && 
     intStamp.getBits() >= smallestCompareWidth

  (convert.preservesOrder(condition, constant, constantReflection))
  // then calculate reverseConverted:
  (reverseConverted != null && convert.convert(reverseConverted, constantReflection).equals(constant))

  (ConstantExpr newConstant) is: 
    return ConstantNode.forConstant(convert.getValue().stamp(view), reverseConverted, metaAccess);
*)


(*

optimization e:
  "x * (const c) \<longmapsto> x << (const n) when (n = intval_log2 c \<and> in_bounds n 0 32)"
   apply unfold_optimization apply simp using e_intval
  using BinaryExprE ConstantExprE bin_eval.simps(2,7) sorry


  nitpick [unary_ints]
  nitpick [binary_ints, bits=16]
  But these give error: 
    Unsupported case: representation function on "Int.int"

+//   && supported   // ie. (convert.stamp as IntegerStamp).getBits() >= smallestCompareWidth
+//   && let value = ((PrimitiveConstant) konstant).asLong()
+//   && let narrow = convert
+//   && let inputBits = narrow.inputBits
# Ian: instead shift left then right
+//   && let reverseConverted = if (convert.inputBits < 64)
+//                             then if (value >>> inputBits - 1 & 1L) == 1L
+//                                  then value | -1L << inputBits
+//                                  else value & ~(-1L << inputBits)
+//                             else value
+//   && reverseConverted != null   // I don't think it can be null?
+//   && narrow.convert(reverseConverted, constantReflection).equals(konstant))
+//   && !GeneratePIC.getValue(options))
+//   && let newConstant = ConstantNode.forConstant(narrow.getValue().stamp(view), reverseConverted, metaAccess)
+//   && newConstant != null
*)

lemma negate_min32:
  fixes y :: int32
  assumes "y = (0x80000000 :: int32)"
  shows "-y = (0x80000000 :: int32)"
  using assms apply code_simp by force

lemma sub_min32:
  fixes y :: int32
  assumes "y = (0x80000000 :: int32)"
  shows "x - y = x + y"
  unfolding assms negate_min32 by simp 

end
