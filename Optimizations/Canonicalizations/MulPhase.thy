subsection \<open>MulNode Phase\<close>

theory MulPhase
  imports
    Common
    Proofs.StampEvalThms
begin

fun mul_size :: "IRExpr \<Rightarrow> nat" where
  "mul_size (UnaryExpr op e) = (mul_size e) + 2" |
  "mul_size (BinaryExpr BinMul x y) = ((mul_size x) + (mul_size y) + 2) * 2" |
  "mul_size (BinaryExpr op x y) = (mul_size x) + (mul_size y) + 2" |
  "mul_size (ConditionalExpr c t f) = (mul_size c) + (mul_size t) + (mul_size f) + 2" |
  "mul_size (ConstantExpr c) = 1" |
  "mul_size (ParameterExpr ind s) = 2" |
  "mul_size (LeafExpr nid s) = 2" |
  "mul_size (ConstantVar c) = 2" |
  "mul_size (VariableExpr x s) = 2"

phase MulNode
  terminating mul_size
begin

(* Word level proofs *)
lemma bin_eliminate_redundant_negative:
  "uminus (x :: 'a::len word) * uminus (y :: 'a::len word) = x * y"
  by simp

lemma bin_multiply_identity:
 "(x :: 'a::len word) * 1 = x"
  by simp

lemma bin_multiply_eliminate:
 "(x :: 'a::len word) * 0 = 0"
  by simp

lemma bin_multiply_negative:
 "(x :: 'a::len word) * uminus 1 = uminus x"
  by simp

lemma bin_multiply_power_2:
 "(x:: 'a::len word) * (2^j) = x << j"
  by simp

(* Helper *)
lemma take_bit64[simp]: 
  fixes w :: "int64"
  shows "take_bit 64 w = w"
proof -
  have "Nat.size w = 64"
    by (simp add: size64)
  then show ?thesis
    by (metis lt2p_lem mask_eq_iff take_bit_eq_mask verit_comp_simplify1(2) wsst_TYs(3))
qed

(* TODO: merge this with val_eliminate_redundant_negative *)
lemma mergeTakeBit:
  fixes a :: "nat"
  fixes b c :: "64 word"
  shows "take_bit a (take_bit a (b) * take_bit a (c)) = 
         take_bit a (b * c)" 
 by (smt (verit, ccfv_SIG) take_bit_mult take_bit_of_int unsigned_take_bit_eq word_mult_def)

(* Value level proofs *)
lemma val_eliminate_redundant_negative:
  assumes "val[-x * -y] \<noteq> UndefVal"
  shows "val[-x * -y] = val[x * y]"
  by (cases x; cases y; auto simp: mergeTakeBit)

lemma val_multiply_neutral:
  assumes "x = new_int b v"
  shows "val[x * (IntVal b 1)] = x"
  by (auto simp: assms)

lemma val_multiply_zero:
  assumes "x = new_int b v"
  shows "val[x * (IntVal b 0)] = IntVal b 0"
  by (simp add: assms)

lemma val_multiply_negative:
  assumes "x = new_int b v"
  shows "val[x * -(IntVal b 1)] = val[-x]" 
  unfolding assms(1) apply auto[1]
  by (metis bin_multiply_negative mergeTakeBit take_bit_minus_one_eq_mask)

(* x * 2^i = x << i*)
lemma val_MulPower2:
  fixes i :: "64 word"
  assumes "y = IntVal 64 (2 ^ unat(i))"
  and     "0 < i"
  and     "i < 64"
  and     "val[x * y] \<noteq> UndefVal"
  shows   "val[x * y] = val[x << IntVal 64 i]"
  using assms apply (cases x; cases y; auto)
    subgoal premises p for x2
    proof -
      have 63: "(63 :: int64) = mask 6"
        by eval
      then have "(2::int) ^ 6 = 64"
        by eval
      then have "uint i < (2::int) ^ 6"
        by (metis linorder_not_less lt2p_lem of_int_numeral p(4) word_2p_lem word_of_int_2p 
            wsst_TYs(3))
      then have "and i (mask 6) = i"
        using mask_eq_iff by blast
      then show "x2 << unat i = x2 << unat (and i (63::64 word))"
        by (auto simp: 63)
    qed
  by presburger

(*  x * ((2 ^ j) + 1) = (x << j) + x  *)
lemma val_MulPower2Add1:
  fixes i :: "64 word"
  assumes "y = IntVal 64 ((2 ^ unat(i)) + 1)"
  and     "0 < i"
  and     "i < 64"
  and     "val_to_bool(val[IntVal 64 0 < x])"
  and     "val_to_bool(val[IntVal 64 0 < y])"
  shows   "val[x * y] = val[(x << IntVal 64 i) + x]"
  using assms apply (cases x; cases y; auto)
    subgoal premises p for x2
  proof -
    have 63: "(63 :: int64) = mask 6"
      by eval
    then have "(2 :: int) ^ 6 = 64"
      by eval
    then have "and i (mask 6) = i"
      by (simp add: less_mask_eq p(6))
    then have "x2 * (2 ^ unat i + 1) = (x2 * (2 ^ unat i)) + x2"
      by (simp add: distrib_left)
    then show "x2 * (2 ^ unat i + 1) = x2 << unat (and i 63) + x2"
      by (simp add: "63" \<open>and i (mask 6) = i\<close>)
    qed 
  using val_to_bool.simps(2) by presburger

(*  x * ((2 ^ j) - 1) = (x << j) - x  *)
lemma val_MulPower2Sub1:
  fixes i :: "64 word"
  assumes "y = IntVal 64 ((2 ^ unat(i)) - 1)"
  and     "0 < i"
  and     "i < 64"
  and     "val_to_bool(val[IntVal 64 0 < x])"
  and     "val_to_bool(val[IntVal 64 0 < y])"
  shows   "val[x * y] = val[(x << IntVal 64 i) - x]"
  using assms apply (cases x; cases y; auto)
    subgoal premises p for x2
  proof -
    have 63: "(63 :: int64) = mask 6"
      by eval
    then have "(2 :: int) ^ 6 = 64"
      by eval
    then have "and i (mask 6) = i"
      by (simp add: less_mask_eq p(6))
    then have "x2 * (2 ^ unat i - 1) = (x2 * (2 ^ unat i)) - x2"
      by (simp add: right_diff_distrib')
    then show "x2 * (2 ^ unat i - 1) = x2 << unat (and i 63) - x2"
      by (simp add: "63" \<open>and i (mask 6) = i\<close>)
    qed 
  using val_to_bool.simps(2) by presburger

(* Value level helpers *)
lemma val_distribute_multiplication:
  assumes "x = IntVal b xx \<and> q = IntVal b qq \<and> a = IntVal b aa"
  assumes "val[x * (q + a)] \<noteq> UndefVal"
  assumes "val[(x * q) + (x * a)] \<noteq> UndefVal"
  shows "val[x * (q + a)] = val[(x * q) + (x * a)]"
  using assms apply (cases x; cases q; cases a; auto) 
  by (metis (no_types, opaque_lifting) distrib_left new_int.elims new_int_unused_bits_zero
      mergeTakeBit)

lemma val_distribute_multiplication64:
  assumes "x = new_int 64 xx \<and> q = new_int 64 qq \<and> a = new_int 64 aa"
  shows "val[x * (q + a)] = val[(x * q) + (x * a)]"
  using assms apply (cases x; cases q; cases a; auto) 
  using distrib_left by blast

(*  x * ((2 ^ j) + (2 ^ k)) = (x << j) + (x << k)  *)
lemma val_MulPower2AddPower2:
  fixes i j :: "64 word"
  assumes "y = IntVal 64 ((2 ^ unat(i)) + (2 ^ unat(j)))"
  and     "0 < i"
  and     "0 < j"
  and     "i < 64"
  and     "j < 64"
  and     "x = new_int 64 xx"
  shows   "val[x * y] = val[(x << IntVal 64 i) + (x << IntVal 64 j)]"
  proof -
    have 63: "(63 :: int64) = mask 6"
      by eval
    then have "(2 :: int) ^ 6 = 64"
      by eval
    then have n: "IntVal 64 ((2 ^ unat(i)) + (2 ^ unat(j))) = 
             val[(IntVal 64 (2 ^ unat(i))) + (IntVal 64 (2 ^ unat(j)))]"
       (* x * (2^i + 2^j)*)
      by auto
   then have 1: "val[x * ((IntVal 64 (2 ^ unat(i))) + (IntVal 64 (2 ^ unat(j))))] = 
                 val[(x * IntVal 64 (2 ^ unat(i))) + (x * IntVal 64 (2 ^ unat(j)))]"
      (* (x * 2^i) + (x * 2^j)*)
     using assms val_distribute_multiplication64 by simp 
   then have 2: "val[(x * IntVal 64 (2 ^ unat(i)))] = val[x << IntVal 64 i]"
     by (metis (no_types, opaque_lifting) Value.distinct(1) intval_mul.simps(1) new_int.simps
         new_int_bin.simps assms(2,4,6) val_MulPower2)
   then show "?thesis" 
     by (metis (no_types, lifting) "1" Value.distinct(1) n intval_mul.simps(1) new_int_bin.elims
         new_int.simps val_MulPower2 assms(1,3,5,6))
   qed

thm_oracles val_MulPower2AddPower2

(* Exp-level proofs *)
lemma exp_multiply_zero_64:
  shows "exp[x * (const (IntVal b 0))] \<ge> ConstantExpr (IntVal b 0)"
  apply auto[1]
  subgoal premises p for m p xa
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p(1) by auto
    obtain xb xvv where xvv: "xv = IntVal xb xvv"
      by (metis evalDet p(1,2) xv evaltree_not_undef intval_is_null.cases intval_mul.simps(3,4,5))
    then have evalNotUndef: "val[xv * (IntVal b 0)] \<noteq> UndefVal"
      using p evalDet xv by blast
    then have mulUnfold: "val[xv * (IntVal b 0)] = IntVal xb (take_bit xb (xvv*0))"
      by (metis new_int.simps xvv new_int_bin.simps intval_mul.simps(1))
    then have isZero: "val[xv * (IntVal b 0)] = (new_int xb (0))"
      by (simp add: mulUnfold)
    then have eq: "(IntVal b 0) = (IntVal xb (0))"
      by (metis Value.distinct(1) intval_mul.simps(1) mulUnfold new_int_bin.elims xvv)
    then show ?thesis
      using evalDet isZero p(1,3) xv by fastforce
  qed
  done

lemma exp_multiply_neutral:
 "exp[x * (const (IntVal b 1))] \<ge> x"
  apply auto[1]
  subgoal premises p for m p xa
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p(1) by auto
    obtain xb xvv where xvv: "xv = IntVal xb xvv"
      by (smt (z3) evalDet intval_mul.elims p(1,2) xv)
    then have evalNotUndef: "val[xv * (IntVal b 1)] \<noteq> UndefVal"
      using p evalDet xv by blast
    then have mulUnfold: "val[xv * (IntVal b 1)] = IntVal xb (take_bit xb (xvv*1))"
      by (metis new_int.simps xvv new_int_bin.simps intval_mul.simps(1))
    then show ?thesis
      by (metis bin_multiply_identity evalDet eval_unused_bits_zero p(1) xv xvv)
  qed
  done

thm_oracles exp_multiply_neutral

lemma exp_multiply_negative:
 "exp[x * -(const (IntVal b 1))] \<ge> exp[-x]"
  apply auto[1]
  subgoal premises p for m p xa
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p(1) by auto
    obtain xb xvv where xvv: "xv = IntVal xb xvv"
      by (metis array_length.cases evalDet evaltree_not_undef intval_mul.simps(3,4,5) p(1,2) xv)
    then have rewrite: "val[-(IntVal b 1)] = IntVal b (mask b)"
      by simp
    then have evalNotUndef: "val[xv * -(IntVal b 1)] \<noteq> UndefVal"
      unfolding rewrite using evalDet p(1,2) xv by blast
    then have mulUnfold: "val[xv * (IntVal b (mask b))] =
                          (if xb=b then (IntVal xb (take_bit xb (xvv*(mask xb)))) else UndefVal)"
      by (metis new_int.simps xvv new_int_bin.simps intval_mul.simps(1))
    then have sameWidth: "xb=b"
      by (metis evalNotUndef rewrite)
    then show ?thesis
      by (metis evalDet eval_unused_bits_zero new_int.elims p(1,2) rewrite unary_eval.simps(2) xvv
          unfold_unary val_multiply_negative xv)
  qed
  done

lemma exp_MulPower2:
  fixes i :: "64 word"
  assumes "y = ConstantExpr (IntVal 64 (2 ^ unat(i)))"
  and     "0 < i"
  and     "i < 64"
  and     "exp[x > (const IntVal b 0)]"
  and     "exp[y > (const IntVal b 0)]"
  shows "exp[x * y] \<ge> exp[x << ConstantExpr (IntVal 64 i)]"
  using ConstantExprE equiv_exprs_def unfold_binary assms by fastforce

lemma exp_MulPower2Add1:
  fixes i :: "64 word"
  assumes "y = ConstantExpr (IntVal 64 ((2 ^ unat(i)) + 1))"
  and     "0 < i"
  and     "i < 64"
  and     "exp[x > (const IntVal b 0)]"
  and     "exp[y > (const IntVal b 0)]"
  shows   "exp[x * y] \<ge> exp[(x << ConstantExpr (IntVal 64 i)) + x]"
  using ConstantExprE equiv_exprs_def unfold_binary assms by fastforce

lemma exp_MulPower2Sub1:
  fixes i :: "64 word"
  assumes "y = ConstantExpr (IntVal 64 ((2 ^ unat(i)) - 1))"
  and     "0 < i"
  and     "i < 64"
  and     "exp[x > (const IntVal b 0)]"
  and     "exp[y > (const IntVal b 0)]"
  shows   "exp[x * y] \<ge> exp[(x << ConstantExpr (IntVal 64 i)) - x]"
  using ConstantExprE equiv_exprs_def unfold_binary assms by fastforce

lemma exp_MulPower2AddPower2:
  fixes i j :: "64 word"
  assumes "y = ConstantExpr (IntVal 64 ((2 ^ unat(i)) + (2 ^ unat(j))))"
  and     "0 < i"
  and     "0 < j"
  and     "i < 64"
  and     "j < 64"
  and     "exp[x > (const IntVal b 0)]"
  and     "exp[y > (const IntVal b 0)]"
  shows   "exp[x * y] \<ge> exp[(x << ConstantExpr (IntVal 64 i)) + (x << ConstantExpr (IntVal 64 j))]"
  using ConstantExprE equiv_exprs_def unfold_binary assms by fastforce

(* Exp level helpers *)

lemma greaterConstant:
  fixes a b :: "64 word"
  assumes "a > b"
  and     "y = ConstantExpr (IntVal 32 a)"
  and     "x = ConstantExpr (IntVal 32 b)"
  shows "exp[BinaryExpr BinIntegerLessThan y x] \<ge> exp[const (new_int 32 0)]"
  using assms 
  apply simp unfolding equiv_exprs_def apply auto 
  sorry

lemma exp_distribute_multiplication:
  assumes "stamp_expr x = IntegerStamp b xl xh"
  assumes "stamp_expr q = IntegerStamp b ql qh"
  assumes "stamp_expr y = IntegerStamp b yl yh"
  assumes "wf_stamp x"
  assumes "wf_stamp q"
  assumes "wf_stamp y"
  shows "exp[(x * q) + (x * y)] \<ge> exp[x * (q + y)]" 
  apply auto[1]
  subgoal premises p for m p xa qa xb aa
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p by simp
    obtain qv where qv: "[m,p] \<turnstile> q \<mapsto> qv"
      using p by simp
    obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> yv"
      using p by simp
    then obtain xvv where xvv: "xv = IntVal b xvv"
      by (metis assms(1,4) valid_int wf_stamp_def xv)
    then obtain qvv where qvv: "qv = IntVal b qvv"
      by (metis qv valid_int assms(2,5) wf_stamp_def)
    then obtain yvv where yvv: "yv = IntVal b yvv"
      by (metis yv valid_int assms(3,6) wf_stamp_def)
    then have rhsDefined: "val[xv * (qv + yv)] \<noteq> UndefVal"
      by (simp add: xvv qvv)
    have "val[xv * (qv + yv)] = val[(xv * qv) + (xv * yv)]"
      using val_distribute_multiplication by (simp add: yvv qvv xvv) 
    then show ?thesis
      by (metis bin_eval.simps(1,3) BinaryExpr p(1,2,3,5,6) qv xv evalDet yv qvv Value.distinct(1)
          yvv intval_add.simps(1))
   qed
  done

text \<open>Optimisations\<close>

optimization EliminateRedundantNegative: "-x * -y \<longmapsto> x * y"
  apply auto[1]
  by (metis BinaryExpr val_eliminate_redundant_negative bin_eval.simps(3))

optimization MulNeutral: "x * y \<longmapsto> x when IsConstantValue y x 1"
  using exp_multiply_neutral by blast

optimization MulEliminator: "x * y \<longmapsto> forZero x when IsConstantValue y x 0"
  using exp_multiply_zero_64 by fast

optimization MulNegate: "x * -y \<longmapsto> -x when IsConstantValue y x 1"
  using exp_multiply_negative by presburger

fun isNonZero :: "Stamp \<Rightarrow> bool" where
  "isNonZero (IntegerStamp b lo hi) = (lo > 0)" |
  "isNonZero _ = False"

lemma isNonZero_defn:
  assumes "isNonZero (stamp_expr x)"
  assumes "wf_stamp x"
  shows "([m, p] \<turnstile> x \<mapsto> v) \<longrightarrow> (\<exists>vv b. (v = IntVal b vv \<and> val_to_bool val[(IntVal b 0) < v]))"
  apply (rule impI) subgoal premises eval
proof -
  obtain b lo hi where xstamp: "stamp_expr x = IntegerStamp b lo hi"
    by (meson isNonZero.elims(2) assms)
  then obtain vv where vdef: "v = IntVal b vv"
    by (metis assms(2) eval valid_int wf_stamp_def)
  have "lo > 0"
    using assms(1) xstamp by force
  then have signed_above: "int_signed_value b vv > 0"
    using assms eval vdef xstamp wf_stamp_def by fastforce
  have "take_bit b vv = vv"
    using eval eval_unused_bits_zero vdef by auto
  then have "vv > 0"
    by (metis bit_take_bit_iff int_signed_value.simps signed_eq_0_iff take_bit_of_0 signed_above
        verit_comp_simplify1(1) word_gt_0 signed_take_bit_eq_if_positive)
  then show ?thesis
    using vdef signed_above by simp
qed
  done

lemma ExpIntBecomesIntValArbitrary:
  assumes "stamp_expr x = IntegerStamp b xl xh"
  assumes "wf_stamp x"
  assumes "valid_value v (IntegerStamp b xl xh)"
  assumes "[m,p] \<turnstile> x \<mapsto> v"
  shows "\<exists>xv. v = IntVal b xv"
  using assms by (simp add: IRTreeEvalThms.valid_value_elims(3))

(*
optimization MulPower2: "x * y \<longmapsto> x << const (IntVal 64 i) 
                              when (i > 0 \<and> stamp_expr x = IntegerStamp 64 xl xh \<and> wf_stamp x \<and>
                                    64 > i \<and>
                                    y = exp[const (IntVal 64 (2 ^ unat(i)))])"
   apply simp apply (rule impI; (rule allI)+; rule impI)
  subgoal premises eval for m p v
proof -
  obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> xv"
    using eval(2) by blast
  then have notUndef: "xv \<noteq> UndefVal"
    by (simp add: evaltree_not_undef)
  obtain xb xvv where xvv: "xv = IntVal xb xvv"
    by (metis wf_stamp_def eval(1) ExpIntBecomesIntValArbitrary xv)
  then have w64: "xb = 64"
    by (metis wf_stamp_def intval_bits.simps ExpIntBecomesIntValArbitrary xv eval(1))
  obtain yv where yv: "[m, p] \<turnstile> y \<mapsto> yv"
    using eval(1,2) by blast
  then have lhs: "[m, p] \<turnstile> exp[x * y] \<mapsto> val[xv * yv]"
    by (metis bin_eval.simps(3) eval(1,2) evalDet unfold_binary xv)
  have "[m, p] \<turnstile> exp[const (IntVal 64 i)] \<mapsto> val[(IntVal 64 i)]"
    by (smt (verit, ccfv_SIG) ConstantExpr constantAsStamp.simps(1) eval_bits_1_64 take_bit64 xv xvv
        validStampIntConst wf_value_def valid_value.simps(1) w64)
  then have rhs: "[m, p] \<turnstile> exp[x << const (IntVal 64 i)] \<mapsto> val[xv << (IntVal 64 i)]"
    by (metis Value.simps(5) bin_eval.simps(10) intval_left_shift.simps(1) new_int.simps xv xvv 
        evaltree.BinaryExpr)
  have "val[xv * yv] = val[xv << (IntVal 64 i)]"
    by (metis ConstantExprE eval(1) evaltree_not_undef lhs yv val_MulPower2)
  then show ?thesis
    by (metis eval(1,2) evalDet lhs rhs)
qed
  done

optimization MulPower2Add1: "x * y \<longmapsto> (x << const (IntVal 64 i)) + x 
                              when (i > 0 \<and> stamp_expr x = IntegerStamp 64 xl xh \<and> wf_stamp x \<and>
                                    64 > i \<and>
                                    y = ConstantExpr (IntVal 64 ((2 ^ unat(i)) + 1)) )"
   apply simp apply (rule impI; (rule allI)+; rule impI)
  subgoal premises p for m p v
  proof -
    obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> xv"
      using p by fast
    then obtain xvv where xvv: "xv = IntVal 64 xvv"
      using p by (metis valid_int wf_stamp_def)
    obtain yv where yv: "[m, p] \<turnstile> y \<mapsto> yv"
      using p by blast
    have ygezero: "y > ConstantExpr (IntVal 64 0)"
      using greaterConstant p wf_value_def sorry 
    then have 1: "0 < i \<and>
                  i < 64 \<and> 
                  y = ConstantExpr (IntVal 64 ((2 ^ unat(i)) + 1))"
      using p by blast
    then have lhs: "[m, p] \<turnstile> exp[x * y] \<mapsto> val[xv * yv]"
      by (metis bin_eval.simps(3) evalDet p(2) xv yv unfold_binary)
    then have "[m, p] \<turnstile> exp[const (IntVal 64 i)] \<mapsto> val[(IntVal 64 i)]"
      by (metis wf_value_def verit_comp_simplify1(2) zero_less_numeral ConstantExpr take_bit64
          constantAsStamp.simps(1) validStampIntConst valid_value.simps(1))
    then have rhs2: "[m, p] \<turnstile> exp[x << const (IntVal 64 i)] \<mapsto> val[xv << (IntVal 64 i)]"
      by (metis Value.simps(5) bin_eval.simps(10) intval_left_shift.simps(1) new_int.simps xv xvv 
          evaltree.BinaryExpr)
    then have rhs: "[m, p] \<turnstile> exp[(x << const (IntVal 64 i)) + x] \<mapsto> val[(xv << (IntVal 64 i)) + xv]" 
       by (metis (no_types, lifting) intval_add.simps(1) bin_eval.simps(1) Value.simps(5) xv xvv
           evaltree.BinaryExpr intval_left_shift.simps(1) new_int.simps)
     then have simple: "val[xv * (IntVal 64 (2 ^ unat(i)))] = val[xv << (IntVal 64 i)]"
       using val_MulPower2 sorry
     then have "val[xv * yv] = val[(xv << (IntVal 64 i)) + xv]"
       using val_MulPower2Add1 sorry
     then show ?thesis
       by (metis "1" evalDet lhs p(2) rhs)
  qed
  done

(* Need to prove exp_MulPower2Sub1 *)
optimization MulPower2Sub1: "x * y \<longmapsto> (x << const (IntVal 64 i)) - x 
                              when (i > 0 \<and> stamp_expr x = IntegerStamp 64 xl xh \<and> wf_stamp x \<and>
                                    64 > i \<and>
                                    y = ConstantExpr (IntVal 64 ((2 ^ unat(i)) - 1)) )"
   apply simp apply (rule impI; (rule allI)+; rule impI)
  subgoal premises p for m p v
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p by fast
    then obtain xvv where xvv: "xv = IntVal 64 xvv"
      using p by (metis valid_int wf_stamp_def)
    obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> yv"
      using p by blast
    have ygezero: "y > ConstantExpr (IntVal 64 0)" sorry
    then have 1: "0 < i \<and>
                  i < 64 \<and> 
                  y = ConstantExpr (IntVal 64 ((2 ^ unat(i)) - 1))"
      using p by blast
    then have lhs: "[m, p] \<turnstile> exp[x * y] \<mapsto> val[xv * yv]"
      by (metis bin_eval.simps(3) evalDet p(2) xv yv unfold_binary)
    then have "[m, p] \<turnstile> exp[const (IntVal 64 i)] \<mapsto> val[(IntVal 64 i)]"
      by (metis wf_value_def verit_comp_simplify1(2) zero_less_numeral ConstantExpr take_bit64
          constantAsStamp.simps(1) validStampIntConst valid_value.simps(1))
    then have rhs2: "[m, p] \<turnstile> exp[x << const (IntVal 64 i)] \<mapsto> val[xv << (IntVal 64 i)]"
      by (metis Value.simps(5) bin_eval.simps(10) intval_left_shift.simps(1) new_int.simps xv xvv 
          evaltree.BinaryExpr)
    then have rhs: "[m, p] \<turnstile> exp[(x << const (IntVal 64 i)) - x] \<mapsto> val[(xv << (IntVal 64 i)) - xv]" 
      using "1" equiv_exprs_def ygezero yv by fastforce
    then have "val[xv * yv] = val[(xv << (IntVal 64 i)) - xv]"
       using "1" exp_MulPower2Sub1 ygezero sorry 
     then show ?thesis
      by (metis evalDet lhs p(1) p(2) rhs)
  qed
done
*)

end (* End of MulPhase *)

end (* End of file *)
