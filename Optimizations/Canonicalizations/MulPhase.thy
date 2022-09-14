theory MulPhase
  imports
    Common
    Proofs.StampEvalThms
begin

section \<open>Optimizations for Mul Nodes\<close>

phase MulNode
  terminating size
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
lemma testt:
  fixes a :: "nat"
  fixes b c :: "64 word"
  shows "take_bit a (take_bit a (b) * take_bit a (c)) = 
         take_bit a (b * c)" 
 by (smt (verit, ccfv_SIG) take_bit_mult take_bit_of_int unsigned_take_bit_eq word_mult_def)


(* Value level proofs *)
lemma val_eliminate_redundant_negative:
  assumes "val[-x * -y] \<noteq> UndefVal"
  shows "val[-x * -y] = val[x * y]"
  using assms apply (cases x; cases y; auto)
  using testt by auto

lemma val_multiply_neutral:
  assumes "x = new_int b v"
  shows "val[x] * (IntVal b 1) = val[x]"
  using assms times_Value_def by force

lemma val_multiply_zero:
  assumes "x = new_int b v"
  shows "val[x] * (IntVal b 0) = IntVal b 0"
  using assms by (simp add: times_Value_def)

lemma val_multiply_negative:
  assumes "x = new_int b v"
  shows "x * intval_negate (IntVal b 1) = intval_negate x"
  using assms times_Value_def
  by (smt (verit) Value.disc(1) Value.inject(1) add.inverse_neutral intval_negate.simps(1) 
      is_IntVal_def mask_0 mask_eq_take_bit_minus_one new_int.elims of_bool_eq(2) take_bit_dist_neg 
      take_bit_of_1 val_eliminate_redundant_negative val_multiply_neutral val_multiply_zero 
      verit_minus_simplify(4) zero_neq_one)

(* x * 2^i = x << i*)
lemma val_MulPower2:
  fixes i :: "64 word"
  assumes "y = IntVal 64 (2 ^ unat(i))"
  and     "0 < i"
  and     "i < 64"
  and     "val[x * y] \<noteq> UndefVal"
  shows   "x * y = val[x << IntVal 64 i]"
  using assms apply (cases x; cases y; auto)
    apply (simp add: times_Value_def)
    subgoal premises p for x2
    proof -
      have 63: "(63 :: int64) = mask 6"
        by eval
      then have "(2::int) ^ 6 = 64"
        by eval
      then have "uint i < (2::int) ^ 6"
        by (metis linorder_not_less lt2p_lem of_int_numeral p(4) size64 word_2p_lem word_of_int_2p wsst_TYs(3))
      then have "and i (mask 6) = i"
        using mask_eq_iff by blast
      then show "x2 << unat i = x2 << unat (and i (63::64 word))"
        unfolding 63
        by force
    qed
    done

(*  x * ((2 ^ j) + 1) = (x << j) + x  *)
lemma val_MulPower2Add1:
  fixes i :: "64 word"
  assumes "y = IntVal 64 ((2 ^ unat(i)) + 1)"
  and     "0 < i"
  and     "i < 64"
  and     "val_to_bool(val[IntVal 64 0 < x])"
  and     "val_to_bool(val[IntVal 64 0 < y])"
  shows   "x * y = val[(x << IntVal 64 i) + x]"
  using assms apply (cases x; cases y; auto)
    apply (simp add: times_Value_def)
    subgoal premises p for x2
  proof -
    have 63: "(63 :: int64) = mask 6"
      by eval
    then have "(2::int) ^ 6 = 64"
      by eval
    then have "and i (mask 6) = i"
      using mask_eq_iff by (simp add: less_mask_eq p(6))
    then have "x2 * ((2::64 word) ^ unat i + (1::64 word)) = (x2 * ((2::64 word) ^ unat i)) + x2"
      by (simp add: distrib_left)
    then show "x2 * ((2::64 word) ^ unat i + (1::64 word)) = x2 << unat (and i (63::64 word)) + x2"
      by (simp add: "63" \<open>and (i::64 word) (mask (6::nat)) = i\<close>)
    qed 
  done


(*  x * ((2 ^ j) - 1) = (x << j) - x  *)
lemma val_MulPower2Sub1:
  fixes i :: "64 word"
  assumes "y = IntVal 64 ((2 ^ unat(i)) - 1)"
  and     "0 < i"
  and     "i < 64"
  and     "val_to_bool(val[IntVal 64 0 < x])"
  and     "val_to_bool(val[IntVal 64 0 < y])"
  shows   "x * y = val[(x << IntVal 64 i) - x]"
  using assms apply (cases x; cases y; auto)
    apply (simp add: times_Value_def)
    subgoal premises p for x2
  proof -
    have 63: "(63 :: int64) = mask 6"
      by eval
    then have "(2::int) ^ 6 = 64"
      by eval
    then have "and i (mask 6) = i"
      using mask_eq_iff by (simp add: less_mask_eq p(6))
    then have "x2 * ((2::64 word) ^ unat i - (1::64 word)) = (x2 * ((2::64 word) ^ unat i)) - x2"
      by (simp add: right_diff_distrib')
    then show "x2 * ((2::64 word) ^ unat i - (1::64 word)) = x2 << unat (and i (63::64 word)) - x2"
      by (simp add: "63" \<open>and (i::64 word) (mask (6::nat)) = i\<close>)
    qed 
  done

(* Helper *)
lemma val_distribute_multiplication:
  assumes "x = new_int 64 xx \<and> q = new_int 64 qq \<and> a = new_int 64 aa"
  shows "val[x * (q + a)] = val[(x * q) + (x * a)]"
  apply (cases x; cases q; cases a; auto) using distrib_left assms by auto


(*  x * ((2 ^ j) + (2 ^ k)) = (x << j) + (x << k)  *)
lemma val_MulPower2AddPower2:
  fixes i j :: "64 word"
  assumes "y = IntVal 64 ((2 ^ unat(i)) + (2 ^ unat(j)))"
  and     "0 < i"
  and     "0 < j"
  and     "i < 64"
  and     "j < 64"
  and     "x = new_int 64 xx"
  shows   "x * y = val[(x << IntVal 64 i) + (x << IntVal 64 j)]"
  using assms
  proof -
    have 63: "(63 :: int64) = mask 6"
      by eval
    then have "(2::int) ^ 6 = 64"
      by eval
    then have n: "IntVal 64 ((2 ^ unat(i)) + (2 ^ unat(j))) = 
           val[(IntVal 64 (2 ^ unat(i))) + (IntVal 64 (2 ^ unat(j)))]"
       (* x * (2^i + 2^j)*)
      using assms by (cases i; cases j; auto) 
   then have 1: "val[x * ((IntVal 64 (2 ^ unat(i))) + (IntVal 64 (2 ^ unat(j))))] = 
           val[(x * IntVal 64 (2 ^ unat(i))) + (x * IntVal 64 (2 ^ unat(j)))]"
      (* (x * 2^i) + (x * 2^j)*)
     using assms val_distribute_multiplication val_MulPower2 by simp 
   then have 2: "val[(x * IntVal 64 (2 ^ unat(i)))] = val[x << IntVal 64 i]"
     using assms val_MulPower2
     by (metis (full_types) Value.distinct(1) intval_mul.simps(1) new_int.simps new_int_bin.simps times_Value_def)
    then show "?thesis"
       by (metis (full_types) "1" Value.distinct(1) assms(1) assms(3) assms(5) assms(6) intval_mul.simps(1) n new_int.simps new_int_bin.elims times_Value_def val_MulPower2)
   qed 

 thm_oracles val_MulPower2AddPower2

(* Exp-level proofs *)
lemma exp_multiply_zero_64:
 "exp[x * (const (IntVal 64 0))] \<ge> ConstantExpr (IntVal 64 0)"
  using val_multiply_zero apply auto 
  using Value.inject(1) constantAsStamp.simps(1) int_signed_value_bounds intval_mul.elims 
        mult_zero_right new_int.simps new_int_bin.simps nle_le numeral_eq_Suc take_bit_of_0 
        unfold_const valid_stamp.simps(1) valid_value.simps(1) zero_less_Suc
  by (smt (verit))

lemma exp_multiply_neutral:
 "exp[x * (const (IntVal b 1))] \<ge> x"
  using val_multiply_neutral apply auto
  by (smt (verit) Value.inject(1) eval_unused_bits_zero intval_mul.elims mult.right_neutral new_int.elims new_int_bin.elims)

thm_oracles exp_multiply_neutral

lemma exp_MulPower2:
  fixes i :: "64 word"
  assumes "y = ConstantExpr (IntVal 64 (2 ^ unat(i)))"
  and     "0 < i"
  and     "i < 64"
  and     "exp[x > (const IntVal b 0)]"
  and     "exp[y > (const IntVal b 0)]"
  shows "exp[x * y] \<ge> exp[x << ConstantExpr (IntVal 64 i)]"
  using assms apply simp using val_MulPower2
  by (metis ConstantExprE equiv_exprs_def unfold_binary)


(* Optimizations *)
optimization EliminateRedundantNegative: "-x * -y \<longmapsto> x * y"
   apply auto using val_eliminate_redundant_negative bin_eval.simps(2)
  by (metis BinaryExpr)

(* Need to prove exp_multiply_neutral *)
optimization MulNeutral: "x * ConstantExpr (IntVal b 1) \<longmapsto> x"
  using exp_multiply_neutral by blast

optimization MulEliminator: "x * ConstantExpr (IntVal b 0) \<longmapsto> const (IntVal b 0)"
  apply auto using val_multiply_zero
  using Value.inject(1) constantAsStamp.simps(1) int_signed_value_bounds intval_mul.elims 
        mult_zero_right new_int.simps new_int_bin.simps take_bit_of_0 unfold_const 
        valid_stamp.simps(1) valid_value.simps(1) 
  by (smt (verit))


optimization MulNegate: "x * -(const (IntVal b 1)) \<longmapsto> -x"
  defer
  apply auto using val_multiply_negative
  apply (smt (verit) Value.distinct(1) Value.sel(1) add.inverse_inverse intval_mul.elims 
      intval_negate.simps(1) mask_eq_take_bit_minus_one new_int.simps new_int_bin.simps 
      take_bit_dist_neg times_Value_def unary_eval.simps(2) unfold_unary 
      val_eliminate_redundant_negative)
  sorry (* termination *)

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
    using assms
    by (meson isNonZero.elims(2))
  then obtain vv where vdef: "v = IntVal b vv"
    by (metis assms(2) eval valid_int wf_stamp_def)
  have "lo > 0"
    using assms(1) xstamp by force
  then have signed_above: "int_signed_value b vv > 0"
    using assms unfolding wf_stamp_def
    using eval vdef xstamp by fastforce
  have "take_bit b vv = vv"
    using eval eval_unused_bits_zero vdef by auto
  then have "vv > 0"
    using signed_above
    by (metis bit_take_bit_iff int_signed_value.simps not_less_zero signed_eq_0_iff signed_take_bit_eq_if_positive take_bit_0 take_bit_of_0 verit_comp_simplify1(1) word_gt_0)
  then show ?thesis
    using vdef using signed_above
    by simp
qed
  done

(* Need to prove exp_MulPower2 *)
optimization MulPower2: "x * y \<longmapsto> x << const (IntVal 64 i) 
                              when (i > 0 \<and> 
                                    64 > i \<and>
                                    y = exp[const (IntVal 64 (2 ^ unat(i)))])"
   defer
   apply simp apply (rule impI; (rule allI)+; rule impI)
  subgoal premises eval for m p v
proof -
  obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> xv"
    using eval(2) by blast
  then obtain xvv where xvv: "xv = IntVal 64 xvv"
    using eval
    using ConstantExprE bin_eval.simps(2) evalDet intval_bits.simps intval_mul.elims new_int_bin.simps unfold_binary 
    by (smt (verit))
  obtain yv where yv: "[m, p] \<turnstile> y \<mapsto> yv"
    using eval(1) eval(2) by blast
  then have lhs: "[m, p] \<turnstile> exp[x * y] \<mapsto> val[xv * yv]"
    by (metis bin_eval.simps(2) eval(1) eval(2) evalDet unfold_binary xv)
  have "[m, p] \<turnstile> exp[const (IntVal 64 i)] \<mapsto> val[(IntVal 64 i)]"
    by (smt (verit, ccfv_SIG) ConstantExpr constantAsStamp.simps(1) eval_bits_1_64 take_bit64 validStampIntConst valid_value.simps(1) xv xvv)
  then have rhs: "[m, p] \<turnstile> exp[x << const (IntVal 64 i)] \<mapsto> val[xv << (IntVal 64 i)]"
    using xv xvv using evaltree.BinaryExpr
    by (metis Value.simps(5) bin_eval.simps(8) intval_left_shift.simps(1) new_int.simps)
  have "val[xv * yv] = val[xv << (IntVal 64 i)]"
    using val_MulPower2
    by (metis ConstantExprE eval(1) evaltree_not_undef lhs times_Value_def yv)
  then show ?thesis
    by (metis eval(1) eval(2) evalDet lhs rhs)
qed
  sorry (* termination issues *)


end (* End of MulPhase *)

end (* End of file *)
