section \<open>Canonicalization Phase\<close>

theory CanonicalizationTreeProofs
  imports
    CanonicalizationTree
    Proofs.StampEvalThms
begin

lemma neutral_rewrite_helper:
      "valid_value x (IntegerStamp b lo hi) \<longrightarrow> intval_mul x (IntVal b (1)) = x"
  and "valid_value x (IntegerStamp b lo hi) \<Longrightarrow> intval_add x (IntVal b (0)) = x"
  and "valid_value x (IntegerStamp b lo hi) \<Longrightarrow> intval_sub x (IntVal b (0)) = x"
  and "valid_value x (IntegerStamp b lo hi) \<Longrightarrow> intval_xor x (IntVal b (0)) = x"
  and "valid_value x (IntegerStamp b lo hi) \<Longrightarrow> intval_or x (IntVal b (0)) = x"
  using valid_int_stamp_gives by fastforce+

lemma annihilator_rewrite_helper:
  shows "valid_value x (IntegerStamp b lo hi) \<Longrightarrow> intval_mul x (IntVal b 0) = IntVal b 0"
  and   "valid_value x (IntegerStamp b lo hi) \<Longrightarrow> intval_and x (IntVal b 0) = IntVal b 0"
  using valid_int_stamp_gives by fastforce+

text \<open>The -1 annihilator of OR is a bit harder to prove, because the upper bits are zeroed.\<close>

lemma annihilator_rewrite_helper2:
     "valid_value x (IntegerStamp b lo hi) \<Longrightarrow>
      intval_or x (IntVal b (neg_one b)) = IntVal b (neg_one b)"
  by (metis intval_or.simps(1) neg_one.simps neg_one_value new_int_bin.simps take_bit_eq_mask
      word_ao_absorbs(4) valid_int_stamp_gives)

lemma idempotent_rewrite_helper:
  shows "valid_value x (IntegerStamp b lo hi) \<Longrightarrow> intval_and x x = x"
  and   "valid_value x (IntegerStamp b lo hi) \<Longrightarrow> intval_or  x x = x"
  using valid_int_stamp_gives by fastforce+

value "size (v::32 word)"

experiment begin
lemma CanonicalizeBinaryProof:
  assumes "CanonicalizeBinaryOp before after"
  assumes "[m, p] \<turnstile> before \<mapsto> res"
  assumes "[m, p] \<turnstile> after \<mapsto> res'"
  shows "res = res'"
  using assms
proof (induct rule: CanonicalizeBinaryOp.induct)
  case (binary_const_fold x val1 y val2 val op)
  then show ?case
    by auto
next
  case (binary_fold_yneutral y c op stampx x stampy)
  obtain xval where x_eval: "[m, p] \<turnstile> x \<mapsto> xval"
    using binary_fold_yneutral.prems(2) by auto
  then have "bin_eval op xval c = xval"
    using neutral_rewrite_helper binary_fold_yneutral.hyps(2-3,6-) is_IntegerStamp_def
    sorry (*by (metis ConstantExpr Value.distinct(5) valid_value.simps(34))*)
  then show ?case
    by (metis binary_fold_yneutral.hyps(1) binary_fold_yneutral.prems(1,2) x_eval BinaryExprE
        ConstantExprE evalDet)
next
  case (binary_fold_yzero32 y c op stampx x stampy)
  obtain xval where x_eval: "[m, p] \<turnstile> x \<mapsto> xval"
    using binary_fold_yzero32.prems(1) by auto
  then have "bin_eval op xval c = c"
    using annihilator_rewrite_helper binary_fold_yzero32.hyps is_IntegerStamp_def
    sorry
  then show ?case
    by (metis BinaryExprE ConstantExprE binary_fold_yzero32.hyps(1) binary_fold_yzero32.prems(1,2)
        evalDet x_eval)
next
  case (binary_fold_yzero64 y c op stampx x stampy)
  obtain xval where x_eval: "[m, p] \<turnstile> x \<mapsto> xval"
    using binary_fold_yzero64.prems(1) by auto
  then have "bin_eval op xval c = c"
    using annihilator_rewrite_helper
    sorry
  then show ?case
    by (metis binary_fold_yzero64.hyps(1) evalDet binary_fold_yzero64.prems(1,2) ConstantExprE
        BinaryExprE x_eval)
next
  case (binary_idempotent op x)
  obtain xval where x_eval: "[m, p] \<turnstile> x \<mapsto> xval"
    using binary_idempotent.prems(1) by auto
  then have "bin_eval op xval xval = xval"
    using idempotent_rewrite_helper binary_idempotent.hyps sorry
  then show ?case
    by (metis BinaryExprE binary_idempotent.prems(1,2) evalDet x_eval)
qed
end

lemma CanonicalizeUnaryProof:
  assumes "CanonicalizeUnaryOp before after"
  assumes "[m, p] \<turnstile> before \<mapsto> res"
  assumes "[m, p] \<turnstile> after \<mapsto> res'"
  shows "res = res'"
  using assms
proof (induct rule: CanonicalizeUnaryOp.induct)
  case (unary_const_fold val' op val)
  then show ?case
    by auto
qed

lemma mul_rewrite_helper:
  shows "valid_value x (IntegerStamp 64 lo hi) \<Longrightarrow> intval_mul x (IntVal 64 (-1)) = intval_negate x" 
  using valid_int_stamp_gives by fastforce+

text \<open>As usual, the general case is harder to prove, because upper bits are zeroed.\<close>
lemma mul_rewrite_helper32:
  shows "valid_value x (IntegerStamp b lo hi) \<Longrightarrow>
         intval_mul x (IntVal b (neg_one b)) = intval_negate x"
  apply auto
  subgoal premises p
  proof -
    obtain y where y: "y = IntVal b (neg_one b)"
      by simp
    obtain xvv where xvv: "x = IntVal b xvv"
      using p valid_int by blast
    have notUndef: "intval_mul x y \<noteq> UndefVal"
      by (simp add: xvv y)
    have unfoldMul: "intval_mul x y = (new_int b (mask b * xvv))"
      by (simp add: mult.commute xvv y)
    have unfoldNegate: "intval_negate x = new_int b (- xvv)"
      using xvv by auto
    then show ?thesis
      by (metis (no_types, opaque_lifting) mask_eqs(5) take_bit_eq_mask mult.commute unfoldMul y
          mult_minus1_right neg_one.simps new_int.simps take_bit_minus_one_eq_mask)
  qed
  done

(* or a more manual proof:
lemma mul_rewrite_helper32:
  shows "valid_value x (IntegerStamp b lo hi) \<Longrightarrow> intval_mul x (new_int b (-1)) = intval_negate x" 
proof -
  assume v: "valid_value x (IntegerStamp b lo hi)"
  then obtain ix where ix: "x = IntVal b ix"
    by (metis valid_int_stamp_gives)
  then show "intval_mul x (new_int b (-1)) = intval_negate x"
    unfolding ix intval_mul.simps new_int_bin.simps new_int.simps
    by (simp; smt (verit, ccfv_threshold) ix mult_minus1_right of_int_mult take_bit_minus_one_eq_mask take_bit_mult take_bit_of_int uint_take_bit_eq v valid_int_fits word_of_int_uint)
qed
*)

experiment begin
lemma CanonicalizeMulProof:
  assumes "CanonicalizeMul before after"
  assumes "[m, p] \<turnstile> before \<mapsto> res"
  assumes "[m, p] \<turnstile> after \<mapsto> res'"
  shows "res = res'"
  using assms
proof (induct rule: CanonicalizeMul.induct)
  show ?thesis
    using ConstantExprE BinaryExprE bin_eval.simps evalDet mul_rewrite_helper
    sorry
qed
end

lemma valid_int_stamp_both:
  assumes 1: "valid_value x (IntegerStamp b lox hix)"
  and     2: "valid_value y (IntegerStamp b loy hiy)"
  obtains ix iy where "x = IntVal b ix"
  and "take_bit b ix = ix"
  and "y = IntVal b iy"
  and "take_bit b iy = iy"
  by (metis valid_int_stamp_gives assms)

(* (x - y) + y \<Rightarrow> x *)
(*  x + (y - x) \<Rightarrow> y *)
(* (-x + y) \<Rightarrow> (y - x) *)
(* (x + (-y)) \<Rightarrow> (x - y) *)
lemma add_rewrites_helper:
  assumes 1:"valid_value x (IntegerStamp b lox hix)"
  and     2:"valid_value y (IntegerStamp b loy hiy)"
  shows "intval_add (intval_sub x y) y = x \<and>
         intval_add x (intval_sub y x) = y \<and>
         intval_add (intval_negate x) y = intval_sub y x \<and>
         intval_add x (intval_negate y) = intval_sub x y"
  using valid_int_stamp_both[OF 1 2] by fastforce

experiment begin
lemma CanonicalizeAddProof:
  assumes "CanonicalizeAdd before after"
  assumes "[m, p] \<turnstile> before \<mapsto> res"
  assumes "[m, p] \<turnstile> after \<mapsto> res'"
  shows "res = res'"
  using assms
proof (induct rule: CanonicalizeAdd.induct)
  case (add_xsub x a y stampa stampy)
  then show ?case 
    using BinaryExprE Stamp.collapse(1) bin_eval.simps(1,3) intval_add_sym add_rewrites_helper(1)
          evalDet
    sorry
next
  case (add_ysub y a x stampa stampx)
  then show ?case sorry (*
    by (metis is_IntegerStamp_def add_ysub.hyps add_ysub.prems evalDet BinaryExprE Stamp.sel(1) 
        bin_eval.simps(1) bin_eval.simps(3) stamp_implies_valid_value intval_add_sym add_rewrites_helper(2))*)
next
  case (add_xnegate nx x stampx stampy y)
  then show ?case sorry (*
    by (smt (verit, del_insts) BinaryExprE Stamp.sel(1) UnaryExprE add_rewrites_helper(4) 
        bin_eval.simps(1) bin_eval.simps(3) evalDet stamp_implies_valid_value intval_add_sym is_IntegerStamp_def unary_eval.simps(2)) *)
next
  case (add_ynegate ny y stampx x stampy)
  then show ?case sorry (*
    by (smt (verit) BinaryExprE Stamp.sel(1) UnaryExprE add_rewrites_helper(4) bin_eval.simps(1) 
        bin_eval.simps(3) evalDet stamp_implies_valid_value is_IntegerStamp_def unary_eval.simps(2)) *)
qed

(* (x + y) - y \<Rightarrow> x *)
(* (x + y) - x \<Rightarrow> y *)
(* (x - y) - x \<Rightarrow> (-y) *)
(* x - (x + y) \<Rightarrow> (-y) *)
(* y - (x + y) \<Rightarrow> (-x) *)
(* x - (x - y) \<Rightarrow> y *)
(* x - (-y) \<Rightarrow> x + y *)
lemma sub_rewrites_helper:
  assumes 1:"valid_value x (IntegerStamp b lox hix)"
  and     2:"valid_value y (IntegerStamp b loy hiy)"

  shows "intval_sub (intval_add x y) y  = x"
  and   "intval_sub (intval_add x y) x  = y" 
  and   "intval_sub (intval_sub x y) x  = intval_negate y" 
  and   "intval_sub x (intval_add x y)  = intval_negate y"
  and   "intval_sub y (intval_add x y)  = intval_negate x" 
  and   "intval_sub x (intval_sub x y)  = y"
  and   "intval_sub x (intval_negate y) = intval_add x y"
  using valid_int_stamp_both[OF 1 2] by fastforce+

(* x - x \<Rightarrow> 0 *)
(* 0 - x \<Rightarrow> -x *)
lemma sub_single_rewrites_helper:
  assumes "valid_value x (IntegerStamp b lox hix)"
  shows   "intval_sub x x = IntVal b 0" 
  and     "intval_sub (IntVal b 0) x = intval_negate x" 
  using assms valid_int_stamp_gives by fastforce+

lemma CanonicalizeSubProof:
  assumes "CanonicalizeSub before after"
  assumes "[m, p] \<turnstile> before \<mapsto> res"
  assumes "[m, p] \<turnstile> after \<mapsto> res'"
  shows "res = res'"
  using assms
proof (induct rule: CanonicalizeSub.induct)
  case (sub_same64 stampx x lo hi)
  show ?case sorry (*
    using ConstantExprE BinaryExprE  bin_eval.simps evalDet sub_same64.prems sub_single_rewrites_helper 
      stamp_implies_valid_value sub_same64.hyps(1) sub_same64.hyps(2)
    by (auto; metis) *)
next
  case (sub_left_add1 x a b stampa stampb)
  then show ?case sorry (*
    by (metis BinaryExprE Stamp.collapse(1) bin_eval.simps(1) bin_eval.simps(3) evalDet 
        stamp_implies_valid_value sub_rewrites_helper(1)) *)
next
  case (sub_left_add2 x a b stampa stampb)
  then show ?case sorry (*
    by (metis BinaryExprE Stamp.collapse(1) bin_eval.simps(1) bin_eval.simps(3) evalDet 
        stamp_implies_valid_value sub_rewrites_helper(2)) *)
next
  case (sub_left_sub x a b stampa stampb)
  then show ?case sorry (*
    by (smt (verit) BinaryExprE Stamp.sel(1) UnaryExprE bin_eval.simps(3) evalDet
        stamp_implies_valid_value is_IntegerStamp_def sub_rewrites_helper(3) unary_eval.simps(2)) *)
next
  case (sub_right_add1 y a b stampa stampb)
  then show ?case sorry (*
    by (smt (verit) BinaryExprE Stamp.sel(1) UnaryExprE bin_eval.simps(1) bin_eval.simps(3) evalDet
        stamp_implies_valid_value is_IntegerStamp_def sub_rewrites_helper(4) unary_eval.simps(2)) *)
next
  case (sub_right_add2 y a b stampa stampb)
  then show ?case sorry (*
    by (smt (verit) BinaryExprE Stamp.sel(1) UnaryExprE bin_eval.simps(1) bin_eval.simps(3) evalDet
        stamp_implies_valid_value is_IntegerStamp_def sub_rewrites_helper(5) unary_eval.simps(2)) *)
next
  case (sub_right_sub y a b stampa stampb)
  then show ?case sorry (*
    by (metis BinaryExprE Stamp.sel(1) bin_eval.simps(3) evalDet
        stamp_implies_valid_value is_IntegerStamp_def sub_rewrites_helper(6)) *)
next
  case (sub_xzero64 stampx x lo hi)
  then show ?case sorry (*
    using ConstantExprE BinaryExprE  bin_eval.simps evalDet sub_xzero64.prems sub_single_rewrites_helper 
      stamp_implies_valid_value sub_xzero64.hyps(1) sub_xzero64.hyps(2)
    by (auto; metis) *)
next
  case (sub_y_negate nb b stampa a stampb)
  then show ?case sorry (*
    by (smt (verit, best) BinaryExprE Stamp.sel(1) UnaryExprE bin_eval.simps(1) bin_eval.simps(3) evalDet
        stamp_implies_valid_value is_IntegerStamp_def sub_rewrites_helper(7) unary_eval.simps(2)) *)
qed

(* -(x-y) = (x-y) *)
lemma negate_xsuby_helper:
  assumes "valid_value x (IntegerStamp b lox hix)"
  and "valid_value y (IntegerStamp b loy hiy)"
  shows "intval_negate (intval_sub x y) = intval_sub y x"
  using valid_int_stamp_both[OF assms] 
  by (smt (verit, ccfv_threshold) ab_group_add_class.ab_diff_conv_add_uminus add.commute diff_0
      add_diff_cancel_left' intval_negate.simps(1) intval_sub.simps(1) take_bit_dist_subR
      new_int_bin.simps new_int.simps)

(* -(-x) = x *)
lemma negate_negate_helper:
  assumes "valid_value x (IntegerStamp b lox hix)"
  shows "intval_negate (intval_negate x) = x" 
  by (metis (no_types, opaque_lifting) add.inverse_inverse assms diff_0 intval_negate.simps(1)
      new_int.simps take_bit_dist_subR valid_int_stamp_gives)

lemma CanonicalizeNegateProof:
  assumes "CanonicalizeNegate before after"
  assumes "[m, p] \<turnstile> before \<mapsto> res"
  assumes "[m, p] \<turnstile> after \<mapsto> res'"
  shows "res = res'"
  using assms
proof (induct rule: CanonicalizeNegate.induct)
  case (negate_negate nx x)
  thus ?case sorry (*
    by (metis UnaryExprE evalDet stamp_implies_valid_value is_IntegerStamp_def negate_negate_helper unary_eval.simps(2)) *)
next
  case (negate_sub e x y stampx stampy)
  thus ?case sorry (*
    by (smt (verit) BinaryExprE Stamp.sel(1) UnaryExprE bin_eval.simps(3) evalDet stamp_implies_valid_value
        is_IntegerStamp_def negate_xsuby_helper unary_eval.simps(2)) *)
qed
end

(* TODO: a better name for this? *)
experiment begin
lemma word_helper:
  shows "\<And> x :: 32 word. \<not>(- x <s 0 \<and> x <s 0)" 
  and   "\<And> x :: 64 word. \<not>(- x <s 0 \<and> x <s 0)"
  and   "\<And> x :: 32 word. \<not> - x <s 0 \<and> \<not> x <s 0 \<Longrightarrow> 2 * x = 0"
  and   "\<And> x :: 64 word. \<not> - x <s 0 \<and> \<not> x <s 0 \<Longrightarrow> 2 * x = 0"
  apply (case_tac[!] "x")
  apply auto+
  sorry

(* abs(-x) = abs(x) *)
(* abs(abs(x)) = abs(x) 
lemma abs_rewrite_helper:
  assumes "valid_value (IntegerStamp b lox hix) x"
  shows "intval_abs (intval_negate x) = intval_abs x"
  and "intval_abs (intval_abs x) = intval_abs x"
  apply (case_tac[!] "x")
  using word_helper apply auto+
  done
*)

lemma abs_abs_is_abs:
  assumes 1: "valid_value x (IntegerStamp b lox hix)"
  shows "intval_abs (intval_abs x) = intval_abs x"
(* was:
  using word_helper
  by (metis assms intval_abs.simps(1) intval_abs.simps(2) valid32or64_both) 
*)
  sorry

lemma abs_neg_is_neg:
  assumes "valid_value x (IntegerStamp b lox hix)"
  shows "intval_abs (intval_negate x) = intval_abs x"
  apply (case_tac[!] "x") using intval_negate.simps(2)
  apply presburger defer
  apply (metis valid_value.simps(5) assms)
  apply simp
  sorry
end

(*
lemma CanonicalizeAbsAbs:
  assumes vv: "is_IntegerStamp (stamp_expr e)"
  assumes "[m, p] \<turnstile> UnaryExpr UnaryAbs (UnaryExpr UnaryAbs e) \<mapsto> v"
  shows "[m, p] \<turnstile> UnaryExpr UnaryAbs e \<mapsto> v"
  by (metis UnaryExprE abs_abs_is_abs assms(2) stamp_implies_valid_value
      is_IntegerStamp_def unary_eval.simps(1) vv)

lemma CanonicalizeAbsNeg:
  assumes vv: "is_IntegerStamp (stamp_expr e)"
  assumes "[m, p] \<turnstile> UnaryExpr UnaryAbs (UnaryExpr UnaryNeg e) \<mapsto> v"
  shows "[m, p] \<turnstile> UnaryExpr UnaryAbs e \<mapsto> v"
  using UnaryExprE abs_neg_is_neg assms(2) stamp_implies_valid_value
      is_IntegerStamp_def unary_eval.simps(2) vv
  by (smt (verit, ccfv_threshold) evaltree.simps unary_eval.simps(1))
  
lemma CanonicalizeAbsProof:
  assumes "CanonicalizeAbs before after"
  assumes "[m, p] \<turnstile> before \<mapsto> res"
  assumes "[m, p] \<turnstile> after \<mapsto> res'"
  shows "res = res'"
  using assms
proof (induct rule: CanonicalizeAbs.induct)
  case (abs_abs ax x)
  then show ?case
    by (metis UnaryExprE abs_rewrite_helper(2) evalDet stamp_implies_valid_value is_IntegerStamp_def
        unary_eval.simps(1))
next
  case (abs_neg nx x)
  then show ?case
    by (metis UnaryExprE abs_rewrite_helper(1) evalDet stamp_implies_valid_value is_IntegerStamp_def
        unary_eval.simps(1) unary_eval.simps(2))
qed
*)
(* ~(~x) = x *)
lemma not_rewrite_helper:
  assumes "valid_value x (IntegerStamp b lox hix)"
  shows "intval_not (intval_not x) = x"
  by (metis bit.double_compl intval_not.simps(1) new_int.simps take_bit_not_take_bit assms
      valid_int_stamp_gives)

experiment begin
lemma CanonicalizeNotProof:
  assumes "CanonicalizeNot before after"
  assumes "[m, p] \<turnstile> before \<mapsto> res"
  assumes "[m, p] \<turnstile> after \<mapsto> res'"
  shows "res = res'"
  using assms
proof (induct rule: CanonicalizeNot.induct)
  case (not_not nx x)
  then show ?case sorry (*
    by (metis UnaryExprE evalDet is_IntegerStamp_def not_rewrite_helper
        stamp_implies_valid_value unary_eval.simps(3)) *)
qed
end

lemma demorgans_rewrites_helper:
  assumes "valid_value x (IntegerStamp b lox hix)"
  and     "valid_value y (IntegerStamp b loy hiy)"

  shows "intval_and (intval_not x) (intval_not y) = intval_not (intval_or x y)"
  and   "intval_or (intval_not x) (intval_not y) = intval_not (intval_and x y)"
  and   "x = y \<Longrightarrow> intval_and x y = x"
  and   "x = y \<Longrightarrow> intval_or x y = x"
  using assms
  apply (cases x; cases y; auto; presburger)
  apply (cases x; cases y; auto; simp add: take_bit_not_take_bit)
  apply (cases x; cases y; auto)
  using assms(1) apply auto apply presburger
  using idempotent_rewrite_helper(2) by blast

experiment begin
lemma CanonicalizeAndProof:
  assumes "CanonicalizeAnd before after"
  assumes "[m, p] \<turnstile> before \<mapsto> res"
  assumes "[m, p] \<turnstile> after \<mapsto> res'"
  shows "res = res'"
  using assms
proof (induct rule: CanonicalizeAnd.induct)
  case (and_same x)
  then show ?case sorry (*
    by (metis BinaryExprE bin_eval.simps(4) demorgans_rewrites_helper(3) evalDet
        stamp_implies_valid_value is_IntegerStamp_def) *)
next
  case (and_demorgans nx x ny y stampx stampy)
  then show ?case sorry (*
    by (smt (z3) BinaryExprE Stamp.sel(1) UnaryExprE bin_eval.simps(4) bin_eval.simps(5) 
        demorgans_rewrites_helper(1) evalDet stamp_implies_valid_value is_IntegerStamp_def unary_eval.simps(3)) *)
qed

lemma CanonicalizeOrProof:
  assumes "CanonicalizeOr before after"
  assumes "[m, p] \<turnstile> before \<mapsto> res"
  assumes "[m, p] \<turnstile> after \<mapsto> res'"
  shows "res = res'"
  using assms
proof (induct rule: CanonicalizeOr.induct)
  case (or_same x)
  then show ?case sorry (*
    by (metis BinaryExprE bin_eval.simps(5) demorgans_rewrites_helper(4) evalDet
        stamp_implies_valid_value is_IntegerStamp_def) *)
next
  case (or_demorgans nx x ny y stampx stampy)
  then show ?case sorry (*
    by (smt (z3) BinaryExprE Stamp.sel(1) UnaryExprE bin_eval.simps(4) bin_eval.simps(5) demorgans_rewrites_helper(2)
        evalDet stamp_implies_valid_value is_IntegerStamp_def unary_eval.simps(3)) *)
qed
end

experiment begin
lemma stamps_touch_but_not_less_than_implies_equal:
  "\<lbrakk>valid_value x stampx;
    valid_value y stampy;
    is_IntegerStamp stampx \<and> is_IntegerStamp stampy;
    stpi_upper stampx = stpi_lower stampy;
    \<not> val_to_bool (intval_less_than x y)\<rbrakk> \<Longrightarrow> x = y" 
  using valid_int_stamp_both intval_equals.simps(1-2) intval_less_than.simps(1-2) val_to_bool.simps(1)
  sorry

lemma disjoint_stamp_implies_less_than:
  "\<lbrakk>valid_value x stampx;
    valid_value y stampy;
    is_IntegerStamp stampx \<and> is_IntegerStamp stampy;
    stpi_upper stampx < stpi_lower stampy\<rbrakk> 
  \<Longrightarrow> val_to_bool(intval_less_than x y)"
  sorry

lemma CanonicalizeConditionalProof:
  assumes "CanonicalizeConditional before after"
  assumes "[m, p] \<turnstile> before \<mapsto> res"
  assumes "[m, p] \<turnstile> after \<mapsto> res'"
  shows "res = res'"
  using assms
proof (induct rule: CanonicalizeConditional.induct)
  case (eq_branches t f c)
  then show ?case
    using evalDet by force
next
  case (cond_eq c x y stampx stampy)
  obtain xval where xeval: "[m,p] \<turnstile> x \<mapsto> xval"
    using cond_eq.hyps(1) cond_eq.prems(1) by fast
  obtain yval where yeval: "[m,p] \<turnstile> y \<mapsto> yval"
    using cond_eq.prems(2) by fast
  show ?case proof (cases "xval = yval")
    case True
    then show ?thesis
      by (smt (verit, ccfv_threshold) ConditionalExprE cond_eq.prems(1,2) evalDet xeval yeval)
  next
    case False
    then have "\<not>(val_to_bool(intval_equals xval yval))"
      apply (cases "intval_equals xval yval")
      prefer 2 defer using val_to_bool.simps apply presburger+
      subgoal premises p for b v
      proof -
        have notUndef: "intval_equals xval yval \<noteq> UndefVal"
          by (simp add: p(2))
        have notUndefImpliesIntVal: "intval_equals xval yval \<noteq> UndefVal
                                                              \<Longrightarrow> (is_IntVal xval \<and> is_IntVal yval)"
          by (metis bin_eval.simps(11) defined_eval_is_intval)
        obtain xb xvv where xvv: "xval = IntVal xb xvv"
          by (meson is_IntVal_def notUndef notUndefImpliesIntVal)
        obtain yb yvv where yvv: "yval = IntVal yb yvv"
          by (meson is_IntVal_def notUndef notUndefImpliesIntVal)
        have sameWidth: "xb = yb"
          by (metis bool_to_val_bin.elims intval_equals.simps(1) notUndef xvv yvv)
        then have unfoldEquals: "intval_equals xval yval = (bool_to_val (xvv = yvv))"
          by (simp add: xvv yvv)
        then have notEqual: "(bool_to_val (xvv = yvv)) = bool_to_val False"
          using False sameWidth xvv yvv by auto
        then show ?thesis
          by (simp add: unfoldEquals)
      qed
      done
    then have "res = yval"
      by (smt (verit, ccfv_threshold) BinaryExprE ConditionalExprE bin_eval.simps(11) evalDet yeval
          cond_eq.hyps(1) cond_eq.prems(1) xeval)
    then show ?thesis
      using cond_eq.prems(1,2) xeval yeval evalDet by presburger
  qed
next
  case (condition_bounds_x c x y stampx stampy)
  obtain xval where xeval: "[m,p] \<turnstile> x \<mapsto> xval"
    using condition_bounds_x.prems(2) by simp
  obtain yval where yeval: "[m,p] \<turnstile> y \<mapsto> yval"
    using condition_bounds_x.hyps(1) condition_bounds_x.prems(1) by blast
  then show ?case proof (cases "val_to_bool(intval_less_than xval yval)")
    case True
    then show ?thesis
      by (smt (verit, best) BinaryExprE ConditionalExprE bin_eval.simps(12) evalDet xeval yeval
          condition_bounds_x.hyps(1) condition_bounds_x.prems(1,2))
  next
    case False
    then have "stpi_upper stampx = stpi_lower stampy"
      sorry (*
      by (metis False condition_bounds_x.hyps(4) order.not_eq_order_implies_strict
          disjoint_stamp_implies_less_than condition_bounds_x.hyps(2) condition_bounds_x.hyps(3) condition_bounds_x.hyps(6)
          stamp_implies_valid_value xeval yeval) *)
    then have "(xval = yval)"
      sorry (*
      by (metis False condition_bounds_x.hyps(2-3,6) stamp_implies_valid_value
          stamps_touch_but_not_less_than_implies_equal xeval yeval) *)
    then have "res = xval \<and> res' = xval"
      using condition_bounds_x.prems(1) \<open>[m,p] \<turnstile> x \<mapsto> res'\<close> evalDet xeval yeval by force
    then show ?thesis
      by simp
  qed
next
  case (condition_bounds_y c x y stampx stampy)
  obtain xval where xeval: "[m,p] \<turnstile> x \<mapsto> xval"
    using condition_bounds_y.hyps(1) condition_bounds_y.prems(1) by blast
  obtain yval where yeval: "[m,p] \<turnstile> y \<mapsto> yval"
    using condition_bounds_y.hyps(1) condition_bounds_y.prems(1) by blast
  then show ?case proof (cases "val_to_bool(intval_less_than xval yval)")
    case True
    then show ?thesis
      by (smt (verit, best) BinaryExprE ConditionalExprE bin_eval.simps(12) evalDet xeval yeval
          condition_bounds_y.hyps(1) condition_bounds_y.prems(1,2))
  next
    case False
    have "stpi_upper stampx = stpi_lower stampy"
      sorry (*
      by (metis False condition_bounds_y.hyps(4) order.not_eq_order_implies_strict
          disjoint_stamp_implies_less_than condition_bounds_y.hyps(2) condition_bounds_y.hyps(3)
          condition_bounds_y.hyps(6) stamp_implies_valid_value xeval yeval) *)
    then have "(xval = yval)"
      sorry (*
      by (metis False condition_bounds_y.hyps(2-3,6)
          stamp_implies_valid_value stamps_touch_but_not_less_than_implies_equal xeval yeval)
      *)
    then have "res = yval \<and> res' = yval"
      using condition_bounds_y.prems(1) \<open>[m,p] \<turnstile> y \<mapsto> res'\<close> evalDet xeval yeval by force
    then show ?thesis
      by simp
  qed
next
  case (negate_condition nc c stampc lo hi stampx x stampy y)
  obtain cval where ceval: "[m,p] \<turnstile> c \<mapsto> cval"
    using negate_condition.prems(2) by auto
  obtain ncval where nceval: "[m,p] \<turnstile> nc \<mapsto> ncval"
    using negate_condition.prems by blast
  then show ?case using assms proof (cases "(val_to_bool ncval)")
    case True
    obtain xval where xeval: "[m,p] \<turnstile> x \<mapsto> xval"
      by (metis (full_types) ConditionalExprE negate_condition.prems(1))
    then have "res = xval"
      by (metis (full_types) ConditionalExprE True evalDet nceval negate_condition.prems(1))
    have "c \<noteq> nc"
      by (simp add: negate_condition.hyps(1))
    then have "\<not>(val_to_bool cval)"
      sorry (*
      by (metis True UnaryExprE ceval evalDet intval_logic_negation.simps(1) nceval negate_condition.hyps(1) negate_condition.hyps(2) negate_condition.hyps(3) stamp_implies_valid_value unary_eval.simps(4) val_to_bool.simps(1) valid_int32)
      *)
    then have "res' = xval"
      by (metis (full_types) ConditionalExprE evalDet xeval negate_condition(9) ceval)
    then show ?thesis
      by (simp add: \<open>res = xval\<close>)
  next
    case False
    obtain yval where yeval: "[m,p] \<turnstile> y \<mapsto> yval"
      by (metis (full_types) ConditionalExprE negate_condition.prems(1))
    then have "res = yval"
      by (metis (full_types) False nceval negate_condition.prems(1) yeval evalDet ConditionalExprE)
    moreover have "val_to_bool(cval)"
      sorry (*
      by (metis False UnaryExprE ceval evalDet intval_logic_negation.simps(1) nceval negate_condition.hyps(1) negate_condition.hyps(2) negate_condition.hyps(3) stamp_implies_valid_value unary_eval.simps(4) val_to_bool.simps(1) valid_int32 zero_neq_one)
      *)
    moreover have "res' = yval"
      by (metis (full_types) calculation(2) ceval negate_condition.prems evalDet ConditionalExprE
          yeval)
    ultimately show ?thesis
      by simp
  qed
next
  case (const_true c val t f)
  then show ?case
    by (auto simp add: evalDet)
next
  case (const_false c val t f)
  then show ?case
    by (auto simp add: evalDet)
qed
end

end