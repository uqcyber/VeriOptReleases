subsection \<open>ConditionalNode Phase\<close>

theory ConditionalPhase
  imports
    Common
    Proofs.StampEvalThms
begin

phase ConditionalNode
  terminating size
begin

lemma negates: "\<exists>v b. e = IntVal b v \<and> b > 0 \<Longrightarrow> val_to_bool (val[e]) \<longleftrightarrow> \<not>(val_to_bool (val[!e]))"
  by (metis (mono_tags, lifting) intval_logic_negation.simps(1) logic_negate_def new_int.simps 
      of_bool_eq(2) one_neq_zero take_bit_of_0 take_bit_of_1 val_to_bool.simps(1))

lemma negation_condition_intval: 
  assumes "e = IntVal b ie"
  assumes "0 < b"
  shows "val[(!e) ? x : y] = val[e ? y : x]"
  by (metis assms intval_conditional.simps negates)

lemma negation_preserve_eval:
  assumes "[m, p] \<turnstile> exp[!e] \<mapsto> v"
  shows "\<exists>v'. ([m, p] \<turnstile> exp[e] \<mapsto> v') \<and> v = val[!v']"
  using assms by auto

lemma negation_preserve_eval_intval:
  assumes "[m, p] \<turnstile> exp[!e] \<mapsto> v"
  shows "\<exists>v' b vv. ([m, p] \<turnstile> exp[e] \<mapsto> v') \<and> v' = IntVal b vv \<and> b > 0"
  by (metis assms eval_bits_1_64 intval_logic_negation.elims negation_preserve_eval unfold_unary)

optimization NegateConditionFlipBranches: "((!e) ? x : y) \<longmapsto> (e ? y : x)"
  apply simp apply (rule allI; rule allI; rule allI; rule impI)
  subgoal premises p for m p v
  proof -
    obtain ev where ev: "[m,p] \<turnstile> e \<mapsto> ev"
      using p by blast
    obtain notEv where notEv: "notEv = intval_logic_negation ev"
      by simp
    obtain lhs where lhs: "[m,p] \<turnstile> ConditionalExpr (UnaryExpr UnaryLogicNegation e) x y \<mapsto> lhs"
      using p by auto
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using lhs by blast
    obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> yv"
      using lhs by blast
    then show ?thesis
      by (smt (z3) le_expr_def ConditionalExpr ConditionalExprE Value.distinct(1) evalDet negates p
          negation_preserve_eval negation_preserve_eval_intval)
  qed
  done

optimization DefaultTrueBranch: "(true ? x : y) \<longmapsto> x" .

optimization DefaultFalseBranch: "(false ? x : y) \<longmapsto> y" .

optimization ConditionalEqualBranches: "(e ? x : x) \<longmapsto> x" .

optimization condition_bounds_x: "((u < v) ? x : y) \<longmapsto> x 
    when (stamp_under (stamp_expr u) (stamp_expr v) \<and> wf_stamp u \<and> wf_stamp v)"
  using stamp_under_defn by fastforce

optimization condition_bounds_y: "((u < v) ? x : y) \<longmapsto> y 
    when (stamp_under (stamp_expr v) (stamp_expr u) \<and> wf_stamp u \<and> wf_stamp v)"
  using stamp_under_defn_inverse by fastforce

(** Start of new proofs **)

(* Value-level proofs *)
lemma val_optimise_integer_test: 
  assumes "\<exists>v. x = IntVal 32 v"
  shows "val[((x & (IntVal 32 1)) eq (IntVal 32 0)) ? (IntVal 32 0) : (IntVal 32 1)] = 
         val[x & IntVal 32 1]"
  using assms apply auto
  apply (metis (full_types) bool_to_val.simps(2) val_to_bool.simps(1))
  by (metis (mono_tags, lifting) bool_to_val.simps(1) val_to_bool.simps(1) even_iff_mod_2_eq_zero
      odd_iff_mod_2_eq_one and_one_eq)

optimization ConditionalEliminateKnownLess: "((x < y) ? x : y) \<longmapsto> x 
                                 when (stamp_under (stamp_expr x) (stamp_expr y)
                                      \<and> wf_stamp x \<and> wf_stamp y)"
  using stamp_under_defn by fastforce

lemma ExpIntBecomesIntVal:
  assumes "stamp_expr x = IntegerStamp b xl xh"
  assumes "wf_stamp x"
  assumes "valid_value v (IntegerStamp b xl xh)"
  assumes "[m,p] \<turnstile> x \<mapsto> v"
  shows "\<exists>xv. v = IntVal b xv"
  using assms by (simp add: IRTreeEvalThms.valid_value_elims(3))

(* Optimisations *)

lemma intval_self_is_true:
  assumes "yv \<noteq> UndefVal"
  assumes "yv = IntVal b yvv"
  shows "intval_equals yv yv = IntVal 32 1"
  using assms by (cases yv; auto)

lemma intval_commute:
  assumes "intval_equals yv xv \<noteq> UndefVal"
  assumes "intval_equals xv yv \<noteq> UndefVal"
  shows "intval_equals yv xv = intval_equals xv yv"
  using assms apply (cases yv; cases xv; auto) by (smt (verit, best))

definition isBoolean :: "IRExpr \<Rightarrow> bool" where
  "isBoolean e = (\<forall>m p cond. (([m,p] \<turnstile> e \<mapsto> cond) \<longrightarrow> (cond \<in> {IntVal 32 0, IntVal 32 1})))"

lemma preserveBoolean:
  assumes "isBoolean c"
  shows "isBoolean exp[!c]"
  using assms isBoolean_def apply auto
  by (metis (no_types, lifting) IntVal0 IntVal1 intval_logic_negation.simps(1) logic_negate_def)

optimization ConditionalIntegerEquals_1: "exp[BinaryExpr BinIntegerEquals (c ? x : y) (x)] \<longmapsto> c
                                          when stamp_expr x = IntegerStamp b xl xh \<and> wf_stamp x \<and>
                                               stamp_expr y = IntegerStamp b yl yh \<and> wf_stamp y \<and>
                                               (alwaysDistinct (stamp_expr x) (stamp_expr y)) \<and>
                                               isBoolean c"
  apply (metis Canonicalization.cond_size add_lessD1 size_binary_lhs) apply auto
  subgoal premises p for m p cExpr xv cond
  proof -
    obtain cond where cond: "[m,p] \<turnstile> c \<mapsto> cond"
      using p by blast
    have cRange: "cond = IntVal 32 0 \<or> cond = IntVal 32 1"
      using p cond isBoolean_def by blast
    then obtain yv where yVal: "[m,p] \<turnstile> y \<mapsto> yv"
      using p(15) by auto
    obtain xvv where xvv: "xv = IntVal b xvv"
       by (metis p(1,2,7) valid_int wf_stamp_def)
    obtain yvv where yvv: "yv = IntVal b yvv"
      by (metis ExpIntBecomesIntVal p(3,4) wf_stamp_def yVal)
    have yxDiff: "xvv \<noteq> yvv"
      by (smt (verit, del_insts) yVal xvv wf_stamp_def valid_int_signed_range p yvv)
    have eqEvalFalse: "intval_equals yv xv = (IntVal 32 0)"
      unfolding xvv yvv apply auto by (metis (mono_tags) bool_to_val.simps(2) yxDiff)
    then have valEvalSame: "cond = intval_equals val[cond ? xv : yv] xv"
      apply (cases "cond = IntVal 32 0"; simp) using cRange xvv by auto
    then have condTrue: "val_to_bool cond \<Longrightarrow> cExpr = xv"
      by (metis (mono_tags, lifting) cond evalDet p(11) p(7) p(9))
    then have condFalse: "\<not>(val_to_bool cond) \<Longrightarrow> cExpr = yv"
      by (metis (full_types) cond evalDet p(11) p(9) yVal)
    then have "[m,p] \<turnstile> c \<mapsto> intval_equals cExpr xv"
      using cond condTrue valEvalSame by fastforce
    then show ?thesis
      by blast
  qed
  done

(* Helpers *)
lemma negation_preserve_eval0:
  assumes "[m, p] \<turnstile> exp[e] \<mapsto> v"
  assumes "isBoolean e"
  shows "\<exists>v'. ([m, p] \<turnstile> exp[!e] \<mapsto> v')"
  using assms
proof -
  obtain b vv where vIntVal: "v = IntVal b vv"
    using isBoolean_def assms by blast
  then have negationDefined: "intval_logic_negation v \<noteq> UndefVal"
    by simp
  show ?thesis
    using assms(1) negationDefined by fastforce
qed

lemma negation_preserve_eval2:
  assumes "([m, p] \<turnstile> exp[e] \<mapsto> v)"
  assumes "(isBoolean e)"
  shows "\<exists>v'. ([m, p] \<turnstile> exp[!e] \<mapsto> v') \<and> v = val[!v']"
  using assms
proof -
  obtain notEval where notEval: "([m, p] \<turnstile> exp[!e] \<mapsto> notEval)"
    by (metis assms negation_preserve_eval0)
  then have logicNegateEquiv: "notEval = intval_logic_negation v"
    using evalDet  assms(1) unary_eval.simps(4) by blast
  then have vRange: "v = IntVal 32 0 \<or> v = IntVal 32 1"
    using assms by (auto simp add: isBoolean_def)
  have evaluateNot: "v = intval_logic_negation notEval"
    by (metis IntVal0 IntVal1 intval_logic_negation.simps(1) logicNegateEquiv logic_negate_def
        vRange)
  then show ?thesis
    using notEval by auto
qed

optimization ConditionalIntegerEquals_2: "exp[BinaryExpr BinIntegerEquals (c ? x : y) (y)] \<longmapsto> (!c)
                                          when stamp_expr x = IntegerStamp b xl xh \<and> wf_stamp x \<and>
                                               stamp_expr y = IntegerStamp b yl yh \<and> wf_stamp y \<and>
                                               (alwaysDistinct (stamp_expr x) (stamp_expr y)) \<and>
                                               isBoolean c"
  apply (smt (verit) not_add_less1 max_less_iff_conj max.absorb3 linorder_less_linear add_2_eq_Suc'
         add_less_cancel_right size_binary_lhs add_lessD1 Canonicalization.cond_size)
  apply auto
  subgoal premises p for m p cExpr yv cond trE faE
  proof -
    obtain cond where cond: "[m,p] \<turnstile> c \<mapsto> cond"
      using p by blast
    then have condNotUndef: "cond \<noteq> UndefVal"
      by (simp add: evaltree_not_undef)
    then obtain notCond where notCond: "[m,p] \<turnstile> exp[!c] \<mapsto> notCond"
      by (meson p(6) negation_preserve_eval2 cond)
    have cRange: "cond = IntVal 32 0 \<or> cond = IntVal 32 1"
      using p cond by (simp add: isBoolean_def)
    then have cNotRange:  "notCond = IntVal 32 0 \<or> notCond = IntVal 32 1"
      by (metis (no_types, lifting) IntVal0 IntVal1 cond evalDet intval_logic_negation.simps(1)
          logic_negate_def negation_preserve_eval notCond)
    then obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p by auto
    then have trueCond: "(notCond = IntVal 32 1) \<Longrightarrow> [m,p] \<turnstile> (ConditionalExpr c x y) \<mapsto> yv"
      by (smt (verit, best) cRange evalDet negates negation_preserve_eval notCond p(7) cond
          zero_less_numeral val_to_bool.simps(1) evaltree_not_undef ConditionalExpr
          ConditionalExprE)
    obtain xvv where xvv: "xv = IntVal b xvv"
      by (metis p(1,2) valid_int wf_stamp_def xv)
    then have opposites: "notCond = intval_logic_negation cond"
      by (metis cond evalDet negation_preserve_eval notCond)
    then have negate: "(intval_logic_negation cond = IntVal 32 0) \<Longrightarrow> (cond = IntVal 32 1)"
      using cRange intval_logic_negation.simps negates by fastforce
    have falseCond: "(notCond = IntVal 32 0) \<Longrightarrow> [m,p] \<turnstile> (ConditionalExpr c x y) \<mapsto> xv"
      unfolding opposites using negate cond evalDet p(13,14,15,16) xv by auto
    obtain yvv where yvv: "yv = IntVal b yvv"
      by (metis p(3,4,7) wf_stamp_def ExpIntBecomesIntVal)
    have yxDiff: "xv \<noteq> yv"
      by (metis linorder_not_less max.absorb1 max.absorb4 max_less_iff_conj min_def xv yvv
          wf_stamp_def valid_int_signed_range p(1,2,3,4,5,7))
    then have trueEvalCond: "(cond = IntVal 32 0) \<Longrightarrow>
                         [m,p] \<turnstile> exp[BinaryExpr BinIntegerEquals (c ? x : y) (y)]
                               \<mapsto> intval_equals yv yv"
      by (smt (verit) cNotRange trueCond ConditionalExprE cond bin_eval.simps(11) evalDet p
          falseCond unfold_binary val_to_bool.simps(1))
    then have falseEval: "(notCond = IntVal 32 0) \<Longrightarrow>
                         [m,p] \<turnstile> exp[BinaryExpr BinIntegerEquals (c ? x : y) (y)]
                               \<mapsto> intval_equals xv yv"
      using p by (metis ConditionalExprE bin_eval.simps(11) evalDet falseCond unfold_binary)
    have eqEvalFalse: "intval_equals yv xv = (IntVal 32 0)"
      unfolding xvv yvv apply auto by (metis (mono_tags) bool_to_val.simps(2) yxDiff yvv xvv)
    have trueEvalEquiv: "[m,p] \<turnstile> exp[BinaryExpr BinIntegerEquals (c ? x : y) (y)] \<mapsto> notCond"
      apply (cases notCond) prefer 2
      apply (metis IntVal0 Value.distinct(1) eqEvalFalse evalDet evaltree_not_undef falseEval p(6)
             intval_commute intval_logic_negation.simps(1) intval_self_is_true logic_negate_def
             negation_preserve_eval2 notCond trueEvalCond yvv cNotRange cond)
      using notCond cNotRange by auto
    show ?thesis
      using ConditionalExprE
      by (metis cNotRange falseEval notCond trueEvalEquiv trueCond falseCond intval_self_is_true
          yvv p(9,11) evalDet)
  qed
  done

optimization ConditionalExtractCondition: "exp[(c ? true : false)] \<longmapsto> c
                                          when isBoolean c"
  using isBoolean_def by fastforce

optimization ConditionalExtractCondition2: "exp[(c ? false : true)] \<longmapsto> !c
                                          when isBoolean c"
  apply auto
  subgoal premises p for m p cExpr cond
  proof-
    obtain cond where cond: "[m,p] \<turnstile> c \<mapsto> cond"
      using p(2) by auto
    obtain notCond where notCond: "[m,p] \<turnstile> exp[!c] \<mapsto> notCond"
      by (metis cond negation_preserve_eval2 p(1))
    then have cRange: "cond = IntVal 32 0 \<or> cond = IntVal 32 1"
      using isBoolean_def cond p(1) by auto
    then have cExprRange: "cExpr = IntVal 32 0 \<or> cExpr = IntVal 32 1"
      by (metis (full_types) ConstantExprE p(4))
    then have condTrue: "cond = IntVal 32 1 \<Longrightarrow> cExpr = IntVal 32 0"
      using cond evalDet p(2) p(4) by fastforce
    then have condFalse: "cond = IntVal 32 0 \<Longrightarrow> cExpr = IntVal 32 1"
      using p cond evalDet by fastforce
    then have opposite: "cond = intval_logic_negation cExpr"
      by (metis (full_types) IntVal0 IntVal1 cRange condTrue intval_logic_negation.simps(1)
          logic_negate_def)
    then have eq: "notCond = cExpr"
      by (metis (no_types, lifting) IntVal0 IntVal1 cExprRange cond evalDet negation_preserve_eval
          intval_logic_negation.simps(1) logic_negate_def notCond)
    then show ?thesis
      using notCond by auto
  qed
  done

optimization ConditionalEqualIsRHS: "((x eq y) ? x : y) \<longmapsto> y"
  apply auto
  subgoal premises p for m p v true false xa ya
  proof-
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p(8) by auto
    obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> yv"
      using p(9) by auto
    have notUndef: "xv \<noteq> UndefVal \<and> yv \<noteq> UndefVal"
      using evaltree_not_undef xv yv by blast
    have evalNotUndef: "intval_equals xv yv \<noteq> UndefVal"
      by (metis evalDet p(1,8,9) xv yv)
    obtain xb xvv where xvv: "xv = IntVal xb xvv"
      by (metis Value.exhaust evalNotUndef intval_equals.simps(3,4,5) notUndef)
    obtain yb yvv where yvv: "yv = IntVal yb yvv"
      by (metis evalNotUndef intval_equals.simps(7,8,9) intval_logic_negation.cases notUndef)
    have unfoldEqual: "(intval_equals xv yv) = bool_to_val (xvv = yvv)"
      using evalNotUndef xvv yvv by auto
    then show ?thesis
      by (smt (z3) p Value.inject(1) bool_to_val.simps(2) bool_to_val_bin.simps intval_equals.elims
          val_to_bool.elims(1) evalDet)
  qed
  done

(* todo not sure if this is done properly *)
optimization normalizeX: "((x eq const (IntVal 32 0)) ? 
                                (const (IntVal 32 0)) : (const (IntVal 32 1))) \<longmapsto> x
                                when stamp_expr x = IntegerStamp 32 0 1 \<and> wf_stamp x \<and>
                                     isBoolean x"
  apply auto
  subgoal premises p for m p v
    proof -
      obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
        using p by blast
       have eval: "[m,p] \<turnstile> if val_to_bool (intval_equals xa (IntVal 32 0))
                        then ConstantExpr (IntVal 32 0)
                        else ConstantExpr (IntVal 32 1) \<mapsto> v"
         using evalDet p(3,4,5,6,7) xa by blast
       then have xaRange: "xa = IntVal 32 0 \<or> xa = IntVal 32 1"
         using isBoolean_def p(3) xa by blast
      then have 6: "v = xa"
        using eval xaRange by auto
      then show ?thesis
        by (auto simp: xa)
    qed
  done

(* todo not sure if this is done properly *)
optimization normalizeX2: "((x eq (const (IntVal 32 1))) ? 
                                  (const (IntVal 32 1)) : (const (IntVal 32 0))) \<longmapsto> x
                                   when (x = ConstantExpr (IntVal 32 0) | 
                                        (x = ConstantExpr (IntVal 32 1)))" .

(* todo not sure if this is done properly *)
optimization flipX: "((x eq (const (IntVal 32 0))) ? 
                            (const (IntVal 32 1)) : (const (IntVal 32 0))) \<longmapsto> x \<oplus> (const (IntVal 32 1))
                             when (x = ConstantExpr (IntVal 32 0) | 
                                  (x = ConstantExpr (IntVal 32 1)))" .

(* todo not sure if this is done properly *)
optimization flipX2: "((x eq (const (IntVal 32 1))) ? 
                             (const (IntVal 32 0)) : (const (IntVal 32 1))) \<longmapsto> x \<oplus> (const (IntVal 32 1))
                              when (x = ConstantExpr (IntVal 32 0) | 
                                   (x = ConstantExpr (IntVal 32 1)))" .

lemma stamp_of_default:
  assumes "stamp_expr x = default_stamp"
  assumes "wf_stamp x"
  shows "([m, p] \<turnstile> x \<mapsto> v) \<longrightarrow> (\<exists>vv. v = IntVal 32 vv)"
  by (metis assms default_stamp valid_value_elims(3) wf_stamp_def)

optimization OptimiseIntegerTest: 
     "(((x & (const (IntVal 32 1))) eq (const (IntVal 32 0))) ? 
      (const (IntVal 32 0)) : (const (IntVal 32 1))) \<longmapsto> 
       x & (const (IntVal 32 1))
       when (stamp_expr x = default_stamp \<and> wf_stamp x)"
  apply (simp; rule impI; (rule allI)+; rule impI)
  subgoal premises eval for m p v
proof -
  obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> xv"
    using eval by fast
  then have x32: "\<exists>v. xv = IntVal 32 v"
    using stamp_of_default eval by auto
  obtain lhs where lhs: "[m, p] \<turnstile> exp[(((x & (const (IntVal 32 1))) eq (const (IntVal 32 0))) ? 
                                 (const (IntVal 32 0)) : (const (IntVal 32 1)))] \<mapsto> lhs"
    using eval(2) by auto
  then have lhsV: "lhs = val[((xv & (IntVal 32 1)) eq (IntVal 32 0)) ? 
                        (IntVal 32 0) : (IntVal 32 1)]"
    using ConditionalExprE ConstantExprE bin_eval.simps(4,11) evalDet xv unfold_binary
          intval_conditional.simps
    by fastforce
  obtain rhs where rhs: "[m, p] \<turnstile> exp[x & (const (IntVal 32 1))] \<mapsto> rhs"
    using eval(2) by blast
  then have rhsV: "rhs = val[xv & IntVal 32 1]"
    by (metis BinaryExprE ConstantExprE bin_eval.simps(4) evalDet xv)
  have "lhs = rhs" 
    using val_optimise_integer_test x32 lhsV rhsV by presburger
  then show ?thesis
    by (metis eval(2) evalDet lhs rhs)
qed
  done

(* todo not sure if this is done properly *)
optimization opt_optimise_integer_test_2: 
     "(((x & (const (IntVal 32 1))) eq (const (IntVal 32 0))) ? 
             (const (IntVal 32 0)) : (const (IntVal 32 1))) \<longmapsto> x
              when (x = ConstantExpr (IntVal 32 0) | (x = ConstantExpr (IntVal 32 1)))" .

(*
optimization opt_conditional_eliminate_known_less: "((x < y) ? x : y) \<longmapsto> x 
                                 when (((stamp_under (stamp_expr x) (stamp_expr y)) |
                                      ((stpi_upper (stamp_expr x)) = (stpi_lower (stamp_expr y))))
                                      \<and> wf_stamp x \<and> wf_stamp y)"
   apply auto using stamp_under_defn
  apply simp sorry
*)

(*
optimization opt_normalize_x_original: "((BinaryExpr BinIntegerEquals x (ConstantExpr (IntVal32 0))) ? 
                                (ConstantExpr (IntVal32 0)) : (ConstantExpr (IntVal32 1))) \<longmapsto> x
                                when (stamp_expr x = IntegerStamp 32 0 1 \<and> 
                                      wf_stamp x)"
   apply unfold_optimization apply simp_all
  using wf_stamp_def apply (cases x; simp) 
  
  sorry
*)

(** End of new proofs **)

end

end
