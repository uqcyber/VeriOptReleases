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

value DefaultTrueBranch_code

optimization DefaultFalseBranch: "(false ? x : y) \<longmapsto> y" .

optimization ConditionalEqualBranches: "(e ? x : x) \<longmapsto> x" .

optimization ConditionBoundsX: 
  (*when "cond[((Expr u)..stamp()..upper()) < ((Expr v)..stamp()..lower())]"*)
  when "wf_stamp u"
  when "wf_stamp v"
  when "cond[u..stamp() instanceof IntegerStamp]"
  when "cond[v..stamp() instanceof IntegerStamp]"
  when "cond[(u..stamp()..upperBound()) < (v..stamp()..lowerBound())]"
  "((u < v) ? x : y) \<longmapsto> x"
  apply (rule impI)+
  subgoal premises assms apply simp apply (rule allI)+ apply (rule impI)+
    subgoal premises eval
  proof -
    have under: "stpi_upper (stamp_expr u) < stpi_lower (stamp_expr v)"
      using stamp_under assms by blast
    have u: "is_IntegerStamp (stamp_expr u)" using assms(1,2) eval
      by (smt (verit) BinaryExprE ConditionalExprE Stamp.disc(2) Stamp.exhaust_sel bin_eval_implies_valid_value never_void stamp_binary.simps(6) stamp_expr.simps(2) valid_value.simps(14) valid_value.simps(15) valid_value.simps(16) valid_value.simps(21) valid_value.simps(22) wf_stamp_def)
    have v: "is_IntegerStamp (stamp_expr v)" using assms(1,2) eval 
      by (smt (verit) BinaryExprE ConditionalExprE Stamp.disc(2) Stamp.exhaust_sel bin_eval_implies_valid_value stamp_binary.simps(13) stamp_binary.simps(9) stamp_expr.simps(2) valid_value.simps(14) valid_value.simps(15) valid_value.simps(16) valid_value.simps(21) valid_value.simps(22) wf_stamp_def)
    have "stamp_under (stamp_expr u) (stamp_expr v)"
      using u v under
      by (smt (verit) BinaryExprE ConditionalExprE Stamp.disc(1) Stamp.disc(3) Stamp.disc(4) Stamp.disc(5) Stamp.disc(6) Stamp.exhaust_sel assms(1,2) eval stamp_under.simps(1) valid_value.simps(21) valid_value.simps(22) wf_stamp_def)
    then show ?thesis
      using assms(1,2) eval stamp_under_defn by fastforce
  qed
  done
  done

optimization ConditionBoundsY:
  when "wf_stamp u \<and> wf_stamp v"
  when "StampUnder v u"
  "((u < v) ? x : y) \<longmapsto> y"
  using stamp_under_defn_inverse
  by (smt (verit, ccfv_threshold) BinaryExprE ConditionalExprE le_expr_def stamp_under_lower)

(** Start of new proofs **)

(* Value-level proofs *)
lemma val_optimise_integer_test: 
  assumes "\<exists>v. x = IntVal 32 v"
  shows "val[((x & (IntVal 32 1)) eq (IntVal 32 0)) ? (IntVal 32 0) : (IntVal 32 1)] = 
         val[x & IntVal 32 1]"
  using assms apply auto[1]
  apply (metis (full_types) bool_to_val.simps(2) val_to_bool.simps(1))
  by (metis (mono_tags, lifting) bool_to_val.simps(1) val_to_bool.simps(1) even_iff_mod_2_eq_zero
      odd_iff_mod_2_eq_one and_one_eq)

optimization ConditionalEliminateKnownLess: 
  when "wf_stamp x \<and> wf_stamp y"
  "((x < y) ? x : y) \<longmapsto> x when (StampUnder x y)"
  using stamp_under_defn stamp_under_lower
  by (meson ConditionBoundsX(1) rewrite_preservation.simps(2))


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
  using assms isBoolean_def apply auto[1]
  by (metis (no_types, lifting) IntVal0 IntVal1 intval_logic_negation.simps(1) logic_negate_def)

optimization ConditionalIntegerEquals1[notactic]: "exp[BinaryExpr BinIntegerEquals (c ? x : y) (x)] \<longmapsto> c
                                          when IsIntegerStamp x && WellFormed x &&
                                               IsIntegerStamp y && WellFormed y &&
                                               AlwaysDistinct x y &&
                                               IsBoolStamp c && WellFormed c"
  defer apply simp
  apply (metis Canonicalization.cond_size add_lessD1 size_binary_lhs) apply auto[1]
  subgoal premises p for m p cExpr xv cond
  proof -
    obtain cond where cond: "[m,p] \<turnstile> c \<mapsto> cond"
      using p by blast
    then have cRange: "cond = IntVal 32 0 \<or> cond = IntVal 32 1"
      using p(6,7) sorry
    then obtain yv where yVal: "[m,p] \<turnstile> y \<mapsto> yv"
      using p by auto
    obtain xvv b where xvv: "xv = IntVal b xvv"
      by (metis Value.exhaust evaltree_not_undef intval_equals.simps(7) intval_equals.simps(8) intval_equals.simps(9) p(8) p(9))
    obtain yvv where yvv: "yv = IntVal b yvv"
      using xvv yVal sorry
    have yxDiff: "xvv \<noteq> yvv"
      using xvv yvv yVal p(8)  p sorry
    have eqEvalFalse: "intval_equals yv xv = (IntVal 32 0)"
      unfolding xvv yvv apply auto[1] by (metis (mono_tags) bool_to_val.simps(2) yxDiff)
    then have valEvalSame: "cond = intval_equals val[cond ? xv : yv] xv"
      apply (cases "cond = IntVal 32 0"; simp) using cRange xvv by auto
    then have condTrue: "val_to_bool cond \<Longrightarrow> cExpr = xv"
      by (metis cond evalDet p(10) p(12) p(8))
    then have condFalse: "\<not>(val_to_bool cond) \<Longrightarrow> cExpr = yv"
      sorry
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

optimization ConditionalIntegerEquals2[notactic]: "exp[BinaryExpr BinIntegerEquals (c ? x : y) (y)] \<longmapsto> (!c)
                                          when IsIntegerStamp x && WellFormed x &&
                                               IsIntegerStamp y && WellFormed y &&
                                               AlwaysDistinct x y &&
                                               IsBoolStamp c"
  defer apply simp
  apply (smt (verit) not_add_less1 max_less_iff_conj max.absorb3 linorder_less_linear add_2_eq_Suc'
         add_less_cancel_right size_binary_lhs add_lessD1 Canonicalization.cond_size)
  apply auto[1]
  subgoal premises p for m p cExpr yv cond trE faE
  proof -
    obtain cond where cond: "[m,p] \<turnstile> c \<mapsto> cond"
      using p by blast
    then have condNotUndef: "cond \<noteq> UndefVal"
      by (simp add: evaltree_not_undef)
    then obtain notCond where notCond: "[m,p] \<turnstile> exp[!c] \<mapsto> notCond"
      sorry
    have cRange: "cond = IntVal 32 0 \<or> cond = IntVal 32 1"
      using p cond sorry
    then have cNotRange:  "notCond = IntVal 32 0 \<or> notCond = IntVal 32 1"
      by (metis (no_types, lifting) IntVal0 IntVal1 cond evalDet intval_logic_negation.simps(1)
          logic_negate_def negation_preserve_eval notCond)
    then obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p by auto
    then have trueCond: "(notCond = IntVal 32 1) \<Longrightarrow> [m,p] \<turnstile> (ConditionalExpr c x y) \<mapsto> yv"
      by (smt (verit, best) cRange evalDet negates negation_preserve_eval notCond p(7) cond
          zero_less_numeral val_to_bool.simps(1) evaltree_not_undef ConditionalExpr
          ConditionalExprE)
    obtain b xvv where xvv: "xv = IntVal b xvv"
      sorry
    then have opposites: "notCond = intval_logic_negation cond"
      by (metis cond evalDet negation_preserve_eval notCond)
    then have negate: "(intval_logic_negation cond = IntVal 32 0) \<Longrightarrow> (cond = IntVal 32 1)"
      using cRange intval_logic_negation.simps negates by fastforce
    have falseCond: "(notCond = IntVal 32 0) \<Longrightarrow> [m,p] \<turnstile> (ConditionalExpr c x y) \<mapsto> xv"
      unfolding opposites using negate cond evalDet p(13,14,15,16) xv by auto
    obtain yvv where yvv: "yv = IntVal b yvv"
      sorry
    have yxDiff: "xv \<noteq> yv"
      sorry
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
      unfolding xvv yvv apply auto[1] by (metis (mono_tags) bool_to_val.simps(2) yxDiff yvv xvv)
    have trueEvalEquiv: "[m,p] \<turnstile> exp[BinaryExpr BinIntegerEquals (c ? x : y) (y)] \<mapsto> notCond"
      apply (cases notCond) prefer 2
      sorry
    show ?thesis
      using ConditionalExprE
      by (metis cNotRange falseEval notCond trueEvalEquiv trueCond falseCond intval_self_is_true
          yvv p(9,11) evalDet)
  qed
  done

lemma IsBoolStamp_def:
  assumes "stamp_expr e = (IntegerStamp 32 0 1) \<and> CodeGen.wf_stamp e"
  assumes "[m, p] \<turnstile> e \<mapsto> v"
  shows "v = IntVal 32 0 \<or> v = IntVal 32 1"
proof -
  obtain b v' where vdef: "v = IntVal b v'"
    by (metis assms(1) assms(2) valid_int)
  have b: "b = 32"
    by (metis assms(1) assms(2) valid_int_same_bits vdef)
  then have "0 \<le> int_signed_value b v' \<and> int_signed_value b v' \<le> 1"
    by (metis assms(1) assms(2) valid_int_signed_range vdef)
  then have "0 \<le> v' \<and> v' \<le> 1"
    unfolding int_signed_value.simps sorry
  then show ?thesis
    using vdef b sorry
  qed

optimization ConditionalExtractCondition: "exp[(c ? true : false)] \<longmapsto> c
                                          when IsBoolStamp c && WellFormed c"
  using IsBoolStamp_def
  using le_expr_def unfold_const val_to_bool.simps(1) by fastforce

optimization ConditionalExtractCondition2: "exp[(c ? false : true)] \<longmapsto> !c
                                          when IsBoolStamp c && WellFormed c"
  apply auto[1]
  subgoal premises p for m p cExpr cond
  proof-
    obtain cond where cond: "[m,p] \<turnstile> c \<mapsto> cond"
      using p(3) by auto
    obtain notCond where notCond: "[m,p] \<turnstile> exp[!c] \<mapsto> notCond"
      sorry
    then have cRange: "cond = IntVal 32 0 \<or> cond = IntVal 32 1"
      using isBoolean_def cond p(1)
      using IsBoolStamp_def p(2) by metis
    then have cExprRange: "cExpr = IntVal 32 0 \<or> cExpr = IntVal 32 1"
      by (metis (full_types) ConstantExprE p(5))
    then have condTrue: "cond = IntVal 32 1 \<Longrightarrow> cExpr = IntVal 32 0"
      using cond evalDet p(3) p(5) by fastforce
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
  apply auto[1]
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
    obtain vv where evalLHS: "[m,p] \<turnstile> if val_to_bool (intval_equals xv yv) then x else y \<mapsto> vv"
      by (metis (full_types) p(4) yv)
    obtain equ where equ: "equ = intval_equals xv yv"
      by fastforce
    have trueEval: "equ = IntVal 32 1 \<Longrightarrow> vv = xv"
      using evalLHS by (simp add: evalDet xv equ)
    have falseEval: "equ = IntVal 32 0 \<Longrightarrow> vv = yv"
      using evalLHS by (simp add: evalDet yv equ)
    then have "vv = v"
      by (metis evalDet evalLHS p(2,8,9) xv yv)
    then show ?thesis
      by (metis (full_types) bool_to_val.simps(1,2) bool_to_val_bin.simps equ evalNotUndef falseEval
          intval_equals.simps(1) trueEval xvv yv yvv)
  qed
  done

(* todo not sure if this is done properly *)
optimization NormalizeX: "((x eq const (IntVal 32 0)) ? 
                                (const (IntVal 32 0)) : (const (IntVal 32 1))) \<longmapsto> x
                                when (UpMaskEquals x 1) && (IsStamp x (IntegerStamp 32 0 1)) && WellFormed x" 
  apply auto[1]
  subgoal premises p for m p v
    proof -
      obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
        using p by blast
       have eval: "[m,p] \<turnstile> if val_to_bool (intval_equals xa (IntVal 32 0))
                        then ConstantExpr (IntVal 32 0)
                        else ConstantExpr (IntVal 32 1) \<mapsto> v"
         using evalDet p(3,4,5,6,7) xa by blast
       then have xaRange: "xa = IntVal 32 0 \<or> xa = IntVal 32 1"
         using isBoolean_def p(2,3) xa sorry
      then have 6: "v = xa"
        using eval xaRange by auto
      then show ?thesis
        by (auto simp: xa)
    qed
    done

(* todo not sure if this is done properly *)
optimization NormalizeX2: "((x eq (const (IntVal 32 1))) ? 
                                 (const (IntVal 32 1)) : (const (IntVal 32 0))) \<longmapsto> x
                                 when IsBool x" .

(* todo not sure if this is done properly *)
optimization FlipX: "((x eq (const (IntVal 32 0))) ? 
                           (const (IntVal 32 1)) : (const (IntVal 32 0))) \<longmapsto> 
                            x \<oplus> (const (IntVal 32 1))
                            when IsBool x" .

(* todo not sure if this is done properly *)
optimization FlipX2: "((x eq (const (IntVal 32 1))) ? 
                            (const (IntVal 32 0)) : (const (IntVal 32 1))) \<longmapsto> 
                            x \<oplus> (const (IntVal 32 1))
                            when IsBool x" .


lemma stamp_of_default:
  assumes "stamp_expr x = default_stamp"
  assumes "wf_stamp x"
  shows "([m, p] \<turnstile> x \<mapsto> v) \<longrightarrow> (\<exists>vv. v = IntVal 32 vv)"
  by (metis assms default_stamp valid_value_elims(3) wf_stamp_def)

(*
optimization OptimiseIntegerTest: 
     "(((x & (const (IntVal 32 1))) eq (const (IntVal 32 0))) ? 
      (const (IntVal 32 0)) : (const (IntVal 32 1))) \<longmapsto> 
       x & (const (IntVal 32 1))
       when (IsStamp x default_stamp && WellFormed x)"
  apply simp apply (rule impI; (rule allI)+; rule impI)
  subgoal premises eval for m p v
proof -
  obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> xv"
    using eval by fast
  then have x32: "\<exists>v. xv = IntVal 32 v"
    using stamp_of_default eval
    by (metis TermRewrites.wf_stamp_def valid_value_elims(3))
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
*)

(* todo not sure if this is done properly *)
optimization OptimiseIntegerTest2: 
     "(((x & (const (IntVal 32 1))) eq (const (IntVal 32 0))) ? 
                   (const (IntVal 32 0)) : (const (IntVal 32 1))) \<longmapsto> 
                   x
                   when IsBool x" .

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
