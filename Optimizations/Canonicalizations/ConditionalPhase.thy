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

lemma signed_less_than_trans:
  assumes "signed_take_bit (b-1) v = v"
  assumes "signed_take_bit (b-1) u = u"
  assumes "64 \<turnstile> u <j v"
  assumes "0 < b \<and> b \<le> 64"
  shows "b \<turnstile> u <j v"
  using assms
  by (smt (verit, ccfv_threshold) int_signed_value.elims raise_lt signed_word_eqI)

optimization ConditionBoundsX: 
  when "valid_stamp (stamp_expr u)"
  when "valid_stamp (stamp_expr v)"
  when "StampUnder u v"
  when "wf_stamp u \<and> wf_stamp v"
  "((u < v) ? x : y) \<longmapsto> x"
  using stamp_under_lower
  by (smt (verit, best) BinaryExprE EvalTreeE(3) le_expr_def stamp_under_defn)

thm_oracles ConditionBoundsX

optimization ConditionBoundsY:
  when "wf_stamp u \<and> wf_stamp v"
  when "valid_stamp (stamp_expr u) \<and> valid_stamp (stamp_expr v)"
  when "StampUnder v u"
  "((u < v) ? x : y) \<longmapsto> y"
  using stamp_under_defn_inverse
  BinaryExprE ConditionalExprE le_expr_def stamp_under_lower
  by (smt (verit, best))

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
  when "valid_stamp (stamp_expr x) \<and> valid_stamp (stamp_expr y)"
  when "StampUnder x y"
  "((x < y) ? x : y) \<longmapsto> x"
  using stamp_under_defn stamp_under_lower
  by (meson ConditionBoundsX(1) rewrite_preservation.simps(2))


lemma ExpIntBecomesIntVal:
  assumes "stamp_expr x = IntegerStamp b xl xh xd xu"
  assumes "wf_stamp x"
  assumes "valid_value v (IntegerStamp b xl xh xd xu)"
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

lemma jlt_trans:
  assumes "(b \<turnstile> h <j l)"
  shows "\<not>((b \<turnstile> l \<le>j val) \<and> (b \<turnstile> val \<le>j h))"
  using assms
  by linarith

lemma is_stamp_empty_valid:
  assumes "is_stamp_empty s"
  shows "\<not>(\<exists> val. valid_value val s)"
  using assms is_stamp_empty.simps apply (cases s; auto)
  by (metis One_nat_def int_signed_value.simps jlt_trans valid_value.simps(1) valid_value_elims(3))

lemma join_valid_stamp:
  assumes "is_IntegerStamp s1 \<and> is_IntegerStamp s2"
  assumes "valid_stamp s1 \<and> valid_stamp s2"
  shows "valid_stamp (join s1 s2)"
  using assms apply (cases s1; cases s2; simp)
  by (metis smax_def smin_def)

lemma join_valid_lower:
  assumes "s1 = IntegerStamp b l1 h1 d1 u1"
  assumes "s2 = IntegerStamp b l2 h2 d2 u2"
  assumes "join s1 s2 = IntegerStamp b l h d u"
  shows "(b \<turnstile> l1 \<le>j val) \<and> (b \<turnstile> l2 \<le>j val) \<equiv> b \<turnstile> l \<le>j val"
  using assms apply auto
  by (smt (verit, del_insts) One_nat_def int_signed_value.elims smax_def)

lemma join_valid_upper:
  assumes "s1 = IntegerStamp b l1 h1 d1 u1"
  assumes "s2 = IntegerStamp b l2 h2 d2 u2"
  assumes "join s1 s2 = IntegerStamp b l h d u"
  shows "(b \<turnstile> val \<le>j h1) \<and> (b \<turnstile> val \<le>j h2) \<equiv> b \<turnstile> val \<le>j h"
  using assms apply auto
  by (smt (verit, del_insts) One_nat_def int_signed_value.elims smin_def)

lemma join_valid_down:
  assumes "s1 = IntegerStamp b l1 h1 d1 u1"
  assumes "s2 = IntegerStamp b l2 h2 d2 u2"
  assumes "join s1 s2 = IntegerStamp b l h d u"
  shows "((and (not val) d1) = 0) \<and> ((and (not val) d2) = 0) \<equiv> (and (not val) d) = 0"
  using assms apply auto
  by (smt (verit, del_insts) bit.conj_disj_distrib or_eq_0_iff)

lemma join_valid_up:
  assumes "s1 = IntegerStamp b l1 h1 d1 u1"
  assumes "s2 = IntegerStamp b l2 h2 d2 u2"
  assumes "join s1 s2 = IntegerStamp b l h d u"
  shows "((and val u1) = val) \<and> ((and val u2) = val) \<equiv> (and val u) = val"
  using assms apply auto
  by (smt (verit) word_ao_absorbs(6) word_ao_absorbs(8) word_bw_assocs(1))

lemma join_valid:
  assumes "is_IntegerStamp s1 \<and> is_IntegerStamp s2"
  assumes "valid_stamp s1 \<and> valid_stamp s2"
  shows "(valid_value v s1 \<and> valid_value v s2) = valid_value v (join s1 s2)" (is "?lhs = ?rhs")
proof
  assume lhs: ?lhs
  obtain b l1 h1 d1 u1 where s1def:"s1 = IntegerStamp b l1 h1 d1 u1"
    using assms
    using is_IntegerStamp_def by fastforce
  then obtain l2 h2 d2 u2 where s2def:"s2 = IntegerStamp b l2 h2 d2 u2"
    using assms
    by (metis Stamp.collapse(1) lhs valid_int valid_int_same_bits)
  also obtain l h d u where joindef:"join s1 s2 = IntegerStamp b l h d u"
    by (simp add: s1def s2def)
  then show ?rhs
    using s1def s2def assms joindef
    using join_valid_stamp join_valid_lower join_valid_upper join_valid_down join_valid_up
    by (smt (verit, del_insts) lhs valid_int valid_value.simps(1))
next
  assume rhs: ?rhs
  obtain b l1 h1 d1 u1 where s1def:"s1 = IntegerStamp b l1 h1 d1 u1"
    using assms
    using is_IntegerStamp_def by fastforce
  also obtain l h d u where joindef:"join s1 s2 = IntegerStamp b l h d u"
    by (metis assms(1) calculation is_IntegerStamp_def join.simps(2) rhs valid_value.simps(22))
  then obtain l2 h2 d2 u2 where s2def:"s2 = IntegerStamp b l2 h2 d2 u2"
    apply (cases s2; auto simp: assms(1)) 
    using calculation apply force
    using assms(1) by fastforce+
  then show ?lhs
    using s1def s2def assms joindef
    using join_valid_stamp join_valid_lower join_valid_upper join_valid_down join_valid_up
    by (smt (verit, del_insts) rhs valid_int valid_value.simps(1))
qed

lemma alwaysDistinct_evaluate:
  assumes "wf_stamp x \<and> wf_stamp y"
  assumes "alwaysDistinct (stamp_expr x) (stamp_expr y)"
  assumes "is_IntegerStamp (stamp_expr x) \<and> is_IntegerStamp (stamp_expr y) \<and> valid_stamp (stamp_expr x) \<and> valid_stamp (stamp_expr y)"
  shows "\<not>(\<exists> val . ([m, p] \<turnstile> x \<mapsto> val) \<and> ([m, p] \<turnstile> y \<mapsto> val))"
proof -
  have "\<forall>v. valid_value v (join (stamp_expr x) (stamp_expr y)) = (valid_value v (stamp_expr x) \<and> valid_value v (stamp_expr y))"
    using assms(3)
    by (simp add: join_valid)
  then show ?thesis
    using assms unfolding alwaysDistinct.simps
    by (metis is_stamp_empty_valid wf_stamp_def)
qed

lemma join_commute:
  assumes "valid_stamp x \<and> valid_stamp y"
  assumes "is_IntegerStamp x \<and> is_IntegerStamp y"
  shows "join x y = join y x"
  using assms(2) apply (cases x; cases y; auto)
  apply (metis assms(1) smax_signed_commute valid_stamp.simps(1))
  apply (metis assms(1) smin_signed_commute valid_stamp.simps(1))
  using or.commute apply blast
  by (meson and.commute)

lemma alwaysDistinct_commute:
  assumes "valid_stamp x \<and> valid_stamp y"
  assumes "is_IntegerStamp x \<and> is_IntegerStamp y"
  shows "alwaysDistinct x y = alwaysDistinct y x"
  using assms join_commute
  by simp

lemma alwaysDistinct_valid:
  assumes "wf_stamp x \<and> wf_stamp y"
  assumes "alwaysDistinct (stamp_expr x) (stamp_expr y)"
  assumes "[m, p] \<turnstile> exp[x eq y] \<mapsto> val"
  shows "\<not>(val_to_bool val)"
proof -
  have no_valid: "\<forall> val. \<not>(valid_value val (join (stamp_expr x) (stamp_expr y)))"
    using assms(2) unfolding alwaysDistinct.simps using is_stamp_empty.simps
    by (smt (verit, ccfv_threshold) is_stamp_empty.elims(2) valid_int_stamp_gives)
  obtain xv yv where evalsub: "[m, p] \<turnstile> x \<mapsto> xv \<and> [m, p] \<turnstile> y \<mapsto> yv"
    using assms(3) by blast
  have xvalid: "valid_value xv (stamp_expr x)"
    using assms(1) evalsub wf_stamp_def by blast
  then have xint: "is_IntegerStamp (stamp_expr x)"
    using assms(1) valid_value.elims(2)
    by (metis Stamp.disc(2) alwaysDistinct.elims(2) assms(2) is_stamp_empty.simps(8) join.simps(34))
  then have xstamp: "valid_stamp (stamp_expr x)"
    using xvalid apply (cases xv; auto) 
    apply (smt (z3) valid_stamp.simps(6) valid_value.elims(1))
    using is_IntegerStamp_def by fastforce
  have yvalid: "valid_value yv (stamp_expr y)"
    using assms(1) evalsub wf_stamp_def by blast
  then have yint: "is_IntegerStamp (stamp_expr y)"
    using assms(1) valid_value.elims(2)
    by (metis Stamp.collapse(1) Stamp.disc(2) alwaysDistinct.elims(2) assms(2) is_stamp_empty.simps(8) join.simps(10) xint)
  then have ystamp: "valid_stamp (stamp_expr y)"
    using yvalid apply (cases yv; auto) 
    apply (smt (z3) valid_stamp.simps(6) valid_value.elims(1))
    using is_IntegerStamp_def by fastforce
  have disjoint: "\<not>(\<exists> val . ([m, p] \<turnstile> x \<mapsto> val) \<and> ([m, p] \<turnstile> y \<mapsto> val))"
    using alwaysDistinct_evaluate
    using assms(1) assms(2) xint xstamp yint ystamp by blast
  (*have "val = bin_eval BinIntegerEquals xv yv"
    sledgehammer
    by (metis BinaryExprE encodeeval.simps assms(3) evalsub graphDet)
  also have "v \<noteq> UndefVal"
    using evale by auto*)
  then have "\<exists>b1 b2. val =  bool_to_val_bin b1 b2 (xv = yv)"
    unfolding bin_eval.simps
    by (smt (verit, ccfv_SIG) BinaryExprE ExpIntBecomesIntVal assms(1) assms(3) bin_eval.simps(13) bool_to_val_bin.elims evalDet eval_thms(117) evalsub is_IntegerStamp_def xint xvalid yint yvalid)
  then show ?thesis
    by (metis (mono_tags, lifting) assms(3) bool_to_val.simps(2) bool_to_val_bin.elims disjoint evalsub unfold_evaltree(1) val_to_bool.simps(1))
qed

optimization ConditionalIntegerEquals1[notactic,nogen]:
  when "wf_stamp x \<and> wf_stamp y"
  when "alwaysDistinct (stamp_expr x) (stamp_expr y)"
  when "isBoolean c"
  "((c ? x : y) eq (x)) \<longmapsto> c"
   apply (metis add_lessD1 size.simps(10) size_binary_lhs)
  apply simp apply (rule allI; rule allI; rule allI; rule impI)
  subgoal premises p for m p v
proof -
  obtain cv where cv: "[m, p] \<turnstile> c \<mapsto> cv"
    using p
    by blast
  then show ?thesis
  proof (cases "val_to_bool cv")
    case True
    obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> xv"
      using p(3) by blast
    then have "[m, p] \<turnstile> exp[c ? x : y] \<mapsto> xv"
      using True cv evalDet p(3) by auto
    then have "[m, p] \<turnstile> exp[(c ? x : y) eq x] \<mapsto> IntVal 32 1"
      by (metis EvalTreeE(5) bin_eval.simps(13) defined_eval_is_intval evalDet evaltree_not_undef intval_self_is_true is_IntVal_def p(3) xv)
    also have "[m, p] \<turnstile> c \<mapsto> IntVal 32 1"
      using True cv
      using isBoolean_def p(1) by fastforce
    ultimately show ?thesis
      by (metis evalDet p(3))
  next
    case False
    obtain yv where yv: "[m, p] \<turnstile> y \<mapsto> yv"
      using p(3) by blast
    then have "[m, p] \<turnstile> exp[c ? x : y] \<mapsto> yv"
      using False cv evalDet p(3) by auto
    obtain eqval where "[m, p] \<turnstile> exp[y eq x] \<mapsto> eqval"
      by (metis EvalTreeE(5) \<open>[m,p] \<turnstile> ConditionalExpr c x y \<mapsto> yv\<close> evalDet evaltree.intros(5) p(3) yv)
    also have "alwaysDistinct (stamp_expr y) (stamp_expr x)"
      by (metis BinaryExprE Stamp.disc(2) \<open>[m,p] \<turnstile> ConditionalExpr c x y \<mapsto> yv\<close> alwaysDistinct.elims(3) defined_eval_is_intval evalDet is_IntVal_def join_commute p(2) p(3) valid_int_gives wf_stamp_def yv)
    then have "\<not>(val_to_bool eqval)"
      using p(2,3) alwaysDistinct_valid
      using calculation by blast
    then have e: "[m, p] \<turnstile> exp[(c ? x : y) eq x] \<mapsto> IntVal 32 0"
      using \<open>[m,p] \<turnstile> ConditionalExpr c x y \<mapsto> yv\<close> calculation evalDet intval_equals_result yv by fastforce
    then have "[m, p] \<turnstile> c \<mapsto> IntVal 32 0"
      using False cv
      using isBoolean_def p(1) by fastforce
    then show ?thesis
      by (metis e evalDet p(3))
  qed
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

optimization ConditionalIntegerEquals2[nogen]:
  when "wf_stamp x \<and> wf_stamp y"
  when "alwaysDistinct (stamp_expr x) (stamp_expr y)"
  when "isBoolean c"
  "((c ? x : y) eq (y)) \<longmapsto> (!c)"
  apply (metis add_2_eq_Suc' less_add_same_cancel1 order_less_trans plus_nat.simps(2) size.simps(10) size_binary_lhs size_pos)
apply simp apply (rule allI; rule allI; rule allI; rule impI)
  subgoal premises p for m p v
proof -
  obtain cv where cv: "[m, p] \<turnstile> c \<mapsto> cv"
    using p
    by blast
  then show ?thesis
  proof (cases "val_to_bool cv")
    case True
    obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> xv"
      using p(3) by blast
    then have "[m, p] \<turnstile> exp[c ? x : y] \<mapsto> xv"
      using True cv evalDet p(3) by auto
    obtain eqval where "[m, p] \<turnstile> exp[x eq y] \<mapsto> eqval"
      by (metis BinaryExpr EvalTreeE(5) \<open>[m,p] \<turnstile> ConditionalExpr c x y \<mapsto> xv\<close> evalDet p(3) xv)
    then have "\<not>(val_to_bool eqval)"
      using p(2,3) alwaysDistinct_valid
      by (meson alwaysDistinct.simps)
    then have e: "[m, p] \<turnstile> exp[(c ? x : y) eq y] \<mapsto> IntVal 32 0"
      using \<open>[m,p] \<turnstile> BinaryExpr BinIntegerEquals x y \<mapsto> eqval\<close> \<open>[m,p] \<turnstile> ConditionalExpr c x y \<mapsto> xv\<close> evalDet intval_equals_result xv by fastforce
    then have "[m, p] \<turnstile> exp[!c] \<mapsto> IntVal 32 0"
      using True cv
      by (metis (no_types, lifting) IntVal0 UnaryExpr Value.simps(6) empty_iff insertE intval_logic_negation.simps(1) isBoolean_def logic_negate_def p(1) unary_eval.simps(4) val_to_bool.simps(1))
    then show ?thesis
      by (metis e evalDet p(3))
  next
    case False
    obtain yv where yv: "[m, p] \<turnstile> y \<mapsto> yv"
      using p(3) by blast
    then have "[m, p] \<turnstile> exp[c ? x : y] \<mapsto> yv"
      using False cv evalDet p(3) by auto
    then have "[m, p] \<turnstile> exp[(c ? x : y) eq y] \<mapsto> IntVal 32 1"
      by (metis EvalTreeE(5) bin_eval.simps(13) defined_eval_is_intval evalDet evaltree_not_undef intval_self_is_true is_IntVal_def p(3) yv)
    also have "[m, p] \<turnstile> exp[!c] \<mapsto> IntVal 32 1"
      using False cv
      by (metis (no_types, lifting) IntVal1 UnaryExpr empty_iff insertE intval_logic_negation.simps(1) isBoolean_def logic_negate_def p(1) semiring_norm(160) unary_eval.simps(4) val_to_bool.simps(1) val_to_bool.simps(2))
    ultimately show ?thesis
      by (metis evalDet p(3))
  qed
qed
  done

(*
lemma IsBoolStamp_def:
  assumes "stamp_expr e = (IntegerStamp 32 0 1) \<and> wf_stamp e"
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
*)

lemma isBooleanCaseTrue:
  assumes "isBoolean c"
  assumes "[m, p] \<turnstile> c \<mapsto> cv"
  shows "val_to_bool cv \<longrightarrow> cv = IntVal 32 1"
  using assms
  using isBoolean_def by fastforce

lemma isBooleanCaseFalse:
  assumes "isBoolean c"
  assumes "[m, p] \<turnstile> c \<mapsto> cv"
  shows "\<not>(val_to_bool cv) \<longrightarrow> cv = IntVal 32 0"
  using assms
  using isBoolean_def by fastforce

optimization ConditionalExtractCondition: 
  when "isBoolean c"
  "(c ? true : false) \<longmapsto> c"
  apply auto
  using isBooleanCaseFalse isBooleanCaseTrue by fastforce

optimization ConditionalExtractCondition2: 
  when "isBoolean c"
  "(c ? false : true) \<longmapsto> !c"
  apply auto
  by (smt (verit, ccfv_threshold) EvalTreeE(1) isBooleanCaseFalse isBooleanCaseTrue negates negation_preserve_eval2 preserveBoolean zero_less_numeral)

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
    by (metis BinaryExprE ConstantExprE bin_eval.simps(6) evalDet xv)
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
