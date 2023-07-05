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
  unfolding intval_logic_negation.simps
  by (metis (mono_tags, lifting) intval_logic_negation.simps(1) logic_negate_def new_int.simps of_bool_eq(2) one_neq_zero take_bit_of_0 take_bit_of_1 val_to_bool.simps(1))

lemma negation_condition_intval: 
  assumes "e = IntVal b ie"
  assumes "0 < b"
  shows "val[(!e) ? x : y] = val[e ? y : x]"
  using assms by (cases e; auto simp: negates logic_negate_def)

lemma negation_preserve_eval:
  assumes "[m, p] \<turnstile> exp[!e] \<mapsto> v"
  shows "\<exists>v'. ([m, p] \<turnstile> exp[e] \<mapsto> v') \<and> v = val[!v']"
  using assms by auto

lemma negation_preserve_eval_intval:
  assumes "[m, p] \<turnstile> exp[!e] \<mapsto> v"
  shows "\<exists>v' b vv. ([m, p] \<turnstile> exp[e] \<mapsto> v') \<and> v' = IntVal b vv \<and> b > 0"
  using assms
  by (metis eval_bits_1_64 intval_logic_negation.elims negation_preserve_eval unfold_unary)

optimization NegateConditionFlipBranches: "((!e) ? x : y) \<longmapsto> (e ? y : x)"
  apply simp using negation_condition_intval negation_preserve_eval_intval
  by (smt (verit, best) ConditionalExpr ConditionalExprE Value.distinct(1) evalDet negates negation_preserve_eval)

optimization DefaultTrueBranch: "(true ? x : y) \<longmapsto> x" .

value DefaultTrueBranch_code

optimization DefaultFalseBranch: "(false ? x : y) \<longmapsto> y" .

optimization ConditionalEqualBranches: "(e ? x : x) \<longmapsto> x" .

optimization condition_bounds_x: "((u < v) ? x : y) \<longmapsto> x 
    when (StampUnder u v && WellFormed u && WellFormed v)"
  using stamp_under_defn
  by (smt (verit, ccfv_SIG) BinaryExprE ConditionalExprE StampEvalThms.wf_stamp_def TermRewrites.wf_stamp_def le_expr_def)
(* by fastforce *)

optimization condition_bounds_y: "((u < v) ? x : y) \<longmapsto> y 
    when (StampUnder v u && WellFormed u && WellFormed v)"
  using stamp_under_defn_inverse
  by (smt (verit, ccfv_threshold) BinaryExprE ConditionalExprE StampEvalThms.wf_stamp_def TermRewrites.wf_stamp_def le_expr_def)
  (* by fastforce *)

(** Start of new proofs **)

(* Value-level proofs *)
lemma val_optimise_integer_test: 
  assumes "\<exists>v. x = IntVal 32 v"
  shows "val[((x & (IntVal 32 1)) eq (IntVal 32 0)) ? (IntVal 32 0) : (IntVal 32 1)] = 
         val[x & IntVal 32 1]"
  using assms apply auto[1]
  apply (metis (full_types) bool_to_val.simps(2) val_to_bool.simps(1))
  by (metis (mono_tags, lifting) and_one_eq bool_to_val.simps(1) even_iff_mod_2_eq_zero odd_iff_mod_2_eq_one val_to_bool.simps(1))

optimization ConditionalEliminateKnownLess: "((x < y) ? x : y) \<longmapsto> x 
                                 when (StampUnder x y &&
                                       WellFormed x && WellFormed y)"
  using stamp_under_defn
  by (smt (verit, best) BinaryExprE ConditionalExprE StampEvalThms.wf_stamp_def TermRewrites.wf_stamp_def le_expr_def)
  (* by fastforce *)

(* Optimisations *)
optimization ConditionalEqualIsRHS: "((x eq y) ? x : y) \<longmapsto> y"
  apply auto[1]
  by (smt (verit) Value.inject(1) bool_to_val.simps(2) bool_to_val_bin.simps evalDet 
      intval_equals.elims val_to_bool.elims(1))

(* todo not sure if this is done properly *)
optimization normalizeX: "((x eq const (IntVal 32 0)) ? 
                                (const (IntVal 32 0)) : (const (IntVal 32 1))) \<longmapsto> x
                                when (UpMaskEquals x 1) && (IsStamp x (IntegerStamp 32 0 1))" 
  apply auto[1]
  subgoal premises p for m p v xa
    proof -
      obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
        using p by blast
       have 3: "[m,p] \<turnstile> if val_to_bool (intval_equals xa (IntVal (32::nat) (0::64 word)))
                  then ConstantExpr (IntVal (32::nat) (0::64 word))
                  else ConstantExpr (IntVal (32::nat) (1::64 word)) \<mapsto> v"
         using evalDet p(3) p(5) xa
         using p(4) p(6) by blast
       then have 4: "xa = IntVal 32 0 | xa = IntVal 32 1"
         sorry
       then have 6: "v = xa"
         sorry
      then show ?thesis
        using xa by auto
    qed
    done

(* todo not sure if this is done properly *)
optimization normalizeX2: "((x eq (const (IntVal 32 1))) ? 
                                 (const (IntVal 32 1)) : (const (IntVal 32 0))) \<longmapsto> x
                                 when IsBool x" .

(* todo not sure if this is done properly *)
optimization flipX: "((x eq (const (IntVal 32 0))) ? 
                           (const (IntVal 32 1)) : (const (IntVal 32 0))) \<longmapsto> 
                            x \<oplus> (const (IntVal 32 1))
                            when IsBool x" .

(* todo not sure if this is done properly *)
optimization flipX2: "((x eq (const (IntVal 32 1))) ? 
                            (const (IntVal 32 0)) : (const (IntVal 32 1))) \<longmapsto> 
                            x \<oplus> (const (IntVal 32 1))
                            when IsBool x" .

lemma stamp_of_default:
  assumes "stamp_expr x = default_stamp"
  assumes "wf_stamp x"
  shows "([m, p] \<turnstile> x \<mapsto> v) \<longrightarrow> (\<exists>vv. v = IntVal 32 vv)"
  using assms
  by (metis default_stamp valid_value_elims(3) wf_stamp_def)

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
  then have lhsV: "lhs = val[((xv & (IntVal 32 1)) eq (IntVal 32 0)) ? (IntVal 32 0) : (IntVal 32 1)]"
    using xv evaltree.BinaryExpr evaltree.ConstantExpr evaltree.ConditionalExpr
    by (smt (verit) ConditionalExprE ConstantExprE bin_eval.simps(11) bin_eval.simps(4) evalDet intval_conditional.simps unfold_binary)
  obtain rhs where rhs: "[m, p] \<turnstile> exp[x & (const (IntVal 32 1))] \<mapsto> rhs"
    using eval(2) by blast
  then have rhsV: "rhs = val[xv & IntVal 32 1]"
    by (metis BinaryExprE ConstantExprE bin_eval.simps(4) evalDet xv)
  have "lhs = rhs" using val_optimise_integer_test x32
    using lhsV rhsV by presburger
  then show ?thesis
    by (metis eval(2) evalDet lhs rhs)
qed
  done

(* todo not sure if this is done properly *)
optimization opt_optimise_integer_test_2: 
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
