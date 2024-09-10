subsection \<open>AddNode Phase\<close>

theory AddPhase
  imports
    Common
begin

phase AddNode 
  terminating size
begin

no_notation andthen (infixr "&&" 50)

no_syntax
  "_seq" :: "Statement \<Rightarrow> Statement => Statement" (infixr ";//" 55)

lemma binadd_commute:
  assumes "bin_eval BinAdd x y \<noteq> UndefVal"
  shows "bin_eval BinAdd x y = bin_eval BinAdd y x"
  by (simp add: intval_add_sym)

inductive_cases cond_Unary: "base_semantics (Unary op e) v"
inductive_cases cond_Binary: "base_semantics (Binary op x y) v"
inductive_cases cond_Conditional: "base_semantics (ConditionDSL.Conditional c t f) v"
inductive_cases cond_Const: "base_semantics (Constant x) y"
inductive_cases cond_Value: "base_semantics (Value x) y"
inductive_cases cond_ExprL: "base_semantics (Expr x) y"
inductive_cases cond_ExprR: "base_semantics x (Expr y)"
inductive_cases cond_Stamp: "base_semantics (Stamp x) y"
inductive_cases cond_Combine: "base_semantics (Combine x y) v"
inductive_cases cond_InstanceOf: "base_semantics (InstanceOf e c) y"
inductive_cases coerce_True: "coerce_to_bool c True"

lemma logic_negation_bool:
  assumes "is_IntVal val"
  assumes "val_to_bool (unary_eval UnaryLogicNegation val)"
  shows "\<not>(val_to_bool val)"
  using assms unfolding unary_eval.simps intval_logic_negation.simps apply (cases val; auto)
  by (metis logic_negate_def take_bit_of_0)

lemma coerce_to_bool_det:
  assumes "coerce_to_bool x c"
  assumes "coerce_to_bool x c'"
  shows "c = c'"
  using assms apply (induction x c arbitrary: c' rule: coerce_to_bool.induct)
  using coerce_to_bool.simps by blast+

lemma base_semantics_det:
  assumes "base_semantics x c"
  assumes "base_semantics x c'"
  shows "c = c'"
  using assms apply (induction x c arbitrary: c' rule: base_semantics.induct) 
  apply (metis Condition.inject(5) cond_Unary)
  apply (metis Condition.inject(5) cond_Binary)
  apply (metis coerce_to_bool_det cond_Conditional)
  using cond_Const apply blast
  using cond_Value apply blast 
  using cond_ExprL apply blast 
  using cond_Stamp apply blast 
  apply (metis cond_Combine)
     apply (smt (verit, ccfv_threshold) Condition.distinct(91) Condition.inject(7) cond_InstanceOf)
  apply (smt (verit, ccfv_threshold) Condition.distinct(91) Condition.inject(7) cond_InstanceOf)
  by (smt (verit, best) Condition.inject(8) Condition.simps(103) cond_InstanceOf)+

lemma instance_of_const:
  assumes "\<exists>c'. base_semantics (InstanceOf (Expr x) STR ''ConstantNode'') c' \<and> coerce_to_bool c' True"
  shows "is_ConstantExpr x"
proof -
  obtain c' where c': "base_semantics (InstanceOf (Expr x) STR ''ConstantNode'') c' \<and> coerce_to_bool c' True"
    using assms by blast
  then have "c' = (Value (IntVal 32 1))"
    using assms coerce_True
    by (smt (verit) Condition.distinct(55) Condition.distinct(75) Condition.inject(5) cond_InstanceOf val_to_bool.simps(1))
  then have "class_name x = Some STR ''ConstantNode''"
    using assms c'
    by (smt (verit) Condition.distinct(77) Condition.distinct(91) Condition.inject(10) Condition.inject(5) Condition.inject(7) Condition.simps(117) Condition.simps(29) Condition.simps(47) Condition.simps(63) Condition.simps(77) Value.inject(1) base_semantics.cases cond_ExprL zero_neq_one)
  then show ?thesis
    apply (cases x; auto)
    subgoal for op e by (cases op; auto)
    subgoal for op x y by (cases op; auto)
    done
qed

lemma instance_of_not_const:
  assumes "\<exists>c'. base_semantics (Unary UnaryLogicNegation (InstanceOf (Expr x) STR ''ConstantNode'')) c' \<and> coerce_to_bool c' True"
  shows "\<not>(is_ConstantExpr x)"
proof -
  obtain val where "base_semantics (InstanceOf (Expr x) STR ''ConstantNode'') (Value val)"
    using assms
    by (meson cond_Unary)
  obtain c' where c': "base_semantics (Unary UnaryLogicNegation (InstanceOf (Expr x) STR ''ConstantNode'')) c' \<and> coerce_to_bool c' True"
    using assms by blast
  then have "c' = Value (unary_eval UnaryLogicNegation val)"
    by (smt (verit) Condition.distinct(91) Condition.inject(5) Condition.inject(7) \<open>base_semantics (InstanceOf (Expr x) STR ''ConstantNode'') (Value val)\<close> assms cond_ExprL cond_InstanceOf cond_Unary)
  then have "val_to_bool (unary_eval UnaryLogicNegation val)"
    using assms coerce_True c'
    by (metis Condition.distinct(55) Condition.distinct(75) Condition.inject(5))
  then have "\<not>(val_to_bool val)"
    using logic_negation_bool
    by (metis Value.disc(2) val_to_bool.elims(2))
  then have "class_name x \<noteq> Some STR ''ConstantNode''"
    using assms
    by (smt (z3) Condition.distinct(77) Condition.distinct(91) Condition.inject(10) Condition.inject(5) Condition.inject(7) Condition.simps(117) Condition.simps(29) Condition.simps(47) Condition.simps(63) Condition.simps(77) \<open>base_semantics (InstanceOf (Expr x) STR ''ConstantNode'') (Value val)\<close> base_semantics.cases cond_ExprL val_to_bool.simps(1) zero_neq_one)
  then show ?thesis
    by (cases x; auto)
qed

lemma combine_cond_lhs:
  assumes "\<exists>c'. base_semantics (x; y) c' \<and> coerce_to_bool c' True"
  shows "\<exists>x'. base_semantics x x' \<and> coerce_to_bool x' True"
  using assms using cond_Combine
  by (metis Condition.distinct(63) Condition.inject(9) Condition.simps(87) coerce_True)

lemma combine_cond_rhs:
  assumes "\<exists>c'. base_semantics (x; y) c' \<and> coerce_to_bool c' True"
  shows "\<exists>y'. base_semantics y y' \<and> coerce_to_bool y' True"
  using assms using cond_Combine
  by (metis Condition.distinct(63) Condition.inject(9) Condition.simps(87) coerce_True)

optimization AddShiftConstantRight:
  when "cond[(Expr x) instanceof ConstantNode]"
  when "cond[!((Expr y) instanceof ConstantNode)]"
  "(x + y) \<longmapsto> (y + x)"
   apply (smt (verit) IRExpr.collapse(6) combine_cond_lhs combine_cond_rhs instance_of_const instance_of_not_const size_flip_binary)
  using le_expr_def binadd_commute by blast

value AddShiftConstantRight_code

(* TODO: define is_neutral and then lemmas like this: 
lemma simp_neutral:
  assumes n: "is_neutral op (IntVal32 n)" 
  shows "bin_eval op x (IntVal32 n) = x"
  apply (induction op)
  unfolding is_neutral.simps 
  using n apply auto
*)

(* poor-mans is_neutral lemma *)
lemma is_neutral_0 [simp]:
  assumes "val[(IntVal b x) + (IntVal b 0)] \<noteq> UndefVal"
  shows "val[(IntVal b x) + (IntVal b 0)] = (new_int b x)"
  by simp


lemma AddNeutral_Exp:
  shows "exp[(e + (const (IntVal 32 0)))] \<ge> exp[e]"
  apply auto[1]
  subgoal premises p for m p x
  proof -
    obtain ev where ev: "[m,p] \<turnstile> e \<mapsto> ev"
      using p by auto
    then obtain b evx where evx: "ev = IntVal b evx"
      by (metis evalDet evaltree_not_undef intval_add.simps(3,4,5) intval_logic_negation.cases
          p(1,2))
    then have additionNotUndef: "val[ev + (IntVal 32 0)] \<noteq> UndefVal"
      using p evalDet ev by blast
    then have sameWidth: "b = 32"
      by (metis evx additionNotUndef intval_add.simps(1))
    then have unfolded: "val[ev + (IntVal 32 0)] = IntVal 32 (take_bit 32 (evx+0))"
      by (simp add: evx)
    then have eqE: "IntVal 32 (take_bit 32 (evx+0)) = IntVal 32 (take_bit 32 (evx))"
      by auto
    then show ?thesis
      by (metis ev evalDet eval_unused_bits_zero evx p(1) sameWidth unfolded)
  qed
  done

optimization AddNeutral: "(e + (const (IntVal 32 0))) \<longmapsto> e"
  using AddNeutral_Exp by presburger

(*
lemma
  "pattern_refinement 
  (VariableExpr STR ''e'' default_stamp)
  (BinaryExpr BinAdd (VariableExpr STR ''e'' default_stamp) (ConstantExpr (IntVal 32 0)))"
  using AddNeutral(1) unfolding pattern_refinement_def apply simp
  by (smt (verit, del_insts) groundof_BinaryExpr groundof_ConstantExpr groundof_det)
*)

ML_val \<open>@{term \<open>x = y\<close>}\<close>

lemma NeutralLeftSubVal:
  assumes "e1 = new_int b ival"
  shows "val[(e1 - e2) + e2] \<approx> e1"
  using assms by (cases e1; cases e2; auto)

lemma RedundantSubAdd_Exp:
  shows "exp[((a - b) + b)] \<ge> a"
  apply auto[1]
  subgoal premises p for m p y xa ya
  proof -
    obtain bv where bv: "[m,p] \<turnstile> b \<mapsto> bv"
      using p(1) by auto
    obtain av where av: "[m,p] \<turnstile> a \<mapsto> av"
      using p(3) by auto
    then have subNotUndef: "val[av - bv] \<noteq> UndefVal"
      by (metis bv evalDet p(3,4,5))
    then obtain bb bvv where bInt: "bv = IntVal bb bvv"
      by (metis bv evaltree_not_undef intval_logic_negation.cases intval_sub.simps(7,8,9))
    then obtain ba avv where aInt: "av = IntVal ba avv"
      by (metis av evaltree_not_undef intval_logic_negation.cases intval_sub.simps(3,4,5) subNotUndef)
    then have widthSame: "bb=ba"
      by (metis av bInt bv evalDet intval_sub.simps(1) new_int_bin.simps p(3,4,5))
    then have valEval: "val[((av-bv)+bv)] = val[av]"
      using aInt av eval_unused_bits_zero widthSame bInt by simp
    then show ?thesis
      by (metis av bv evalDet p(1,3,4))
  qed
  done
  
optimization RedundantSubAdd: "((e1 - e2) + e2) \<longmapsto> e1"
  using RedundantSubAdd_Exp by blast

(* a little helper lemma for using universal quantified assumptions *)
lemma allE2: "(\<forall>x y. P x y) \<Longrightarrow> (P a b \<Longrightarrow> R) \<Longrightarrow> R"
  by simp

lemma just_goal2: 
  assumes "(\<forall> a b. (val[(a - b) + b] \<noteq> UndefVal \<and> a \<noteq> UndefVal \<longrightarrow>
                    val[(a - b) + b] = a))"
  shows "(exp[(e\<^sub>1 - e\<^sub>2) + e\<^sub>2]) \<ge> e\<^sub>1"
  unfolding le_expr_def unfold_binary bin_eval.simps by (metis assms evalDet evaltree_not_undef)

optimization RedundantSubAdd2: " e2 + (e1 - e2) \<longmapsto> e1"
  using size_binary_rhs_a apply simp apply auto[1]
  by (smt (z3) NeutralLeftSubVal evalDet eval_unused_bits_zero intval_add_sym intval_sub.elims new_int.simps well_formed_equal_defn)


(* Demonstration of our FOUR levels of expression rewrites:
   =======================================================
  level 1 (Java-like): "-e + y \<longmapsto> y - e"
  level 2 (expr trees): "rewrite_preservation
     (BinaryExpr BinAdd (UnaryExpr UnaryNeg e) y \<longmapsto> BinaryExpr BinSub y e) &&&
    rewrite_termination
     (BinaryExpr BinAdd (UnaryExpr UnaryNeg e) y \<longmapsto> BinaryExpr BinSub y e)
     Common.size"
  level 2b: "BinaryExpr BinAdd (UnaryExpr UnaryNeg e) y \<le> BinaryExpr BinSub y e"
  level 2c: "\<forall>m p v. ([m,p] \<turnstile> BinaryExpr BinAdd (UnaryExpr UnaryNeg e) y \<mapsto> v)
                   \<longrightarrow> ([m,p] \<turnstile> BinaryExpr BinSub y e \<mapsto> v)"
  level 3 (intval ops): "\<And>m p xa ya.
       [m,p] \<turnstile> e \<mapsto> xa \<Longrightarrow>
       [m,p] \<turnstile> y \<mapsto> ya \<Longrightarrow>
       intval_negate xa \<noteq> UndefVal \<Longrightarrow>
       intval_add (intval_negate xa) ya \<noteq> UndefVal \<Longrightarrow>
       \<exists>x. ([m,p] \<turnstile> y \<mapsto> x) \<and>
           (\<exists>y. ([m,p] \<turnstile> e \<mapsto> y) \<and>
                intval_add (intval_negate xa) ya =
                intval_sub x y)"
  level 3b: "\<forall>m p v.
       (\<exists>x ya.
           (\<exists>xa. ([m,p] \<turnstile> e \<mapsto> xa) \<and>
                 x = intval_negate xa \<and> x \<noteq> UndefVal) \<and>
                 ([m,p] \<turnstile> y \<mapsto> ya) \<and>
                 v = intval_add x ya \<and> v \<noteq> UndefVal) \<longrightarrow>
       (\<exists>x ya.
           ([m,p] \<turnstile> y \<mapsto> x) \<and>
           ([m,p] \<turnstile> e \<mapsto> ya) \<and>
            v = intval_sub x ya \<and> v \<noteq> UndefVal)"
  level 4 (Word library): "-ev + yv = yv - ev" (twice, for 32-bit and 64-bit)
*)


(* The LowLevel version, intval_*, of this helper lemma is much easier
   to prove than the bin_eval level.  And equally easy to use in AddToSub.
 *)
lemma AddToSubHelperLowLevel:
  shows "val[-e + y] = val[y - e]" (is "?x = ?y")
  by (induction y; induction e; auto)

print_phases

(* -----  Starts here -----  *)

(* 
 AddNode has 8 optimisations total
 Currently *6* optimisations are verified.

 -- Already verified above --

 - AddShiftRightConst
 - RedundantSubAdd
 - AddNeutral (32-bit only)

 -- Verified below --
 
 - RedundantAddSub
 - AddRightNegateToSub
 - AddLeftNegateToSub 

 -- Left to go --
 - MergeSignExtendAdd
 - MergeZeroExtendAdd

*)

(* Value level proofs *)
lemma val_redundant_add_sub:
  assumes "a = new_int bb ival"
  assumes "val[b + a] \<noteq> UndefVal"
  shows "val[(b + a) - b] = a"
  using assms apply (cases a; cases b; auto) by presburger

lemma val_add_right_negate_to_sub:
  assumes "val[x + e] \<noteq> UndefVal"
  shows "val[x + (-e)] = val[x - e]"
  by (cases x; cases e; auto simp: assms)

(* Exp level proofs *)
lemma exp_add_left_negate_to_sub:
  "exp[-e + y] \<ge> exp[y - e]"
  by (cases e; cases y; auto simp: AddToSubHelperLowLevel)

lemma RedundantAddSub_Exp:
  shows "exp[(b + a) - b] \<ge> a"
  apply auto[1]
    subgoal premises p for m p y xa ya
  proof -
    obtain bv where bv: "[m,p] \<turnstile> b \<mapsto> bv"
      using p(1) by auto
    obtain av where av: "[m,p] \<turnstile> a \<mapsto> av"
      using p(4) by auto
    then have addNotUndef: "val[av + bv] \<noteq> UndefVal"
      by (metis bv evalDet intval_add_sym intval_sub.simps(2) p(2,3,4))
    then obtain bb bvv where bInt: "bv = IntVal bb bvv"
      by (metis bv evalDet evaltree_not_undef intval_add.simps(3,5) intval_logic_negation.cases
          intval_sub.simps(8) p(1,2,3,5))
    then obtain ba avv where aInt: "av = IntVal ba avv"
      by (metis addNotUndef intval_add.simps(2,3,4,5) intval_logic_negation.cases)
    then have widthSame: "bb=ba"
      by (metis addNotUndef bInt intval_add.simps(1))
    then have valEval: "val[((bv+av)-bv)] = val[av]"
      using aInt av eval_unused_bits_zero widthSame bInt by simp
    then show ?thesis
      by (metis av bv evalDet p(1,3,4))
  qed
  done

text \<open>Optimisations\<close>

optimization RedundantAddSub: "(b + a) - b \<longmapsto> a"
  using RedundantAddSub_Exp by blast

optimization AddRightNegateToSub: "x + -e \<longmapsto> x - e"
  apply (metis Nat.add_0_right add_2_eq_Suc' add_less_mono1 add_mono_thms_linordered_field(2) 
         less_SucI not_less_less_Suc_eq size_binary_const size_non_add size_pos)
  using AddToSubHelperLowLevel intval_add_sym by auto

optimization AddLeftNegateToSub: "-e + y \<longmapsto> y - e"
  apply (smt (verit, best) One_nat_def add.commute add_Suc_right is_ConstantExpr_def less_add_Suc2 
         numeral_2_eq_2 plus_1_eq_Suc size.simps(1) size.simps(11) size_binary_const size_non_add)
  using exp_add_left_negate_to_sub by simp

(* ----- Ends here ----- *)

end

(* Isabelle Isar Questions:
 Why doesn't subgoal handle \forall and \<longrightarrow> ?
 Then this pattern might become just a single subgoal?
  subgoal premises p1
    apply ((rule allI)+; rule impI)
    subgoal premises p2 for m p v
*)
end