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


lemma wf_value_intval_add:
  assumes "intval_add x y \<noteq> UndefVal"
  assumes "wf_value x" 
  assumes "wf_value y"
  shows "wf_value (intval_add x y)"
proof -
  obtain b xv where xv: "x = IntVal b xv"
    by (smt (z3) assms(1) intval_add.elims)
  then obtain yv where yv: "y = IntVal b yv"
    using assms(1) apply (cases y; auto)
    by argo
  from xv yv have "intval_add x y = IntVal b (take_bit b (xv+yv))" (is "_ = IntVal b ?val")
    using assms
    using intval_add.simps(1) by presburger
  then have "constantAsStamp (intval_add x y) = (IntegerStamp b (int_signed_value b ?val) (int_signed_value b ?val))" (is "_ = ?stamp")
    using constantAsStamp.simps(1) by presburger
  then have "valid_stamp ?stamp"
    by (metis assms(3) constantAsStamp.simps(1) validStampIntConst valid_stamp.simps(1) valid_value.simps(1) wf_value_def yv)
  then show ?thesis 
    using valid_value.simps(1)
    by (simp add: \<open>intval_add x y = IntVal b (take_bit b (xv + yv))\<close> wf_value_def)
qed

optimization AddFold:
  "((const x) + (const y)) \<longmapsto> (const (x + y))"
  apply auto
  using wf_value_intval_add by blast

thm AddFold_code

lemma binadd_commute:
  assumes "bin_eval BinAdd x y \<noteq> UndefVal"
  shows "bin_eval BinAdd x y = bin_eval BinAdd y x"
  by (simp add: intval_add_sym)

optimization AddShiftConstantRight:
  when "cond[x instanceof ConstantNode]"
  when "cond[!(y instanceof ConstantNode)]"
  "(x + y) \<longmapsto> (y + x)"
  subgoal premises assms
  proof -
    from assms have "evalCondition (InstanceOf (Expr x) STR ''ConstantNode'')" using combine_cond_lhs combine_cond_rhs
      by blast
    then have "is_ConstantExpr x"
      using instance_of_const by presburger
    show ?thesis
      using assms by (smt (verit) IRExpr.collapse(6) combine_cond_lhs combine_cond_rhs instance_of_const instance_of_not_const size_flip_binary)
  qed
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

fun build_choice :: "VarName \<Rightarrow> (VarName \<times> Rules) list \<Rightarrow> Rules" where
  "build_choice v rl = choice (fold (\<lambda>r rl. (snd r \<Zhide> [fst r \<mapsto> v] # rl)) rl [])"

print_phases
gencode "AddPhase" "choice [
  (snd AddLeftNegateToSub_code),
  (snd AddRightNegateToSub_code),
  (snd RedundantAddSub_code),
  (snd RedundantSubAdd2_code),
  (snd RedundantSubAdd_code),
  (snd AddNeutral_code),
  (snd AddShiftConstantRight_code),
  (snd AddFold_code)
]"

gencode "AddPhaseR" "build_choice STR ''e'' [
  (AddLeftNegateToSub_code),
  (AddRightNegateToSub_code),
  (RedundantAddSub_code),
  (RedundantSubAdd2_code),
  (RedundantSubAdd_code),
  (AddNeutral_code),
  (AddShiftConstantRight_code),
  (AddFold_code)
]"

(* Isabelle Isar Questions:
 Why doesn't subgoal handle \forall and \<longrightarrow> ?
 Then this pattern might become just a single subgoal?
  subgoal premises p1
    apply ((rule allI)+; rule impI)
    subgoal premises p2 for m p v
*)
end