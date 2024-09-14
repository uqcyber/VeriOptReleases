theory MetaOptimization
  imports CodeGenAltAlt
begin


section \<open>Meta-optimizations\<close>

locale metaopt =
  fixes opt :: "Rules \<Rightarrow> Rules option"
  fixes size :: "Rules \<Rightarrow> nat"
  assumes sound: "valid_rules r \<and> opt r = Some r' \<Longrightarrow> eval_rules r \<sigma> = eval_rules r' \<sigma>"
  assumes terminates: "opt r = Some r' \<Longrightarrow> size r' < size r"
  assumes size_else: "size r1 < size (either r1 r2) \<and> size r2 < size (either r1 r2)"
  assumes size_choice: "\<forall>r \<in> set rules. size r < size (choice rules)"
  assumes size_cond: "size r < size (cond m r)"
  assumes size_base: "size (base l e) = size (base l e)"
  assumes size_seq: "size r1 < size (seq r1 r2) \<and> size r2 < size (seq r1 r2)"
begin

definition maybe_opt :: "Rules \<Rightarrow> Rules option" where
  "maybe_opt r = (if valid_rules r then opt r else None)"

function apply_meta :: "Rules \<Rightarrow> Rules" where
  "apply_meta m = (case maybe_opt m of Some m' \<Rightarrow> apply_meta m' | None \<Rightarrow> 
    (case m of
      (either r1 r2) \<Rightarrow> (either (apply_meta r1) (apply_meta r2)) |
      (choice rules) \<Rightarrow> choice (map (apply_meta) rules) |
      (cond m r) \<Rightarrow> cond m (apply_meta r) |
      (base l e) \<Rightarrow> (base l e) |
      (seq r1 r2) \<Rightarrow> (seq (apply_meta r1) r2) \<comment> \<open>Avoid recursing through rhs as it could change the entry var\<close>
  ))"
  apply pat_completeness+
  by simp+

(*function apply_meta :: "Rules \<Rightarrow> Rules" and traverse :: "Rules \<Rightarrow> Rules" where
  "traverse m = (case m of
      (r1 else r2) \<Rightarrow> ((apply_meta r1) else (apply_meta r2)) |
      (choice rules) \<Rightarrow> choice (map (apply_meta) rules) |
      (m ? r) \<Rightarrow> m ? (apply_meta r) |
      (base e) \<Rightarrow> (base e) |
      (r1 \<Zsemi> r2) \<Rightarrow> (apply_meta r1 \<Zsemi> apply_meta r2)
  )" |
  "apply_meta m = (case opt m of Some m' \<Rightarrow> apply_meta m' | None \<Rightarrow> 
    traverse m)"
  apply pat_completeness+
  by simp+

definition termination_measure :: "((Rules + Rules) \<times> (Rules + Rules)) set" where
  "termination_measure = {r'. \<exists>r. r' = (Inl r) \<and> r \<in> measure size}"*)

termination apply_meta apply standard
  apply (relation "measure size")
  apply simp
  using size_cond apply force
  using size_else apply force
  using size_else apply force
  using size_seq apply force
  (*using size_seq apply force*)
  using size_choice apply force
  unfolding maybe_opt_def
  by (meson in_measure option.distinct(1) terminates)

theorem apply_meta_sound:
  "eval_rules r \<sigma> = eval_rules (apply_meta r) \<sigma>"
proof (induction r arbitrary: \<sigma> rule: apply_meta.induct)
  case (1 m)
  then show ?case proof (cases "maybe_opt m")
    case None
    then show ?thesis proof (cases m)
      case (base e)
      then show ?thesis
        using None by auto
    next
      case (cond x21 r)
      have ih: "eval_rules r \<sigma> = eval_rules (apply_meta r) \<sigma>"
        using None 1
        using cond by blast
      have app: "apply_meta m = cond x21 (apply_meta r)"
        using None cond by fastforce
      have "\<forall>e. eval_rules (cond x21 r) \<sigma> e = eval_rules (cond x21 (apply_meta r)) \<sigma> e"
        using ih condE
        by (smt (verit) "1.IH"(1) None cond eval_rules.simps)
      then show ?thesis 
        using app cond
        by auto
    next
      case (either r1 r2)
      have ih1: "eval_rules r1 \<sigma> = eval_rules (apply_meta r1) \<sigma>"
        using None 1
        using either by blast
      have ih2: "eval_rules r2 \<sigma> = eval_rules (apply_meta r2) \<sigma>"
        using None 1
        using either by blast
      have app: "apply_meta m = either (apply_meta r1) (apply_meta r2)"
        using None either by fastforce
      have "\<forall>e. eval_rules (either r1 r2) \<sigma> e = eval_rules (either (apply_meta r1) (apply_meta r2)) \<sigma> e"
        using ih1 ih2 elseE
        by (metis eval_rules.intros(3) eval_rules.intros(4))
      then show ?thesis
        using app either by auto
    next
      case (seq r1 r2)
      have ih1: "eval_rules r1 \<sigma> = eval_rules (apply_meta r1) \<sigma>"
        using None 1
        using seq by blast
      have app: "apply_meta m = seq (apply_meta r1) r2"
        using None seq by fastforce
      have "\<forall>e. eval_rules (seq r1 r2) \<sigma> e = eval_rules (seq (apply_meta r1) r2) \<sigma> e"
        apply (rule allI; rule iffI)
        using ih1 seqE eval_rules.intros(8) eval_rules.intros(9) eval_rules.intros(10) 
        apply (smt (verit) "1.IH"(4) None Rules.distinct(11) Rules.distinct(15) Rules.distinct(19) Rules.distinct(5) Rules.inject(4) eval_rules.cases list.simps(8) seq)
        by (smt (verit) "1.IH"(4) None eval_rules.intros(10) eval_rules.intros(8) eval_rules.intros(9) seq seqE)
      then show ?thesis
        using app seq by auto
    next
      case (choice rules)
      have ih: "\<forall>r \<in> set rules. eval_rules r \<sigma> = eval_rules (apply_meta r) \<sigma>"
        using None 1
        using choice by blast
      have app: "apply_meta m = (choice (map apply_meta rules))"
        using None choice by fastforce
      have allE: "\<forall>a \<in> set rules. \<forall>e. eval_rules a \<sigma> e = eval_rules (apply_meta a) \<sigma> e"
        using "1.IH"(5) None choice by simp
      have "\<forall>e. eval_rules (choice rules) \<sigma> e = eval_rules (choice (map apply_meta rules)) \<sigma> e"
        using inductive_choice  ih by blast
      then show ?thesis
        using app choice by auto
    qed
  next
    case (Some a)
    then show ?thesis using 1
      by (metis (no_types, lifting) apply_meta.elims domI domIff maybe_opt_def metaopt.sound metaopt_axioms option.simps(5))
  qed
qed

definition run :: "Rules \<Rightarrow> Rules" where
  "run r = apply_meta r"

end


context includes match_syntax match_pattern_syntax
begin
subsection \<open>Lift Match Sequence to Rule Conditions\<close>

fun lift_cond :: "Rules \<Rightarrow> Rules option" where
  "lift_cond ((m1 && m2) ? r) = (Some (m1 ? (m2 ? r)))" |
  "lift_cond _ = None"

lemma lift_cond_sound:
  "eval_rules ((m1 && m2) ? r) \<sigma> = eval_rules (m1 ? (m2 ? r)) \<sigma>"
proof -
  have "\<forall>e. eval_rules (m1 ? (m2 ? r)) \<sigma> e = eval_rules ((m1 && m2) ? r) \<sigma> e"
    using condE apply auto[1] 
    apply (metis AndThen eval_rules.intros(2))
    by (metis eval_match_andthen eval_rules.intros(2))
  then show ?thesis 
    by blast
qed

fun combined_size :: "Rules \<Rightarrow> nat" where
  "combined_size (m ? r) = 1 + (2 * size m) + combined_size r" |
  "combined_size (base l e) = 0" |
  "combined_size (r1 else r2) = 1 + combined_size r1 + combined_size r2" |
  "combined_size (choice (rule # rules)) = 1 + combined_size rule + combined_size (choice rules)" |
  "combined_size (choice []) = 1" |
  "combined_size (r1 \<Zsemi> r2) = 1 + combined_size r1 + combined_size r2"

lemma combined_size_decreases:
  "combined_size (m1 ? (m2 ? r)) < combined_size ((m1 && m2) ? r)"
proof -
  have lhs: "combined_size (m1 ? (m2 ? r)) = 1 + 1 + (2 * size m1) + (2 * size m2) + combined_size r"
    by simp
  have rhs: "combined_size ((m1 && m2) ? r) = 1 + (2 * size (m1 && m2)) + combined_size r"
    using combined_size.simps(1) by blast
  show ?thesis using lhs rhs
    by simp
qed
end

setup \<open>Locale_Code.open_block\<close>
interpretation lift_cond : metaopt
  lift_cond
  combined_size
  apply standard
  using lift_cond_sound apply auto sorry (*
  subgoal for rules apply (induction rules; auto)
  using lift_cond.elims sledgehammer
  apply (metis lift_cond.elims option.distinct(1) option.inject)*)
(*
  subgoal for rules apply (induction rules; auto)
  using lift_cond.elims option.distinct(1) option.sel sledgehammer
  by (smt (verit))
    by (smt (verit) lift_cond.elims option.distinct(1) option.sel)
  apply (smt (verit) lift_cond.elims option.distinct(1) option.sel)
        apply (smt (verit) lift_cond.elims option.distinct(1) option.sel)
  using combined_size_decreases lift_cond.elims apply force
      apply simp
  subgoal for rules apply (induction rules; auto) done
  by simp+*)
setup \<open>Locale_Code.close_block\<close>

fun run where "run x = lift_cond.apply_meta x"

thm lift_cond.apply_meta_sound
thm_oracles lift_cond.apply_meta_sound

value "(snd (Predicate.the (generateC STR ''myrule''
    (BinaryExprPattern BinSub (BinaryExprPattern BinAdd (VariableExprPattern STR ''x'') (VariableExprPattern STR ''y'')) (VariableExprPattern STR ''x''))
    None
    (VariableExprPattern STR ''x''))))"

value "run (snd (Predicate.the (generateC STR ''myrule''
    (BinaryExprPattern BinSub (BinaryExprPattern BinAdd (VariableExprPattern STR ''x'') (VariableExprPattern STR ''y'')) (VariableExprPattern STR ''x''))
    None
    (VariableExprPattern STR ''x''))))"



subsection \<open>Eliminate Noop Operations\<close>

(*
fun elim_noop :: "Rules \<Rightarrow> Rules option" where
  "elim_noop ((noop x) ? r) = Some (r)" |
  "elim_noop _ = None"

lemma elim_noop_sound:
  "eval_rules (noop x ? r) \<sigma> = eval_rules (r) \<sigma>"
proof -
  have "\<forall>e. eval_rules (noop x ? r) \<sigma> e = eval_rules (r) \<sigma> e"
    using condE apply auto[1] 
     apply (smt (verit, ccfv_threshold) eval_match_andthen eval_match_noop eval_rules.intros(2))
     (* doesn't hold due to our little noop = assert situation *)
  then show ?thesis 
    by blast
qed

lemma elim_noop_decreases:
  "combined_size (x ? r) < combined_size ((x && y) ? r)"
  unfolding combined_size.simps by simp

setup \<open>Locale_Code.open_block\<close>
interpretation elim_noop : metaopt
  elim_noop
  combined_size
  apply standard
  using elim_noop_sound
  apply (smt (verit, best) elim_noop.elims option.distinct(1) option.sel)
  using combined_size_decreases elim_noop.elims apply force
      apply simp
  subgoal for rules apply (induction rules; auto) done
  by simp+
setup \<open>Locale_Code.close_block\<close>
*)

context includes match_syntax match_pattern_syntax
begin
subsection \<open>Join Equal Conditions\<close>

fun join_conditions :: "Rules \<Rightarrow> Rules option" where
  "join_conditions (m1 ? r1 else m2 ? r2) = 
    (if m1 = m2
      then Some (m1 ? (r1 else r2)) else None)" |
  "join_conditions (m1 ? (m2 ? r1)) = 
    (if m1 = m2
      then Some ((m1 ? r1)) else None)" |
  "join_conditions _ = None"

lemma join_cond:
  assumes "valid_match m"
  shows "eval_rules (m ? (m ? r)) \<sigma> e = eval_rules (m ? r) \<sigma> e" (is "?lhs = ?rhs")
  using assms
  by (smt (verit) condE eval_match_deterministic eval_match_idempotent eval_rules.intros(2))

lemma join_else:
  assumes "valid_match m"
  shows "eval_rules (m ? r1 else m ? r2) \<sigma> e = eval_rules (m ? (r1 else r2)) \<sigma> e" (is "?lhs = ?rhs")
  using assms
  by (smt (z3) condE elseE eval_match_deterministic eval_rules.intros(2) eval_rules.intros(3) eval_rules.intros(4))

lemma join_conditions_sound:
  assumes "valid_rules r"
  assumes "join_conditions r = Some r'"
  shows "eval_rules r \<sigma> = eval_rules r' \<sigma>"
  using assms proof (cases r)
  case (base x1)
  then show ?thesis using assms(2) by simp
next
  case (cond x21 x22)
  obtain m r'' where rdef: "r = m ? (m ? r'')"
    using assms(2)
    by (smt (z3) Rules.distinct(9) cond join_conditions.elims option.distinct(1))
  then have "r' = m ? r''"
    using assms(2) by force
  also have "valid_match m"
    using assms(1) rdef by auto
  ultimately show ?thesis using rdef join_cond
    by blast
next
  case (either x31 x32)
  obtain m r1 r2 where rdef: "r = (m ? r1 else m ? r2)"
    using assms(2)
    by (smt (z3) Rules.distinct(9) either join_conditions.elims option.distinct(1))
  then have "r' = m ? (r1 else r2)"
    using assms(2) by force
  also have "valid_match m"
    using assms(1) rdef by auto
  ultimately show ?thesis using rdef join_else
    by blast
next
  case (seq x41 x42)
  then show ?thesis using assms(2) by simp
next
  case (choice x5)
  then show ?thesis using assms(2) by simp
qed
end

setup \<open>Locale_Code.open_block\<close>
interpretation join_conditions : metaopt
  join_conditions
  size
  apply standard
  using join_conditions_sound apply blast
  apply (smt (z3) Rules.size(7) Rules.size(8) add.right_neutral add_Suc_right join_conditions.elims less_add_Suc1 option.distinct(1) option.sel plus_nat.simps(2))
  apply simp+
  subgoal for rules apply (induction rules; auto) done
  by simp+
setup \<open>Locale_Code.close_block\<close>

subsection \<open>Combined Meta-optimizations\<close>

(*fun reduce where "reduce x = (join_conditions.apply_meta o elim_noop.apply_meta o lift_cond.apply_meta) x"*)
definition reduce where "reduce = (join_conditions.apply_meta o lift_cond.apply_meta)"


theorem reduce_sound:
  "eval_rules r \<sigma> = eval_rules (reduce r) \<sigma>"
  by (metis comp_eq_dest_lhs join_conditions.apply_meta_sound lift_cond.apply_meta_sound reduce_def)

value "reduce (snd (Predicate.the (generateC STR ''myrule''
    (BinaryExprPattern BinSub (BinaryExprPattern BinAdd (VariableExprPattern STR ''x'') (VariableExprPattern STR ''y'')) (VariableExprPattern STR ''x''))
    None
    (VariableExprPattern STR ''x''))))"

end