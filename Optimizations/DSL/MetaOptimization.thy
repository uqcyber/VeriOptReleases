theory MetaOptimization
  imports CodeGenAltAlt
begin

context includes match_syntax match_pattern_syntax begin
lemma eval_match_equivalence:
  assumes "\<forall>e. (m \<U> \<sigma> = e) = (m' \<U> \<sigma> = e)"
  shows "eval_match m \<sigma> = eval_match m' \<sigma>"
  using assms
  by blast

lemma eval_match_redundant:
  assumes "valid_match m"
  shows "eval_match (m && m) u = eval_match m u"
  using assms AndThen eval_match_andthen eval_match_deterministic eval_match_idempotent eval_match_equivalence
  by (smt (verit, del_insts))

lemma eval_rules_choice_map_induct:
  assumes "eval_rules (a) u e = eval_rules (f a) u e"
  assumes "eval_rules (choice rules) u e = eval_rules (choice (map f rules)) u e"
  shows "eval_rules (choice (a # rules)) u e = eval_rules (choice (map f (a # rules))) u e"
  using assms choiceE eval_rules.intros(5,6,7)
  by (smt (verit, ccfv_threshold) list.map_disc_iff list.set_intros(1) list.set_intros(2) list.simps(9) option.distinct(1) set_ConsD)

lemma monotonic_cond:
  assumes "\<forall>e u. eval_rules r u e = eval_rules (f r) u e"
  shows "\<forall>e u. eval_rules (m ? r) u e = eval_rules (m ? f r) u e"
  using assms by (metis condE eval_rules.intros(2))

lemma monotonic_else:
  assumes "\<forall>e u. eval_rules r1 u e = eval_rules (f r1) u e"
  assumes "\<forall>e u. eval_rules r2 u e = eval_rules (f r2) u e"
  shows "\<forall>e. eval_rules (r1 else r2) u e = eval_rules (f r1 else f r2) u e"
  using assms
  by (metis elseE eval_rules.intros(3) eval_rules.intros(4))

lemma monotonic_seq_with_entry:
  assumes "\<forall>e u. eval_rules r1 u e = eval_rules (f r1) u e"
  assumes "\<forall>e u. eval_rules r2 u e = eval_rules (f r2) u e"
  assumes "entry_var r2 = entry_var (f r2)"
  shows "\<forall>e. eval_rules (r1 \<Zsemi> r2) u e = eval_rules (f r1 \<Zsemi> f r2) u e"
  using assms seqE
  by (smt (verit, ccfv_SIG) eval_rules.intros(10) eval_rules.intros(8) eval_rules.intros(9))

lemma monotonic_seq_without_entry:
  assumes "\<forall>e u. eval_rules r1 u e = eval_rules (f r1) u e"
  shows "\<forall>e. eval_rules (r1 \<Zsemi> r2) u e = eval_rules ((f r1) \<Zsemi> r2) u e"
  using assms seqE
  by (smt (verit, ccfv_SIG) eval_rules.intros(10) eval_rules.intros(8) eval_rules.intros(9))

lemma monotonic_choice:
  assumes "\<forall>r e u. r \<in> set rules \<longrightarrow> eval_rules r u e = eval_rules (f r) u e"
  shows "\<forall>e. eval_rules (choice rules) u e = eval_rules (choice (map f rules)) u e"
  using assms apply (induction rules) apply simp
  by (metis eval_rules_choice_map_induct list.set_intros(1) list.set_intros(2))
end


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


context includes match_syntax match_pattern_syntax begin
subsection \<open>Lift Match Sequence to Rule Conditions\<close>

fun lift_cond :: "Rules \<Rightarrow> Rules option" where
  "lift_cond ((m1 && m2) ? r) = (Some (m1 ? (m2 ? r)))" |
  "lift_cond _ = None"

lemma lift_condE:
  "lift_cond r = Some r' \<Longrightarrow> \<exists>m1 m2 rule. r = ((m1 && m2) ? rule) \<and> r' = (m1 ? (m2 ? rule))"
  apply (cases r) apply auto 
  subgoal for cond 
    apply (cases cond) by auto
  done
  
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
  apply standard apply auto
  using lift_cond_sound lift_condE apply blast
  using combined_size_decreases lift_condE apply blast
  subgoal for rules r apply (induction rules) 
    apply fastforce
    by force
  done
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



subsection \<open>Join Shared Conditions\<close>

context includes match_syntax match_pattern_syntax begin
(*fun common_size :: "Rules \<Rightarrow> nat" where
  "common_size (m ? r) = 1 + common_size r" |
  "common_size (base l e) = 0" |
  "common_size (r1 else r2) = 1 + common_size r1 + common_size r2" |
  "common_size (choice (rule # rules)) = 1 + common_size rule + common_size (choice rules)" |
  "common_size (choice []) = 0" |
  "common_size (r1 \<Zsemi> r2) = 1 + common_size r1 + common_size r2"
*)

fun find_common :: "MATCH \<Rightarrow> Rules \<Rightarrow> Rules option" where
  "find_common m (m' ? r) = (if m = m' then Some r else None)" |
  "find_common m r = None"

fun find_uncommon :: "MATCH \<Rightarrow> Rules \<Rightarrow> Rules option" where
  "find_uncommon m (m' ? r) = (if m = m' then None else Some (m' ? r))" |
  "find_uncommon m r = Some r"

definition join_common :: "MATCH \<Rightarrow> Rules list \<Rightarrow> Rules list" where
  "join_common m rules = List.map_filter (find_common m) rules"

definition join_uncommon :: "MATCH \<Rightarrow> Rules list \<Rightarrow> Rules list" where
  "join_uncommon m rules = List.map_filter (find_uncommon m) rules"

lemma find_common_defn:
  assumes "find_common m x = v"
  shows "v \<noteq> None \<longleftrightarrow> (\<exists>r. x = (m ? r) \<and> v = Some r)"
  using assms apply (induction m x rule: find_common.induct) unfolding find_common.simps apply force
  by simp+

lemma find_uncommon_preserve:
  "find_uncommon m r = Some r \<or> find_uncommon m r = None"
  by (metis find_uncommon.elims)

lemma join_uncommon_subset:
  "set (join_uncommon m x) \<subseteq> set x"
  unfolding join_uncommon_def List.map_filter_def using find_uncommon_preserve
  by (smt (verit, best) comp_def filter_is_subset list.map_ident_strong mem_Collect_eq option.sel set_filter)

fun combine_conditions :: "Rules \<Rightarrow> Rules option" where
  "combine_conditions (choice ((m ? r) # rules)) = 
    Some 
      (choice ((m ? (choice (r # join_common m rules)))
        # [(choice (join_uncommon m rules))]))" |
  "combine_conditions _ = None"

lemma join_common_empty: "join_common m [] = []"
  by (simp add: join_common_def map_filter_simps(2))
lemma join_uncommon_empty: "join_uncommon m [] = []"
  by (simp add: join_uncommon_def map_filter_simps(2))

lemma eval_choice: "{e. eval_rules (choice rules) u e \<and> e \<noteq> None} = {e | e r . r \<in> set rules \<and> eval_rules r u e \<and> e \<noteq> None}"
  using choiceE eval_rules.intros(5) by fastforce

lemma eval_choice_none: "eval_rules (choice rules) u None = (\<forall> r \<in> set rules . eval_rules r u None)"
  by (metis choiceE eval_rules.intros(6) length_pos_if_in_set list.size(3) nless_le option.distinct(1))

inductive_cases evalRulesE: "eval_rules r u e"

lemmas monotonic =
  monotonic_cond
  monotonic_else
  monotonic_choice
  monotonic_seq_with_entry
  monotonic_seq_without_entry

lemma unordered_choice:
  assumes "set rules = set rules'"
  shows "\<forall>e. eval_rules (choice rules) u e = eval_rules (choice rules') u e"
  using assms by (metis choiceE eval_choice_none eval_rules.intros(5))

lemma find_inverse_lhs:
  "\<exists>e. find_common m rules = None \<longleftrightarrow> find_uncommon m rules = Some e"
  by (smt (verit, best) find_common.elims find_uncommon.simps(1) find_uncommon.simps(2) find_uncommon.simps(3) find_uncommon.simps(4) find_uncommon.simps(5))

lemma find_inverse_rhs:
  "\<exists>e. find_common m rules = Some e \<longleftrightarrow> find_uncommon m rules = None"
  by (smt (verit, best) find_common.elims find_uncommon.simps(1) find_uncommon.simps(2) find_uncommon.simps(3) find_uncommon.simps(4) find_uncommon.simps(5))

lemma join_common_equal:
  assumes "find_common m a = None"
  shows "(map ((?) m) (join_common m rules')) = (map ((?) m) (join_common m (a # rules')))"
  apply (simp add: join_common_def join_uncommon_def List.map_filter_def)
  by (simp add: assms)

lemma join_common_plus:
  assumes "find_common m a = Some a'"
  shows "(m ? a') # (map ((?) m) (join_common m rules')) = (map ((?) m) (join_common m (a # rules')))"
  using assms unfolding join_common_def join_uncommon_def List.map_filter_def
  by simp

lemma join_combines:
  "(set (map (\<lambda>r. m ? r) (join_common m rules)) \<union> set (join_uncommon m rules)) = set rules"
  apply (induction rules) 
    apply (simp add: join_common_def join_uncommon_def List.map_filter_def)
  subgoal premises induct for a rules'
  proof (cases "find_common m a")
    case None
    have "find_uncommon m a = Some a" 
      using None find_inverse_lhs
      by (metis find_uncommon_preserve option.distinct(1))
    then have "join_uncommon m (a # rules') = a # (join_uncommon m rules')"
      unfolding join_common_def join_uncommon_def List.map_filter_def
      by simp
    then show ?thesis using induct join_common_equal
      by (metis None Un_insert_right list.simps(15))
  next
    case (Some a')
    have "find_uncommon m a = None" 
      by (metis Some find_common_defn find_uncommon.simps(1) option.distinct(1))
    then have "join_uncommon m (a # rules') = (join_uncommon m rules')"
      unfolding join_common_def join_uncommon_def List.map_filter_def
      by simp
    then show ?thesis
      by (metis Some Un_insert_left find_common.elims induct join_common_plus list.simps(15) option.distinct(1))
  qed
  done

lemma join_common_set_def:
  "set (join_common m rules) = {r. (m ? r) \<in> set rules}"
  unfolding join_common_def List.map_filter_def 
  apply (induction rules)
   apply simp 
  subgoal for a rules 
    apply (cases a) by auto
  done

lemma join_uncommon_set_def:
  "set (join_uncommon m rules) = {r. r \<in> set rules \<and> (\<forall>r'. r \<noteq> (m ? r'))}"
  unfolding join_uncommon_def List.map_filter_def 
  apply (induction rules) apply simp
  subgoal for a rules 
    apply (cases a) by auto
  done

lemma
  assumes "\<exists>r \<in> set rules. r \<in> set rules' \<and> eval_rules r u (Some e)"
  shows "eval_rules (choice rules) u (Some e) = eval_rules (choice rules') u (Some e)"
  using assms
  using eval_rules.intros(5) by blast

lemma map_None:
  "(\<forall>r\<in>set rules. eval_rules (m ? r) u None) = eval_rules (choice (map ((?) m) rules)) u None"
  (is "?lhs = eval_rules ?rhs u None")
proof -
  have setequiv: "set (map ((?) m) rules) = {m ? r | r . r\<in>set rules}"
    by (simp add: Setcompr_eq_image)
  then show ?thesis
    using eval_choice_none by auto
qed

lemma setequiv: "set (map ((?) m) rules) = {m ? r | r . r\<in>set rules}"
  by (simp add: Setcompr_eq_image)

lemma eval_rules_cond_fail:
  assumes "\<not>(\<exists>e. eval_match m u e)"
  shows "\<not>(eval_rules (m ? r) u e)"
  using assms
  by (meson condE)

lemma eval_rules_choice_fail:
  assumes "\<not>(\<exists>e. eval_match m u e)"
  assumes "rules \<noteq> []"
  shows "\<not>(eval_rules (choice (map ((?) m) rules)) u e)" (is "\<not>(eval_rules (choice ?rules) u e)")
proof -
  have "\<forall>r \<in> set ?rules. \<not>(eval_rules (r) u e)"
    by (simp add: assms eval_rules_cond_fail)
  then show ?thesis
    using assms choiceE
    by (smt (verit) condE list.set_intros(1) map_None neq_Nil_conv)
qed

(*
lemma eval_rules_choice_empty:
  assumes "eval_rules (choice []) u e"
  shows "eval_rules (m ? choice []) u e"
proof -
  have "eval_rules (choice []) u None"
    by (simp add: eval_rules.intros(7))
  have "eval_rules (m ? choice []) u None"
    sledgehammer
  then show "eval_rules (m ? choice []) u e"
    sledgehammer

lemma pull_cond_out_rhs:
  assumes "eval_rules (choice (map ((?) m) rules)) u e" (is "eval_rules ?lhs u e")
  shows "eval_rules (m ? choice rules) u e" (is "eval_rules ?rhs u e")
proof (cases rules)
  case Nil
  then show ?thesis using assms sledgehammer
next
  case (Cons a list)
  then show ?thesis sorry
qed
  proof (cases "\<not>(\<exists>e. eval_match m u e)")
    case True \<comment> \<open>If m doesn't match then both the lhs and rhs should evaluate to e = None\<close>
    have lhs: "\<forall>e. eval_rules ?lhs u e \<longrightarrow> e = None"
      using True eval_rules.intros(2) eval_rules.intros(5)
      by (smt (verit, del_insts) choiceE condE ex_map_conv option.distinct(1))
    have rhs: "\<forall>e. eval_rules ?rhs u e \<longrightarrow> e = None"
      by (meson True condE)
    then show ?thesis using assms condE
      using lhs rhs sledgehammer
      using eval_always_result
      using assms by blast
  next
    case match: (Some a) \<comment> \<open>Drop down into evaluation post matching m\<close>
      have allEval: "\<forall>r \<in> set rules. eval_rules r a e = eval_rules (m ? r) u e"
        by (metis match condE eval_rules.intros(2) option.distinct(1) option.sel)
        then show ?thesis
        proof (cases e)
          case evalsNone: None
          have "\<forall>r \<in> set rules. eval_rules r a None"
            using evalsNone allEval assms map_None by blast
          then have "\<forall>r \<in> set rules. eval_rules (m ? r) u None"
            using evalsNone allEval by blast
          then have "eval_rules ?lhs u None"
            by (simp add: map_None)
          then show ?thesis
            using evalsNone
            using \<open>\<forall>r\<in>set rules. eval_rules r a None\<close> eval_choice_none eval_rules.intros(2) match by blast
        next
          case evalsSome: (Some a')
            then have "\<exists>r \<in> set rules. eval_rules (m ? r) u (Some a')"
              using condE assms match
              using choiceE by fastforce
            then have "\<exists>r \<in> set rules. eval_rules (m ? r) u e"
              by (simp add: evalsSome)
            then have "eval_rules ?rhs u e"
              using allEval eval_rules.intros(2) eval_rules.intros(6) evalsSome match by blast
            then show ?thesis
              by simp
          qed
        qed

lemma pull_cond_out_lhs:
  assumes "eval_rules (m ? choice rules) u e" (is "eval_rules ?lhs u e")
  shows "eval_rules (choice (map ((?) m) rules)) u e" (is "eval_rules ?rhs u e")
  proof (cases "eval_match m u")
    case None \<comment> \<open>If m doesn't match then both the lhs and rhs should evaluate to e = None\<close>
    have lhs: "\<forall>e. eval_rules ?lhs u e \<longrightarrow> e = None"
      using None eval_rules.intros(3) eval_rules.intros(7)
      by (smt (verit, del_insts) choiceE condE ex_map_conv option.distinct(1))
    have rhs: "\<forall>e. eval_rules ?rhs u e \<longrightarrow> e = None"
      by (simp add: lhs pull_cond_out_rhs)
    then show ?thesis using lhs rhs
      using eval_always_result
      using assms by blast
  next
    case match: (Some a) \<comment> \<open>Drop down into evaluation post matching m\<close>
      have allEval: "\<forall>r \<in> set rules. eval_rules r a e = eval_rules (m ? r) u e"
        by (metis match condE eval_rules.intros(2) option.distinct(1) option.sel)
        then show ?thesis
        proof (cases e)
          case evalsNone: None
          have "\<forall>r \<in> set rules. eval_rules r a None"
            by (metis assms condE eval_choice_none evalsNone match option.discI option.inject)
          then have "\<forall>r \<in> set rules. eval_rules (m ? r) u None"
            using evalsNone allEval by blast
          then show ?thesis
            using evalsNone map_None by blast
        next
          case evalsSome: (Some a')
            then have "\<exists>r \<in> set rules. eval_rules (m ? r) u (Some a')"
              using condE assms match
              using choiceE
              by (metis allEval option.distinct(1) option.sel)
            then have "\<exists>r \<in> set rules. eval_rules (m ? r) u e"
              by (simp add: evalsSome)
            then have "eval_rules ?rhs u e"
              by (metis eval_rules.intros(6) evalsSome image_eqI image_set)
            then show ?thesis
              by simp
          qed
        qed

lemma pull_cond_out:
  "eval_rules (choice (map ((?) m) rules)) u e = eval_rules (m ? choice rules) u e"
  using pull_cond_out_lhs pull_cond_out_rhs by blast

lemma cases_None:
  assumes "eval_rules (choice ((m ? r) # rules)) u None"
  shows "
  eval_rules (m ? (choice (r # join_common m rules))) u None \<and>
  eval_rules ((choice (join_uncommon m rules))) u None"
  apply (rule conjI)
  using assms
  unfolding join_common_def List.map_filter_def
   apply (induction rules) apply simp using pull_cond_out
    apply fastforce apply auto[1] using pull_cond_out defer defer
    apply (meson assms eval_choice_none join_uncommon_subset list.set_intros(2) subsetD)
  subgoal for a rules y
    apply (cases a)
        apply force
    subgoal premises pre for m' r' 
    proof -
      have "m = m'"
        using pre(3,4)
        by (metis find_common.simps(1) option.distinct(1))
      then show ?thesis using pre apply auto[1]
        by (smt (verit, del_insts) eval_choice_none list.set_intros(1) list.set_intros(2) list.simps(9) pull_cond_out set_ConsD)
    qed
      by simp+
  subgoal for a rules
    apply (cases a)
    by (simp add: eval_choice_none)+
  done

lemma cases_None1:
  assumes "
  eval_rules (m ? (choice (r # join_common m rules))) u None \<and>
  eval_rules ((choice (join_uncommon m rules))) u None"
  shows "eval_rules (choice ((m ? r) # rules)) u None"
proof -
  have head: "eval_rules (m ? r) u None"
    using assms
    by (meson list.set_intros(1) map_None pull_cond_out_lhs)
  have common_None: "\<forall>r' \<in> set (join_common m rules). eval_rules (m ? r') u None"
    by (meson assms list.set_intros(2) map_None pull_cond_out_lhs)
  have uncommon_None: "\<forall>r' \<in> set (join_uncommon m rules). eval_rules r' u None"
    using assms eval_choice_none by blast
  have "\<forall>r' \<in> set rules. eval_rules r' u None"
    using join_combines common_None uncommon_None pull_cond_out
    by (metis (no_types, lifting) UnE assms eval_choice_none list.set_intros(2) list.simps(9))
  then show ?thesis using head
    by (simp add: eval_choice_none)
qed

  
lemma cases_Some:
  assumes "eval_rules (choice rules) u (Some e)"
  shows "
  eval_rules (m ? (choice (join_common m rules))) u (Some e) \<or>
  eval_rules ((choice (join_uncommon m rules))) u (Some e)"
proof -
  obtain r where r: "r \<in> set rules \<and> eval_rules r u (Some e)"
    by (metis assms choiceE option.discI)
  then show ?thesis
  proof (cases r)
    case (base x1)
    have "r \<in> set (join_uncommon m rules)"
      using join_uncommon_set_def base r by blast
    then show ?thesis
      using eval_rules.intros(6) r by presburger
  next
    case (cond m' r')
    then show ?thesis
    proof (cases "m = m'")
      case True
      then have "r' \<in> set (join_common m rules)"
        using cond r join_common_set_def
        by blast
      then show ?thesis
        by (metis True cond eval_rules.intros(6) image_eqI image_set pull_cond_out_rhs r)
    next
      case False
      have "r \<in> set (join_uncommon m rules)"
        using join_uncommon_set_def False r
        using cond by blast
      then show ?thesis
        using eval_rules.intros(6) r by presburger
    qed
  next
    case (else x31 x32)
    have "r \<in> set (join_uncommon m rules)"
      using join_uncommon_set_def else r by blast
    then show ?thesis
      using eval_rules.intros(6) r by presburger
  next
    case (seq x41 x42)
    have "r \<in> set (join_uncommon m rules)"
      using join_uncommon_set_def seq r by blast
    then show ?thesis
      using eval_rules.intros(6) r by presburger
  next
    case (choice x5)
    have "r \<in> set (join_uncommon m rules)"
      using join_uncommon_set_def choice r by blast
    then show ?thesis
      using eval_rules.intros(6) r by presburger
  qed
qed

lemma cases_Some1:
  assumes "eval_rules (choice ((m ? r) # rules)) u (Some e)"
  shows "
  eval_rules (m ? (choice (r # join_common m rules))) u (Some e) \<or>
  eval_rules ((choice (join_uncommon m rules))) u (Some e)"
  using cases_Some assms
  by (smt (verit, ccfv_threshold) choiceE eval_rules.intros(6) list.set_intros(1) list.set_intros(2) list.simps(9) option.distinct(1) pull_cond_out set_ConsD)

lemma cases_Some2:
  assumes "eval_rules (m ? (choice (r # join_common m rules))) u (Some e) \<or>
  eval_rules ((choice (join_uncommon m rules))) u (Some e)" (is "?c1 \<or> ?c2")
  shows "eval_rules (choice ((m ? r) # rules)) u (Some e)"
using assms proof (rule disjE)
  assume c1: "?c1"
  then show ?thesis
  proof (cases "eval_rules (m ? r) u (Some e)")
    case True
    then show ?thesis
      by (meson eval_rules.intros(6) list.set_intros(1))
  next
    case False
    then have "\<exists>r \<in>set (join_common m rules). eval_rules (m ? r) u (Some e)"
      using c1
      by (smt (verit, del_insts) choiceE condE eval_rules.intros(2) option.distinct(1) set_ConsD)
    then show ?thesis 
      by (metis eval_rules.intros(6) join_common_set_def list.set_intros(2) mem_Collect_eq)
  qed
next
  assume "?c2"
  then have "\<exists>r \<in>set (join_uncommon m rules). eval_rules r u (Some e)"
    by (metis choiceE option.discI)
  then show ?thesis
    by (meson eval_rules.intros(6) join_uncommon_subset list.set_intros(2) subsetD)
qed

lemma evalchoice_twoelement:
  assumes "eval_rules (choice [x1, x2]) u (Some e)"
  shows "eval_rules x1 u (Some e) \<or> eval_rules x2 u (Some e)"
  using assms choiceE by fastforce
*)

lemma combine_conditions_valid:
  "combine_conditions r = Some r' \<Longrightarrow> eval_rules r u e = eval_rules r' u e"
  apply (induction r arbitrary: u e r' rule: combine_conditions.induct) defer apply simp+
  subgoal premises p for m r rules u e
  proof (rule iffI)
    assume eval: "eval_rules (choice ((m ? r) # rules)) u e"
    show "eval_rules
     (choice
       [m ? (choice (r # join_common m rules)),
        (choice (join_uncommon m rules))])
     u e"
    proof (cases e)
      case None
      have "eval_rules (m ? (choice (r # join_common m rules))) u None \<and>
  eval_rules ((choice (join_uncommon m rules))) u None"
        sorry
        using None cases_None eval by blast
      then have "eval_rules (m ? combine_conditions (choice (r # join_common m rules))) u None \<and>
  eval_rules (combine_conditions (choice (join_uncommon m rules))) u None" 
        using p monotonic_cond by blast
      then show ?thesis using None eval_choice_none by simp
    next
      case (Some a)
      have "eval_rules (m ? (choice (r # join_common m rules))) u (Some a) \<or>
  eval_rules ((choice (join_uncommon m rules))) u (Some a)"
        using Some cases_Some1 eval by simp
      then have "eval_rules (m ? combine_conditions (choice (r # join_common m rules))) u (Some a) \<or>
  eval_rules (combine_conditions (choice (join_uncommon m rules))) u (Some a)"
        using p monotonic_cond by blast
      then show ?thesis
        by (metis Some eval_rules.intros(6) list.set_intros(1) list.set_intros(2))
    qed
  next
    assume eval: "eval_rules
     (choice
       [m ? combine_conditions (choice (r # join_common m rules)),
        combine_conditions (choice (join_uncommon m rules))])
     u e"
    show "eval_rules (choice ((m ? r) # rules)) u e"
    proof (cases e)
      case None
      then have "eval_rules (m ? (choice (r # join_common m rules))) u None \<and>
  eval_rules ((choice (join_uncommon m rules))) u None"
        by (smt (verit) eval eval_choice_none list.set_intros(1) list.set_intros(2) monotonic_cond p(1) p(2))
      then show ?thesis using cases_None1 None by blast
    next
      case (Some a)
      then have "eval_rules (m ? combine_conditions (choice (r # join_common m rules))) u (Some a) \<or>
  eval_rules (combine_conditions (choice (join_uncommon m rules))) u (Some a)"
        using eval evalchoice_twoelement by simp
      then have "eval_rules (m ? (choice (r # join_common m rules))) u (Some a) \<or>
  eval_rules ((choice (join_uncommon m rules))) u (Some a)"
        using p monotonic_cond by blast
      then show ?thesis using cases_Some2 Some
        by simp
    qed
  qed
  done


fun eliminate_choice :: "Rules \<Rightarrow> Rules" where
  "eliminate_choice (base e) = base e" |
  "eliminate_choice (r1 else r2) = (eliminate_choice r1 else eliminate_choice r2)" |
  "eliminate_choice (m ? r) = (m ? eliminate_choice r)" |
  "eliminate_choice (choice (r # [])) = eliminate_choice r" |
  "eliminate_choice (choice rules) = 
    choice (map eliminate_choice rules)" |
  "eliminate_choice (r1 \<Zsemi> r2) = (eliminate_choice r1 \<Zsemi> eliminate_choice r2)"

lemma choice_Single:
  "eval_rules (choice [r]) u e = eval_rules r u e"
  apply (cases e)
  using eval_choice_none apply auto[1]
  using choiceE eval_rules.intros(6) by fastforce

lemma entry_var_single_choice:
  "entry_var r = entry_var (choice [r])"
  unfolding entry_var.simps by simp

lemma entry_var_eliminate_choice:
  "entry_var r = entry_var (eliminate_choice r)"
  apply (induction r rule: eliminate_choice.induct)
  apply simp 
  using eliminate_choice.simps(2) entry_var.simps(3) apply presburger
  using eliminate_choice.simps(3) entry_var.simps(1) apply presburger
  unfolding eliminate_choice.simps
  using entry_var_single_choice apply presburger
  apply simp 
  using entry_var_rules apply blast
  using entry_var.simps(5) by presburger


lemma eliminate_choice_valid_1:
  "{e. eval_rules r u e} = {e. eval_rules (eliminate_choice r) u e}"
  apply (induction r arbitrary: u rule: eliminate_choice.induct)
  apply simp unfolding eliminate_choice.simps
  apply (smt (verit) Collect_cong elseE eval_rules.intros(4) eval_rules.intros(5) mem_Collect_eq)
  unfolding eliminate_choice.simps
      apply (smt (verit) Collect_cong condE eval_rules.intros(3) eval_rules.simps mem_Collect_eq)
  unfolding eliminate_choice.simps
  using choice_Single apply presburger
  using monotonic_choice apply blast
  apply (metis Collect_cong mem_Collect_eq monotonic_choice)
  using entry_var_eliminate_choice
  by (smt (verit, ccfv_SIG) Collect_cong mem_Collect_eq monotonic_seq_with_entry)

lemma eliminate_choice_valid:
  "eval_rules r u e = eval_rules (eliminate_choice r) u e"
  using eliminate_choice_valid_1 by blast

definition optimized_export where
  "optimized_export = eliminate_choice \<circ> combine_conditions o lift_common o lift_match o eliminate_noop"

lemma elim_noop_preserve_def_vars:
  "def_vars m = def_vars (elim_noop m)"
  apply (induction m rule: elim_noop.induct) by simp+

lemma elim_noop_preserve_use_vars:
  "use_vars m = use_vars (elim_noop m)"
  apply (induction m rule: elim_noop.induct) apply simp+
  using elim_noop_preserve_def_vars by simp+

lemma elim_noop_preserve_valid:
  assumes "valid_match m"
  shows "valid_match (elim_noop m)"
    using assms apply (induction m rule: elim_noop.induct) apply simp+
    using elim_noop_preserve_def_vars elim_noop_preserve_use_vars by simp+

lemma eliminate_noop_preserve_valid:
  assumes "valid_rules r"
  shows "valid_rules (eliminate_noop r)"
  using assms apply (induction r rule: eliminate_noop.induct) apply simp
  apply (simp add: elim_noop_preserve_valid) by simp+


lemma lift_match_preserve_valid:
  assumes "valid_rules r"
  shows "valid_rules (lift_match r)"
  using assms apply (induction r rule: lift_match.induct) apply simp
  by simp+

lemma optimized_export_valid:
  assumes "valid_rules r"
  shows "eval_rules r u e = eval_rules (optimized_export r) u e"
  unfolding optimized_export_def comp_def
  using lift_common_valid lift_match_valid eliminate_noop_valid 
  using combine_conditions_valid eliminate_choice_valid
  by (metis assms eliminate_noop_preserve_valid lift_match_preserve_valid)

thm_oracles optimized_export_valid

end