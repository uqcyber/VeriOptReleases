section \<open>Match Patterns\<close>

theory CompileRewrite
  imports
    Stratego
    VeriComp.Compiler
begin

(*lift_definition fmupds :: "('x \<Rightarrow> 'z option) \<Rightarrow> 'x list \<Rightarrow> 'z list \<Rightarrow> ('x \<Rightarrow> 'z option)"
  is map_upds .*)
setup_lifting type_definition_fmap

parametric_constant map_upds_transfer[transfer_rule]: map_upds_def

lift_definition fmupds :: "('a, 'b) fmap \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> ('a, 'b) fmap"
  is map_upds
  parametric map_upds_transfer
  by simp

subsection \<open>Variable Scope\<close>

type_synonym VarName = "string"
type_synonym Vars = "VarName fset"

type_synonym Scope = "Vars \<times> (VarName \<rightharpoonup> VarName)"

fun remove_var :: "VarName \<Rightarrow> Scope \<Rightarrow> Scope" where
  "remove_var v (vs, m) = (vs - {|v|}, m)"
fun add_var :: "VarName \<Rightarrow> Scope \<Rightarrow> Scope" where
  "add_var v (vs, m) = (vs |\<union>| {|v|}, m)"

function fresh_var :: "VarName \<Rightarrow> Scope \<Rightarrow> VarName" where
  "fresh_var v s = 
    (if v |\<in>| (fst s) 
      then fresh_var (v @ ''z'') (remove_var v s)
      else v)"
  by fastforce+

termination fresh_var
  apply (relation "measure (\<lambda>(v, s). (fcard (fst s)))")
  apply simp
  using fcard_fminus1_less by force

fun fresh :: "VarName \<Rightarrow> Scope \<Rightarrow> Scope \<times> VarName" where
  "fresh v s = (let v = fresh_var v s in (add_var v s, v))"


subsection \<open>Match Primitive\<close>

print_locale Rewritable



locale CompiledRewrites = Rewritable +
  fixes subexprs :: "'a \<Rightarrow> 'a list"
  fixes chain :: "('a \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a)) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a)"
  assumes shrinks: "\<forall>e' \<in> set (subexprs e). size e > size e'"
  assumes "map f (subexprs e) = subexprs (snd (chain (\<lambda>e a. (plus a 1, f e)) e 0))"
  assumes "length (subexprs e) = fst (chain (\<lambda>e a. (plus a 1, f e)) e 0)"
begin

fun map_tree :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "map_tree f xs = snd (chain (\<lambda>e a. (plus a 1, f e)) xs (0::nat))"

fun maybe_map_tree :: "('a \<Rightarrow> 'a option) \<Rightarrow> 'a \<Rightarrow> 'a option" where
  "maybe_map_tree f xs = 
    (let (flag, e') = (chain (\<lambda>e a. (if (f e) = None then 1 else 0, the (f e))) xs (0::nat)) in
      (if flag = 1 then None else Some e'))"

fun pattern_variables :: "'a \<Rightarrow> string list" where
  "pattern_variables e = List.map_filter varof (subexprs e)"


datatype ('e, 'cond) MATCH =
  match VarName "'e" |
  equality VarName VarName (infixl "==" 52) |
  andthen "('e, 'cond) MATCH" "('e, 'cond) MATCH" (infixl "&&" 50) |
  cond "'cond" | \<comment> \<open>This was 'a => bool as the second argument but it disagrees with code generation. Requires work regardless.\<close>
  noop

fun register_name where
  "register_name (s, m) vn v = (s, m(vn\<mapsto>v))"

fun nth_fresh :: "VarName \<Rightarrow> Scope \<Rightarrow> nat \<Rightarrow> (Scope \<times> VarName)" where
  "nth_fresh v s 0 = fresh v s" |
  "nth_fresh v s (Suc n) = fresh v (fst (nth_fresh v s n))"

fun replace_subexprs :: "Scope \<Rightarrow> ('a) \<Rightarrow> (Scope \<times> ('a))" where
  "replace_subexprs s e =
    (let (n, e') = chain (\<lambda>e n. (plus n 1, var (snd (nth_fresh ''a'' s n)))) e 0
      in (fst (nth_fresh ''a'' s n), e'))"

fun expression_vars :: "Scope \<Rightarrow> ('a) \<Rightarrow> (Scope \<times> string list)" where
  "expression_vars s e = 
    (chain_list s (\<lambda>e' s'. (fresh ''a'' s')) (subexprs e))"

fun replace_subexpr :: "string list \<Rightarrow> ('a) \<Rightarrow> ('a)" where
  "replace_subexpr vs e = snd (chain (\<lambda>e n. (plus n 1, var (vs!n))) e 0)"

fun join :: "(('e, 'cond) MATCH) list \<Rightarrow> ('e, 'cond) MATCH" where
  "join [] = noop" |
  "join [x] = x" |
  "join (x # xs) = (x && join xs)"

type_synonym ('e, 'cond) MatchGenerator = "'e \<Rightarrow> VarName \<Rightarrow> Scope \<Rightarrow> Scope \<times> ('e, 'cond) MATCH"

abbreviation generate_subexprs :: "('a, 'b) MatchGenerator \<Rightarrow> 'a list \<Rightarrow> Scope \<Rightarrow> string list \<Rightarrow> ((Scope \<times> nat) \<times> ('a, 'b) MATCH list)" where
  "generate_subexprs f es s vs \<equiv> 
     (chain_list (s, 0) (\<lambda>e' (s', n). 
        (let (scope, m) = (f e' (vs!n) s') in
          ((scope, plus n 1), m))) es)"

function match_pattern :: "('a, 'b) MatchGenerator" where
  "match_pattern e v s =
    (case varof e of
      Some vn \<Rightarrow> (case (snd s) vn of 
        None \<Rightarrow> (register_name s vn v, noop) |
        Some v' \<Rightarrow> (register_name s vn v, equality v' v)) |
      None \<Rightarrow>
        (let (s', vs) = expression_vars s e in
        (let ((s'', _), e'') = (generate_subexprs match_pattern (subexprs e) s' vs) in
                        (s'', (match v (replace_subexpr vs e) && join e'')))))"
  by fastforce+

termination match_pattern
  apply (relation "measure (\<lambda>(e, v, s). size e)")
   apply simp+ apply auto[1]
  using shrinks sorry

definition gen_pattern :: "('a) \<Rightarrow> VarName \<Rightarrow> ('a, 'b) MATCH" where
  "gen_pattern p v = snd (match_pattern p v ({|v|}, Map.empty))"

subsubsection \<open>Semantics\<close>

fun equal_ignore_vars :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "equal_ignore_vars e1 e2 = ((map_tree (\<lambda>_. var ''a'') e1) = (map_tree (\<lambda>_. var ''a'') e2))"

type_synonym 'e Subst = "string \<rightharpoonup> 'e"

fun unify :: "string list \<Rightarrow> 'a list \<Rightarrow> 'a Subst \<Rightarrow> 'a Subst option" where
  "unify [] [] s = Some s" |
  "unify (v # vs) (e # es) s = 
    (if s v = Some e then unify vs es s
     else (if v \<in> dom s \<and> s v \<noteq> Some e then None
           else unify vs es (s(v \<mapsto> e))))" |
  "unify _ _ s = None"

function ground_expr :: "'a \<Rightarrow> 'a Binding \<Rightarrow> 'a option" where
  "ground_expr e s =
    (case varof e of
      Some v \<Rightarrow>(case fmlookup s v of None \<Rightarrow> None
                | Some v' \<Rightarrow> Some v') |
      None \<Rightarrow> maybe_map_tree (\<lambda>e'. ground_expr e' s) e)"
  apply auto[1]
  by fastforce

\<comment> \<open>Requires a proof that all the arguments to the map tree anonymous function are less than the original input\<close>
termination  sorry

lemma ground_expr_idempotent:
  assumes "a' \<subseteq>\<^sub>f a"
  assumes "ground_expr e a' = Some e'"
  shows "ground_expr e a' = ground_expr e a"
  using assms apply (induction e a' arbitrary: a a' rule: ground_expr.induct)
  apply lifting sorry


fun eval_match :: "('a, 'b) MATCH \<Rightarrow> 'a Subst \<Rightarrow> ('a Subst) option" where
  "eval_match (match v e) s =
    (case s v of
      Some e' \<Rightarrow>
        (if equal_ignore_vars e e' then
          (unify (pattern_variables e) (subexprs e') s) else None) |
      None \<Rightarrow> None)" |
  "eval_match (equality v1 v2) s =
    (if v1 \<in> dom s \<and> v2 \<in> dom s \<and> s v1 = s v2 then Some s else None)" |
  "eval_match (andthen m1 m2) s =
      (case eval_match m1 s of 
        None \<Rightarrow> None |
        Some s' \<Rightarrow> eval_match m2 s')" |
  "eval_match noop s = Some s" |
  "eval_match (cond e) s =
      (case eval_condition (ground_condition e s) of
        None \<Rightarrow> None |
        Some e' \<Rightarrow> (if e' then Some s else None))"

subsubsection \<open>Validity\<close>

fun def_vars :: "('a, 'b) MATCH \<Rightarrow> string set" where
  "def_vars (match v p) = set (pattern_variables p)" |
  "def_vars (equality e1 e2) = {e1, e2}" |
  "def_vars (m1 && m2) = def_vars m1 \<union> def_vars m2" |
  "def_vars (cond c) = {}" |
  "def_vars noop = {}"

fun use_vars :: "('a, 'b) MATCH \<Rightarrow> string set" where
  "use_vars (match v p) = {v}" |
  "use_vars (equality e1 e2) = {}" |
  "use_vars (m1 && m2) = use_vars m1 \<union> (use_vars m2 - def_vars m1)" |
  "use_vars (cond c) = {}" |
  "use_vars noop = {}"

fun valid_match :: "('a, 'b) MATCH \<Rightarrow> bool" where
  "valid_match (match v e) = (v \<notin> set (pattern_variables e) \<and> distinct (pattern_variables e))" |
  "valid_match (m1 && m2) = (valid_match m1 \<and> valid_match m2 \<and> use_vars m1 \<inter> def_vars m2 = {})" |
  "valid_match _ = True"

subsubsection \<open>Lemmata\<close>

lemma noop_semantics_rhs:
  "eval_match (lhs && noop) s = eval_match lhs s"
  by (simp add: option.case_eq_if)

lemma noop_semantics_lhs:
  "eval_match (noop && rhs) s = eval_match rhs s"
  by simp

lemma seq_det_lhs:
  assumes "\<forall>s. eval_match lhs1 s = eval_match lhs2 s"
  shows "eval_match (lhs1 && rhs) s = eval_match (lhs2 && rhs) s"
  using assms by simp

lemma seq_det_rhs:
  assumes "\<forall>s. eval_match rhs1 s = eval_match rhs2 s"
  shows "eval_match (lhs && rhs1) s = eval_match (lhs && rhs2) s"
proof (cases "eval_match lhs s")
  case None
  then show ?thesis by simp
next
  case (Some a)
  then obtain s' where s': "eval_match lhs s = Some s'"
    by simp
  then have lhs: "eval_match (lhs && rhs1) s = eval_match rhs1 s'"
    by simp
  from s' have rhs: "eval_match (lhs && rhs2) s = eval_match rhs2 s'"
    by simp
  from lhs rhs show ?thesis using assms
    by simp
qed

lemma unify_effect:
  assumes "unify vs es s = Some a"
  shows "a = s(vs [\<mapsto>] es)"
  using assms proof (induction vs es s rule: unify.induct)
  case (1 s)
  then show ?case by simp
next
  case (2 v vs e es s)
  then show ?case proof (cases "s v = Some e")
    case True
    then show ?thesis
      by (metis "2.IH"(1) "2.prems" map_upd_triv map_upds_Cons unify.simps(2))
  next
    case False
    then show ?thesis
      by (metis "2.IH"(2) "2.prems" map_upds_Cons option.distinct(1) unify.simps(2))
  qed
next
  case ("3_1" v va s)
  then show ?case by simp
next
  case ("3_2" v va s)
  then show ?case by simp
qed


lemma match_def_affect:
  assumes "eval_match m u = Some a"
  shows "\<forall>v. v \<notin> def_vars m \<longrightarrow> u v = a v"
using assms proof (induction m u arbitrary: a rule: eval_match.induct)
  case (1 v e s)
  then show ?case unfolding def_vars.simps pattern_variables.simps eval_match.simps
    by (smt (verit, best) map_upds_apply_nontin option.case_eq_if option.distinct(1) unify_effect)
next
  case (2 v1 v2 s)
  then show ?case
    by (metis eval_match.simps(2) option.discI option.inject)
next
  case (3 m1 m2 s)
  then show ?case using UnCI def_vars.simps(3) eval_match.simps(3) option.case_eq_if option.collapse
    by (smt (verit, ccfv_threshold))
next
  case (4 s)
  then show ?case
    by simp
next
  case (5 sc s)
  then show ?case
    by (smt (verit, del_insts) eval_match.simps(5) option.case_eq_if option.distinct(1) option.sel)
qed

lemma use_def:
  assumes "valid_match m"
  shows "def_vars m \<inter> use_vars m = {}"
  using assms apply (induction m)
  apply simp+
  apply blast
  by simp+

lemma match_use_affect:
  assumes "eval_match m u = Some a"
  assumes "valid_match m"
  shows "\<forall>v \<in> use_vars m. u v = a v"
  using assms apply (induction m u arbitrary: u a rule: eval_match.induct)
  by (meson disjoint_iff_not_equal match_def_affect use_def)+


lemma unify_subset:
  assumes "unify vs es s = Some a"
  shows "s \<subseteq>\<^sub>m a"
using assms proof (induction vs es s rule: unify.induct)
  case (1 s)
  then show ?case by simp
next
  case (2 v vs e es s)
  then show ?case proof (cases "s v = Some e")
    case True
    then show ?thesis
      by (metis "2.IH"(1) "2.prems" unify.simps(2))
  next
    case False
    then show ?thesis
      by (metis "2.IH"(2) "2.prems" fun_upd_None_if_notin_dom map_le_imp_upd_le map_le_refl map_le_trans option.discI unify.simps(2))
  qed
next
  case ("3_1" v va s)
  then show ?case by simp
next
  case ("3_2" v va s)
  then show ?case by simp
qed

lemma eval_match_subset:
  assumes "eval_match m u = Some a"
  assumes "valid_match m"
  shows "u \<subseteq>\<^sub>m a"
  using assms proof (induction m arbitrary: u a)
  case (match x1 x2)
  then show ?case using match apply simp
    using unify.simps(1) unify_subset
    by (smt (verit, del_insts) option.case_eq_if option.distinct(1))
next
  case (equality x1 x2)
  then show ?case
    by (metis eval_match.simps(2) map_le_refl option.distinct(1) option.sel)
next
  case (andthen m1 m2)
  then show ?case
    using valid_match.simps(2) eval_match.simps(3) map_le_trans option.case_eq_if option.collapse
    sorry
next
  case (cond x)
  then show ?case
    using match_def_affect by fastforce
next
  case noop
  then show ?case by simp
qed

lemma unify_idempotence:
  assumes "unify vs es a' = Some a'"
  assumes "a' \<subseteq>\<^sub>m a"
  shows "unify vs es a = Some a"
  using assms proof (induction vs es a' rule: unify.induct)
  case (1 s)
  then show ?case by simp
next
  case (2 v vs e es s)
  then show ?case proof (cases "s v = Some e")
    case True
    then show ?thesis
      by (metis "2.IH"(1) "2.prems"(1) "2.prems"(2) domI map_le_def unify.simps(2))
  next
    case False
    then show ?thesis
      by (metis "2.prems"(1) domIff fun_upd_idem_iff map_le_antisym map_le_imp_upd_le option.discI unify.simps(2) unify_subset)
  qed
next
  case ("3_1" v va s)
  then show ?case by simp
next
  case ("3_2" v va s)
  then show ?case by simp
qed

lemma lift_idempotence:
  assumes "eval_match m a' = Some a'"
  assumes "a' \<subseteq>\<^sub>m a"
  assumes "valid_match m"
  shows "eval_match m a = Some a"
  using assms proof (induction m arbitrary: a a')
  case (match x1 x2)
  then show ?case unfolding eval_match.simps using unify_idempotence
    by (smt (verit, ccfv_SIG) domIff map_le_def option.case_eq_if option.distinct(1))
next
  case (equality x1 x2)
  from equality show ?case apply simp
    by (metis domIff map_le_def option.distinct(1))
next
  case (andthen m1 m2)
  obtain a'' where m1eval: "eval_match m1 a' = Some a''"
    using andthen.prems(1) by fastforce
  then have m2eval: "eval_match m2 a'' = Some a'"
    using andthen.prems(1) by auto
  then have "a'' \<subseteq>\<^sub>m a'"
    using andthen.prems(3) eval_match_subset valid_match.simps(2) by blast
  then show ?case
    by (metis andthen.IH(1) andthen.IH(2) andthen.prems(2) andthen.prems(3) eval_match.simps(3) eval_match_subset m1eval m2eval map_le_antisym option.simps(5) valid_match.simps(2))
next
  case (cond c)
  then have "(ground_condition c a') = (ground_condition c a)"
    sorry (*
    by (metis (no_types, lifting) Rewritable_axioms Rewritable_def eval_match.simps(5) option.case_eq_if option.collapse option.distinct(1))*)
  then show ?case
    by (smt (verit, ccfv_SIG) cond.prems(1) eval_match.simps(5) option.case_eq_if option.distinct(1) prod.exhaust_sel)
next
  case noop
  then show ?case by simp
qed

lemma idempotent_unify2:
  assumes "unify vs es u = Some a"
  shows "unify vs es a = Some a"
using assms proof (induction vs es u rule: unify.induct)
  case (1 s)
  then show ?case by simp
next
  case (2 v vs e es s)
  then show ?case proof (cases "s v = Some e")
    case True
    then show ?thesis
      by (metis "2.IH"(1) "2.prems" domI map_le_def unify.simps(2) unify_subset)
  next
    case False
    then show ?thesis
      by (metis (no_types, lifting) "2.IH"(2) "2.prems" domI fun_upd_same map_le_def option.distinct(1) unify.simps(2) unify_subset)
  qed
next
  case ("3_1" v va s)
  then show ?case by simp
next
  case ("3_2" v va s)
  then show ?case by simp
qed

lemma idempotent_match:
  assumes "eval_match m u = Some a"
  assumes "valid_match m"
  shows "eval_match m a = Some a"
  using assms 
proof (induction m arbitrary: u a)
  case (match x1 x2)
  then show ?case using idempotent_unify2
    by (smt (verit) def_vars.simps(1) eval_match.simps(1) match_def_affect option.case_eq_if valid_match.simps(1))
next
  case (equality x1 x2)
  then show ?case
    by (metis (no_types, lifting) eval_match.simps(2) eval_match_subset lift_idempotence)
next
  case (andthen m1 m2)
  obtain a' where m1eval: "eval_match m1 u = Some a'"
    using andthen.prems(1) by fastforce
  have m1idem: "eval_match m1 a' = Some a'"
    using andthen.IH(1) andthen.prems(2) m1eval valid_match.simps(2) by blast
  have validm1: "valid_match m1"
    using andthen.prems(2) by auto
  have m2eval: "eval_match m2 a' = Some a"
    using andthen.prems(1) m1eval by auto
  have validm2: "valid_match m2"
    using andthen.prems(2) by auto
  have m2idem: "eval_match m2 a = Some a"
    using m2eval validm2
    using andthen.IH(2) by blast
  have "a' \<subseteq>\<^sub>m a"
    using eval_match_subset m2eval validm2 by blast
  then have "eval_match m1 a = Some a"
    using m1idem lift_idempotence validm1 by blast
  then show ?case
    by (simp add: m2idem)
next
  case (cond x)
  then show ?case
    using match_def_affect
    by fastforce
next
  case noop
  then show ?case
    by simp
qed     

lemma match_eq:
  assumes "valid_match m"
  shows "eval_match (m && m) u = eval_match m u"
  using assms
  by (simp add: idempotent_match option.case_eq_if)

subsection \<open>Combining Rules\<close>

datatype ('e, 'cond) Rules =
  base "'e" |
  cond' "('e, 'cond) MATCH" "('e, 'cond) Rules" (infixl "?" 52) |
  else' "('e, 'cond) Rules" "('e, 'cond) Rules" (infixl "else" 50) |
  seq "('e, 'cond) Rules" "('e, 'cond) Rules" (infixl "\<then>" 49) |
  choice "(('e, 'cond) Rules) list"

function var_expr :: "'a \<Rightarrow> Scope \<Rightarrow> 'a" where
  "var_expr e (s, m) =
    (case varof e of
      Some v \<Rightarrow>(case m v of None \<Rightarrow> var v
                | Some v' \<Rightarrow> var v') |
      None \<Rightarrow> map_tree (\<lambda>e'. var_expr e' (s, m)) e)"
  apply auto[1]
  by fastforce

text \<open>Requires a proof that all the arguments to the map tree anonymous function are less than the original input\<close>
termination var_expr sorry

fun generate :: "'a \<Rightarrow> 'a \<Rightarrow> ('a, 'b) Rules" where
  "generate p r = 
    (let (s, m) = match_pattern p ''e'' ({||}, (\<lambda>x. None))
     in (m ? (base (var_expr r s))))"

fun variable_substitutor :: "(string \<rightharpoonup> string) \<Rightarrow> (string \<rightharpoonup> 'a)" where
  "variable_substitutor f = (\<lambda>v. (case f v of Some v' \<Rightarrow> Some (var v') | None \<Rightarrow> None))"

fun generate_with_condition :: "'a \<Rightarrow> 'a \<Rightarrow> ('b) \<Rightarrow> ('a, 'b) Rules" where
  "generate_with_condition p r c = 
    (let (s, m) = match_pattern p ''e'' ({||}, (\<lambda>x. None))
     in ((m && (cond (ground_condition c (variable_substitutor (snd s))))) ? (base (var_expr r s))))" (* TODO: ground_condition *)


subsubsection \<open>Semantics\<close>

text \<open>Replace any variable expressions with value in a substitution.\<close>
fun evaluated_terms where
  "evaluated_terms f es s = map (\<lambda>e. f e s) es"

fun has_none :: "('a option) list \<Rightarrow> bool" where
  "has_none [] = False" |
  "has_none (x # xs) = ((x = None) \<and> has_none xs)"

function eval_expr :: "'a \<Rightarrow> 'a Subst \<Rightarrow> 'a option" where
  "eval_expr e u =
    (case varof e of
        Some v \<Rightarrow> u v
      | None \<Rightarrow> 
        (if has_none (evaluated_terms eval_expr (subexprs e) u)
          then None
          else Some (map_tree (the o (\<lambda>e'. eval_expr e' u)) e)))"
  by fastforce+

termination eval_expr sorry

inductive eval_rules :: "('a, 'b) Rules \<Rightarrow> 'a Subst \<Rightarrow> 'a option \<Rightarrow> bool" where
  \<comment> \<open>Evaluate the result\<close>
  "eval_rules (base e) u (eval_expr e u)" |

  \<comment> \<open>Evaluate a condition\<close>
  "\<lbrakk>eval_match m u = Some u' \<and>
    eval_rules r u' e\<rbrakk>
   \<Longrightarrow> eval_rules (cond' m r) u e" |
  "\<lbrakk>eval_match m u = None\<rbrakk>
   \<Longrightarrow> eval_rules (cond' m r) u None" |

  \<comment> \<open>Evaluate else\<close>
  "\<lbrakk>eval_rules r1 u (Some r)\<rbrakk>
   \<Longrightarrow> eval_rules (r1 else r2) u (Some r)" |
  "\<lbrakk>eval_rules r1 u None \<and>
    eval_rules r2 u e\<rbrakk>
   \<Longrightarrow> eval_rules (r1 else r2) u e" |

  \<comment> \<open>Evaluate choice\<close>
  "\<lbrakk>rule \<in> set rules \<and>
    eval_rules rule u (Some r)\<rbrakk>
   \<Longrightarrow> eval_rules (choice rules) u (Some r)" |
  "\<lbrakk>\<forall> rule \<in> set rules. eval_rules rule u None\<rbrakk>
   \<Longrightarrow> eval_rules (choice rules) u None" |
  "\<lbrakk>rules = []\<rbrakk>
   \<Longrightarrow> eval_rules (choice rules) u None" |

  \<comment> \<open>Evaluate sequential\<close>
  "\<lbrakk>eval_rules r1 u (Some e') \<and>
    eval_rules r2 (u(''e'' \<mapsto> e')) r\<rbrakk>
   \<Longrightarrow> eval_rules (r1 \<then> r2) u r" |
  "\<lbrakk>eval_rules r1 u None \<and>
    eval_rules r2 u r\<rbrakk>
   \<Longrightarrow> eval_rules (r1 \<then> r2) u r"

inductive_cases baseE: "eval_rules (base e') u e"
inductive_cases condE: "eval_rules (cond' m r) u e"
inductive_cases elseE: "eval_rules (r1 else r2) u e"
inductive_cases choiceE: "eval_rules (choice r) u e"
inductive_cases seqE: "eval_rules (r1 \<then> r2) u e"

(*code_pred [show_modes] eval_rules .*)

subsubsection \<open>Validity\<close>

fun valid_rules :: "('a, 'b) Rules \<Rightarrow> bool" where
  "valid_rules (m ? r) = (valid_match m \<and> valid_rules r)" |
  "valid_rules (r1 else r2) = (valid_rules r1 \<and> valid_rules r2)" |
  "valid_rules (r1 \<then> r2) = (valid_rules r1 \<and> valid_rules r2)" |
  "valid_rules (choice rules) = (\<forall>r \<in> set rules. valid_rules r)" |
  "valid_rules _ = True"

subsubsection \<open>Lemmata\<close>

lemma choice_join:
  assumes "eval_rules (a) u e = eval_rules (f a) u e"
  assumes "eval_rules (choice rules) u e = eval_rules (choice (map f rules)) u e"
  shows "eval_rules (choice (a # rules)) u e = eval_rules (choice (map f (a # rules))) u e"
  using assms
  by (smt (verit, ccfv_threshold) choiceE eval_rules.intros(6) eval_rules.intros(7) list.map_disc_iff list.set_intros(1) list.set_intros(2) list.simps(9) option.distinct(1) set_ConsD)

lemma chain_equiv:
  "eval_rules (m1 ? (m2 ? r)) u e = eval_rules ((m1 && m2) ? r) u e"
  using condE apply auto[1]
   apply (smt (verit, best) condE eval_match.simps(3) eval_rules.intros(2) eval_rules.intros(3) option.simps(4) option.simps(5))
  by (metis (no_types, lifting) condE eval_match.simps(3) eval_rules.intros(2) eval_rules.intros(3) is_none_code(2) is_none_simps(1) option.case_eq_if option.collapse)

lemma eval_choice: "{e. eval_rules (choice rules) u e \<and> e \<noteq> None} = {e | e r . r \<in> set rules \<and> eval_rules r u e \<and> e \<noteq> None}"
  using choiceE eval_rules.intros(6) by fastforce

lemma eval_choice_none: "eval_rules (choice rules) u None = (\<forall> r \<in> set rules . eval_rules r u None)"
  by (metis choiceE eval_rules.intros(7) length_pos_if_in_set list.size(3) nless_le option.distinct(1))

inductive_cases evalRulesE: "eval_rules r u e"

lemma eval_always_result:
  "\<exists> e. eval_rules r u e"
  apply (induction r arbitrary: u)
  using eval_rules.intros(1) apply auto[1]
  using eval_rules.intros(2,3) apply (metis option.exhaust)
  using eval_rules.intros(4,5) apply (metis split_option_ex) 
  using eval_rules.intros(9,10) apply (metis split_option_ex) 
  using eval_rules.intros(6,7) by (metis split_option_ex) 

lemma unordered_choice:
  assumes "set rules = set rules'"
  shows "\<forall>e. eval_rules (choice rules) u e = eval_rules (choice rules') u e"
  using assms by (metis choiceE eval_choice_none eval_rules.intros(6))

lemma monotonic_cond:
  assumes "\<forall>e u. eval_rules r u e = eval_rules (f r) u e"
  shows "\<forall>e u. eval_rules (m ? r) u e = eval_rules (m ? f r) u e"
  using assms by (metis condE eval_rules.intros(2) eval_rules.intros(3))

lemma monotonic_else:
  assumes "\<forall>e u. eval_rules r1 u e = eval_rules (f r1) u e"
  assumes "\<forall>e u. eval_rules r2 u e = eval_rules (f r2) u e"
  shows "\<forall>e. eval_rules (r1 else r2) u e = eval_rules (f r1 else f r2) u e"
  using assms
  by (smt (verit, best) elseE eval_rules.intros(4) eval_rules.intros(5))

lemma monotonic_seq:
  assumes "\<forall>e u. eval_rules r1 u e = eval_rules (f r1) u e"
  assumes "\<forall>e u. eval_rules r2 u e = eval_rules (f r2) u e"
  shows "\<forall>e. eval_rules (r1 \<then> r2) u e = eval_rules (f r1 \<then> f r2) u e"
  using assms
  by (smt (verit) eval_rules.simps seqE)

lemma monotonic_choice:
  assumes "\<forall>r e u. r \<in> set rules \<longrightarrow> eval_rules r u e = eval_rules (f r) u e"
  shows "\<forall>e. eval_rules (choice rules) u e = eval_rules (choice (map f rules)) u e"
  using assms apply (induction rules) apply simp
  by (metis choice_join list.set_intros(1) list.set_intros(2))

lemmas monotonic =
  monotonic_cond
  monotonic_else
  monotonic_choice
  monotonic_seq

lemma map_None:
  "(\<forall>r\<in>set rules. eval_rules (m ? r) u None) = eval_rules (choice (map ((?) m) rules)) u None"
  (is "?lhs = eval_rules ?rhs u None")
proof -
  have setequiv: "set (map ((?) m) rules) = {m ? r | r . r\<in>set rules}"
    by (simp add: Setcompr_eq_image)
  then show ?thesis
    using eval_choice_none
    by fastforce
qed

lemma setequiv: "set (map ((?) m) rules) = {m ? r | r . r\<in>set rules}"
  by (simp add: Setcompr_eq_image)

lemma pull_cond_out_rhs:
  assumes "eval_rules (choice (map ((?) m) rules)) u e" (is "eval_rules ?lhs u e")
  shows "eval_rules (m ? choice rules) u e" (is "eval_rules ?rhs u e")
  proof (cases "eval_match m u")
    case None \<comment> \<open>If m doesn't match then both the lhs and rhs should evaluate to e = None\<close>
    have lhs: "\<forall>e. eval_rules ?lhs u e \<longrightarrow> e = None"
      using None eval_rules.intros(3) eval_rules.intros(7)
      by (smt (verit, del_insts) choiceE condE ex_map_conv option.distinct(1))
    have rhs: "\<forall>e. eval_rules ?rhs u e \<longrightarrow> e = None"
      by (metis None condE option.distinct(1))
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

lemma choice_Single:
  "eval_rules (choice [r]) u e = eval_rules r u e"
  apply (cases e)
  using eval_choice_none apply auto[1]
  using choiceE eval_rules.intros(6) by fastforce


lemma redundant_conditions:
  assumes "valid_match m"
  shows "eval_rules (m ? (m ? r1)) u e = eval_rules (m ? r1) u e" (is "?lhs = ?rhs")
proof -
  have "?lhs = eval_rules ((m && m) ? r1) u e"
    using chain_equiv
    by blast
  moreover have "eval_rules ((m && m) ? r1) u e = ?rhs"
    using match_eq
    by (smt (verit) Rules.distinct(1) Rules.distinct(11) Rules.distinct(13) Rules.distinct(9) Rules.inject(2) assms eval_rules.simps)
  ultimately show ?thesis by simp
qed


subsection \<open>Rule Optimizations\<close>

subsubsection \<open>Eliminate \texttt{noop} Operations\<close>

fun elim_noop :: "('e, 'cond) MATCH \<Rightarrow> ('e, 'cond) MATCH" where
  "elim_noop (lhs && noop) = elim_noop lhs" |
  "elim_noop (noop && rhs) = elim_noop rhs" |
  "elim_noop (lhs && rhs) = ((elim_noop lhs) && (elim_noop rhs))" |
  "elim_noop m = m"

lemma sound_optimize_noop:
  "eval_match m s = eval_match (elim_noop m) s"
  apply (induction m arbitrary: s rule: elim_noop.induct)
  using noop_semantics_rhs apply force+
  using seq_det_rhs
  apply (metis elim_noop.simps(14) elim_noop.simps(22)) apply force
           apply (metis elim_noop.simps(16) seq_det_lhs seq_det_rhs)
  apply (metis elim_noop.simps(17) elim_noop.simps(24) seq_det_rhs)
  by simp+

fun eliminate_noop :: "('e, 'cond) Rules \<Rightarrow> ('e, 'cond) Rules" where
  "eliminate_noop (base e) = base e" |
  "eliminate_noop (noop ? r) = eliminate_noop r" |
  "eliminate_noop (m ? r) = elim_noop m ? eliminate_noop r" |
  "eliminate_noop (r1 else r2) = (eliminate_noop r1 else eliminate_noop r2)" |
  "eliminate_noop (choice rules) = choice (List.map eliminate_noop rules)" |
  "eliminate_noop (r1 \<then> r2) = (eliminate_noop r1 \<then> eliminate_noop r2)"

lemma eliminate_noop_valid:
  "eval_rules r u e = eval_rules (eliminate_noop r) u e"
  apply (induction r arbitrary: u e rule: eliminate_noop.induct)
          apply simp
  apply (metis condE eliminate_noop.simps(2) eval_match.simps(4) eval_rules.intros(2) option.distinct(1) option.inject)
  using sound_optimize_noop apply (simp add: monotonic_cond)
  using sound_optimize_noop apply (simp add: monotonic_cond)
  using eliminate_noop.simps(2) condE sound_optimize_noop
      apply (smt (verit) eliminate_noop.simps(5) eval_rules.simps)
  using sound_optimize_noop apply (simp add: monotonic_cond)
  using sound_optimize_noop apply (simp add: monotonic_else)
  apply (simp add: monotonic_choice)
  by (simp add: monotonic_seq)

(*
fun elim_empty :: "'a MATCH \<Rightarrow> 'a MATCH" where
  "elim_empty (condition Empty) = noop" |
  "elim_empty (m1 && m2) = (elim_empty m1 && elim_empty m2)" |
  "elim_empty m = m"

fun eliminate_empty :: "'a::Rewritable Rules \<Rightarrow> 'a Rules" where
  "eliminate_empty (base e) = base e" |
  "eliminate_empty (m ? r) = elim_empty m ? eliminate_empty r" |
  "eliminate_empty (r1 else r2) = (eliminate_empty r1 else eliminate_empty r2)" |
  "eliminate_empty (choice rules) = choice (List.map eliminate_empty rules)" |
  "eliminate_empty (r1 \<then> r2) = (eliminate_empty r1 \<then> eliminate_empty r2)"*)


subsubsection \<open>Lift primitive sequential (\texttt{\&\&}) to rule sequential (\texttt{?})\<close>

definition size_condition :: "'cond \<Rightarrow> nat" where
  "size_condition _ = 0"

definition size_Rule :: "('a, 'b) Rules \<Rightarrow> nat" where
  "size_Rule = size_Rules size size_condition"

fun combined_size :: "('e, 'cond) Rules \<Rightarrow> nat" where
  "combined_size (m ? r) = (2 * size_MATCH size_condition size_condition m) + combined_size r" |
  "combined_size (base e) = 0" |
  "combined_size (r1 else r2) = combined_size r1 + combined_size r2" |
  "combined_size (choice (rule # rules)) = 1 + combined_size rule + combined_size (choice rules)" |
  "combined_size (choice []) = 1" |
  "combined_size (r1 \<then> r2) = combined_size r1 + combined_size r2"

function (sequential) lift_match :: "('e, 'cond) Rules \<Rightarrow> ('e, 'cond) Rules" where
  "lift_match (r1 else r2) = ((lift_match r1) else (lift_match r2))" |
  "lift_match (choice rules) = choice (map lift_match rules)" |
  "lift_match ((m1 && m2) ? r) = (lift_match (m1 ? (m2 ? r)))" |
  "lift_match (m ? r) = m ? (lift_match r)" |
  "lift_match (base e) = (base e)" |
  "lift_match (r1 \<then> r2) = (lift_match r1 \<then> lift_match r2)"
  by pat_completeness auto
termination lift_match
  apply (relation "measures [combined_size, (size_Rules size_condition size_condition)]") apply auto[1]
  apply auto[1] apply auto[1] apply simp
  subgoal for rules x apply (induction rules) apply simp by fastforce
  apply simp subgoal for m2 r apply (cases m2)
    apply auto[1]
    by simp+
  by fastforce+

lemma lift_match_valid:
  "eval_rules r u e = eval_rules (lift_match r) u e"
  apply (induction r arbitrary: u e rule: lift_match.induct) 
           apply simp 
  using lift_match.simps(1) elseE
  apply (smt (verit, ccfv_threshold) eval_rules.intros(4) eval_rules.intros(5))
  unfolding lift_match.simps(2)
  subgoal premises ind for rules u e 
    using ind apply (induction rules) apply simp
    using choice_join
    by (metis list.set_intros(1) list.set_intros(2))
        apply (simp add: chain_equiv)
       apply (metis condE eval_rules.intros(2) eval_rules.intros(3) lift_match.simps(4))
        apply (metis condE eval_rules.intros(2) eval_rules.intros(3) lift_match.simps(5))
       apply (metis condE eval_rules.intros(2) eval_rules.intros(3) lift_match.simps(6))
      apply (metis condE eval_rules.intros(2) eval_rules.intros(3) lift_match.simps(7))
    apply simp
  by (smt (verit) Rules.distinct(11) Rules.distinct(15) Rules.distinct(19) Rules.distinct(5) Rules.inject(4) eval_rules.simps lift_match.simps(9))


subsubsection \<open>Merge Common Conditions in \texttt{else} and sequential (\texttt{?}) Operations\<close>

fun join_conditions :: "('e, 'cond) Rules \<Rightarrow> ('e, 'cond) Rules option" where
  "join_conditions (m1 ? r1 else m2 ? r2) = 
    (if m1 = m2
      then Some (m1 ? (r1 else r2)) else None)" |
  "join_conditions (m1 ? (m2 ? r1)) = 
    (if m1 = m2
      then Some ((m1 ? r1)) else None)" |
  "join_conditions r = None"

lemma join_conditions_shrinks:
  "join_conditions r = Some r' \<Longrightarrow> (<) (size_Rule r') (size_Rule r)"
  apply (induction r rule: join_conditions.induct)
  using Rules.size(7) Rules.size(8) Suc_le_eq add.left_commute add.right_neutral antisym_conv1 join_conditions.simps(1) le_simps(1) option.distinct(1) option.sel plus_nat.simps(2)
   add_Suc_right le_add2 sorry(*
  apply (smt (z3))
  apply (metis Rules.size(7) add.right_neutral add_Suc_right join_conditions.simps(2) less_add_Suc2 option.distinct(1) option.sel)
  by simp+*)

lemma join_conditions_valid:
  assumes "valid_rules r"
  shows "join_conditions r = Some r' \<Longrightarrow> eval_rules r u e = eval_rules r' u e"
  using assms apply (induction r rule: join_conditions.induct)
  apply (smt (verit, ccfv_threshold) condE elseE eval_rules.intros(2) eval_rules.intros(3) eval_rules.intros(4) eval_rules.intros(5) join_conditions.simps(1) option.distinct(1) option.sel)
  subgoal premises p for m1 m2 r
  proof -
    have v1:"valid_match m1" using p(2) by simp
    moreover have v2:"valid_match m2" using p(2) by simp
    ultimately show ?thesis
      by (metis join_conditions.simps(2) option.discI option.sel p(1) redundant_conditions)
  qed
  by simp+

function lift_common :: "('e, 'cond) Rules \<Rightarrow> ('e, 'cond) Rules" where
  "lift_common (r1 else r2) = (
    case join_conditions (r1 else r2) 
    of Some r \<Rightarrow> lift_common r |
       None \<Rightarrow> (lift_common r1 else lift_common r2))" |
  "lift_common (m ? r) = (
    case join_conditions (m ? r) 
    of Some r' \<Rightarrow> lift_common r' |
       None \<Rightarrow> (m ? lift_common r))" |
  "lift_common (choice rules) = choice (List.map lift_common rules)" |
  "lift_common (base e) = base e" |
  "lift_common (r1 \<then> r2) = (lift_common r1 \<then> lift_common r2)"
  using combined_size.cases 
  apply (smt (verit, ccfv_threshold))
  by simp+
termination sorry (*
  apply (relation "measures [size_Rule]") apply auto[1]
    apply simp subgoal for r1 r2 apply (induction r1 rule: join_conditions.induct) by simp+
   apply auto[1]
  using join_conditions_shrinks apply fastforce+
  by (simp add: le_imp_less_Suc size_list_estimation')+*)

lemma lift_common_valid:
  assumes "valid_rules r"
  shows "eval_rules r u e = eval_rules (lift_common r) u e"
  using assms proof (induction r arbitrary: u e rule: lift_common.induct)
  case (1 r1 r2)
  then show ?case
  proof (cases "join_conditions (r1 else r2)")
    case None
    then have "(lift_common (r1 else r2)) = (lift_common r1 else lift_common r2)"
      by simp
    then show ?thesis using 1
      by (simp add: None monotonic_else)
  next
    case (Some a)
    then obtain m1 m2 r1' r2' where ex: "(r1 else r2) = (m1 ? r1' else m2 ? r2')"
      by (smt (z3) Rules.distinct(9) join_conditions.elims option.distinct(1))
    then have "m1 = m2"
      by (metis Some join_conditions.simps(1) option.distinct(1))
    then show ?thesis using 1
      using ex join_conditions_valid
      by (metis (no_types, lifting) join_conditions.simps(1) lift_common.simps(1) option.case_eq_if option.distinct(1) option.sel valid_rules.simps(1) valid_rules.simps(2))
  qed
next
  case (2 m r)
  then show ?case
  proof (cases "join_conditions (m ? r)")
    case None
    then have "(lift_common (m ? r)) = (m ? lift_common r)"
      by simp
    then show ?thesis using 2
      by (simp add: None monotonic_cond)
  next
    case (Some a)
    then obtain m1 m2 r' where ex: "(m ? r) = (m1 ? (m2 ? r'))"
      by (smt (z3) Rules.distinct(9) join_conditions.elims option.distinct(1))
    then have "m1 = m2"
      by (metis Some join_conditions.simps(2) option.distinct(1))
    then show ?thesis using 2
      by (simp add: ex join_conditions_valid)
  qed
next
  case (3 rules)
  then show ?case by (simp add: monotonic_choice)
next
  case (4 e)
  then show ?case by simp
next
  case (5 r1 r2)
  then show ?case by (simp add: monotonic_seq)
qed

subsubsection \<open>Merge Common Conditions in Non-deterministic Choice\<close>

fun find_common :: "('e, 'cond) MATCH \<Rightarrow> ('e, 'cond) Rules \<Rightarrow> ('e, 'cond) Rules option" where
  "find_common m (m' ? r) = (if m = m' then Some r else None)" |
  "find_common m r = None"

fun find_uncommon :: "('e, 'cond) MATCH \<Rightarrow> ('e, 'cond) Rules \<Rightarrow> ('e, 'cond) Rules option" where
  "find_uncommon m (m' ? r) = (if m = m' then None else Some (m' ? r))" |
  "find_uncommon m r = Some r"

definition join_common :: "('e, 'cond) MATCH \<Rightarrow> ('e, 'cond) Rules list \<Rightarrow> ('e, 'cond) Rules list" where
  "join_common m rules = List.map_filter (find_common m) rules"

definition join_uncommon :: "('e, 'cond) MATCH \<Rightarrow> ('e, 'cond) Rules list \<Rightarrow> ('e, 'cond) Rules list" where
  "join_uncommon m rules = List.map_filter (find_uncommon m) rules"

function (sequential) combine_conditions :: "('e, 'cond) Rules \<Rightarrow> ('e, 'cond) Rules" where
  "combine_conditions (base e) = base e" |
  "combine_conditions (r1 else r2) = (combine_conditions r1 else combine_conditions r2)" |
  "combine_conditions (m ? r) = (m ? combine_conditions r)" |
  "combine_conditions (choice ((m ? r) # rules)) = 
    choice ((m ? combine_conditions (choice (r # join_common m rules)))
      # [combine_conditions (choice (join_uncommon m rules))])" |
  "combine_conditions (choice rules) = 
    choice (List.map combine_conditions rules)" |
  "combine_conditions (r1 \<then> r2) = (combine_conditions r1 \<then> combine_conditions r2)"
  apply pat_completeness+
  by simp+

fun common_size :: "('e, 'cond) Rules \<Rightarrow> nat" where
  "common_size (m ? r) = 1 + common_size r" |
  "common_size (base e) = 0" |
  "common_size (r1 else r2) = 1 + common_size r1 + common_size r2" |
  "common_size (choice (rule # rules)) = 1 + common_size rule + common_size (choice rules)" |
  "common_size (choice []) = 0" |
  "common_size (r1 \<then> r2) = 1 + common_size r1 + common_size r2"

lemma find_common_size:
  assumes "(find_common m r) \<noteq> None"
  shows "size_Rule (the (find_common m r)) < size_Rule r"
  using assms apply (induction r rule: find_common.induct)
  apply simp+
  using size_Rule_def apply fastforce apply fastforce by simp+

lemma common_size_choice_gt:
  "x \<in> set va \<Longrightarrow> common_size x \<le> common_size (choice va)"
  apply (induction va) apply simp
  by fastforce

lemma find_common_defn:
  assumes "find_common m x = v"
  shows "v \<noteq> None \<longleftrightarrow> (\<exists>r. x = (m ? r) \<and> v = Some r)"
  using assms apply (induction m x rule: find_common.induct) unfolding find_common.simps apply force
  by simp+

lemma find_common_shrinks:
  "find_common m x = Some z \<Longrightarrow> common_size z \<le> common_size x"
  unfolding find_common.simps using find_common_defn
  by (metis common_size.simps(1) le_add2 option.distinct(1) option.inject)

lemma join_common_shrinks:
  "common_size (choice (join_common m x)) \<le> common_size (choice x)"
  unfolding join_common_def
  apply (induction x)
   apply (simp add: map_filter_simps(2))
  subgoal for a x
    apply (cases "find_common m a") unfolding List.map_filter_def apply simp
    using find_common_shrinks apply simp
    using add_le_mono by blast
  done

lemma find_uncommon_preserve:
  "find_uncommon m r = Some r \<or> find_uncommon m r = None"
  by (metis find_uncommon.elims)

lemma join_uncommon_subset:
  "set (join_uncommon m x) \<subseteq> set x"
  unfolding join_uncommon_def List.map_filter_def using find_uncommon_preserve
  by (smt (verit, best) comp_def filter_is_subset list.map_ident_strong mem_Collect_eq option.sel set_filter)

lemma size_join_uncommon:
  "\<forall>r \<in> set (join_uncommon m rules) . find_uncommon m r = Some r' \<longrightarrow> common_size r' \<le> common_size r"
  unfolding join_uncommon_def map_filter_def
  apply (induction rule: find_uncommon.induct; auto) 
  apply (metis common_size.simps(1) dual_order.eq_iff find_uncommon_preserve option.distinct(1) option.sel plus_1_eq_Suc)
    apply (metis Suc_eq_plus1_left add_Suc_right add_Suc_shift common_size.simps(3) find_uncommon_preserve option.distinct(1) option.inject order_refl)
  apply (metis Suc_eq_plus1_left add_Suc_right add_Suc_shift common_size.simps(6) find_uncommon_preserve le_refl option.distinct(1) option.inject)
  by (metis find_uncommon_preserve option.distinct(1) option.inject verit_comp_simplify1(2))

lemma find_uncommon_shrinks:
  "find_uncommon m x = Some z \<Longrightarrow> common_size z \<le> common_size x"
  unfolding find_uncommon.simps
  by (metis dual_order.refl find_uncommon_preserve option.distinct(1) option.inject)

lemma join_uncommon_shrinks:
  "common_size (choice (join_uncommon m rules))
       \<le> (common_size (choice rules))"
  unfolding join_uncommon_def
  apply (induction rules)
   apply (simp add: map_filter_simps(2))
  subgoal for a x
    apply (cases "find_uncommon m a") unfolding List.map_filter_def apply simp
    using find_uncommon_shrinks
    by fastforce
  done

termination combine_conditions
  apply (relation "measures [common_size]") apply auto[1] apply simp+ using join_common_shrinks
  using le_imp_less_Suc apply blast
          apply (simp add: le_imp_less_Suc) defer
         apply simp apply auto[1]
        apply (simp add: common_size_choice_gt le_imp_less_Suc)
       apply auto[1] using common_size_choice_gt apply fastforce
      apply auto[1] using common_size_choice_gt apply fastforce
     apply auto[1] using common_size_choice_gt apply fastforce
    apply simp+ using join_uncommon_shrinks
  by (metis le_imp_less_Suc plus_1_eq_Suc trans_le_add2)

lemma join_common_empty: "join_common m [] = []"
  by (simp add: join_common_def map_filter_simps(2))
lemma join_uncommon_empty: "join_uncommon m [] = []"
  by (simp add: join_uncommon_def map_filter_simps(2))

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
      using eval_rules.intros(6) r by blast
  next
    case (cond' m' r')
    then show ?thesis
    proof (cases "m = m'")
      case True
      then have "r' \<in> set (join_common m rules)"
        using cond' r join_common_set_def
        by blast
      then show ?thesis
        by (metis True cond' eval_rules.intros(6) image_eqI image_set pull_cond_out_rhs r)
    next
      case False
      have "r \<in> set (join_uncommon m rules)"
        using join_uncommon_set_def False r
        using cond' by blast
      then show ?thesis
        using eval_rules.intros(6) r by blast
    qed
  next
    case (else' x31 x32)
    have "r \<in> set (join_uncommon m rules)"
      using join_uncommon_set_def else' r by blast
    then show ?thesis
      using eval_rules.intros(6) r by blast
  next
    case (seq x41 x42)
    have "r \<in> set (join_uncommon m rules)"
      using join_uncommon_set_def seq r by blast
    then show ?thesis
      using eval_rules.intros(6) r by blast
  next
    case (choice x5)
    have "r \<in> set (join_uncommon m rules)"
      using join_uncommon_set_def choice r by blast
    then show ?thesis
      using eval_rules.intros(6) r by blast
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

lemma combine_conditions_valid:
  "eval_rules r u e = eval_rules (combine_conditions r) u e"
  apply (induction r arbitrary: u e rule: combine_conditions.induct) apply simp
  apply (simp add: monotonic)+
        defer
  apply simp+
  apply (metis (mono_tags, lifting) choice_join combine_conditions.simps(1) list.simps(9) monotonic_choice)
  using monotonic_choice
  using combine_conditions.simps(7) monotonic_choice apply metis
  using combine_conditions.simps(8) monotonic_choice apply metis
  using combine_conditions.simps(9) monotonic_choice apply metis
   apply (simp add: monotonic)+
  subgoal premises p for m r rules u e
  proof (rule iffI)
    assume eval: "eval_rules (choice ((m ? r) # rules)) u e"
    show "eval_rules
     (choice
       [m ? combine_conditions (choice (r # join_common m rules)),
        combine_conditions (choice (join_uncommon m rules))])
     u e"
    proof (cases e)
      case None
      have "eval_rules (m ? (choice (r # join_common m rules))) u None \<and>
  eval_rules ((choice (join_uncommon m rules))) u None"
        using None cases_None eval by blast
      then have "eval_rules (m ? combine_conditions (choice (r # join_common m rules))) u None \<and>
  eval_rules (combine_conditions (choice (join_uncommon m rules))) u None" 
        using p monotonic_cond by blast
      then show ?thesis using None eval_choice_none by fastforce
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

subsubsection \<open>Eliminate Non-deterministic Choice Operations\<close>

fun eliminate_choice :: "('e, 'cond) Rules \<Rightarrow> ('e, 'cond) Rules" where
  "eliminate_choice (base e) = base e" |
  "eliminate_choice (r1 else r2) = (eliminate_choice r1 else eliminate_choice r2)" |
  "eliminate_choice (m ? r) = (m ? eliminate_choice r)" |
  "eliminate_choice (choice (r1 # choice [] # r2)) = eliminate_choice (choice (r1 # r2))" |
  "eliminate_choice (choice (r # [])) = eliminate_choice r" |
  "eliminate_choice (choice rules) = 
    choice (List.map eliminate_choice rules)" |
  "eliminate_choice (r1 \<then> r2) = (eliminate_choice r1 \<then> eliminate_choice r2)"

lemma eliminate_choice_valid_1:
  "{e. eval_rules r u e} = {e. eval_rules (eliminate_choice r) u e}"
  apply (induction r arbitrary: u rule: eliminate_choice.induct)
  apply simp unfolding eliminate_choice.simps
  apply (smt (verit) Collect_cong elseE eval_rules.intros(4) eval_rules.intros(5) mem_Collect_eq)
  unfolding eliminate_choice.simps
               apply (metis (mono_tags) Collect_cong mem_Collect_eq monotonic_cond)
  unfolding eliminate_choice.simps
  apply auto[1] 
  apply (smt (verit, del_insts) choiceE eval_choice_none eval_rules.intros(6) list.distinct(1) list.set_cases list.set_intros(1) list.set_intros(2) mem_Collect_eq set_ConsD)
  apply (smt (verit, ccfv_SIG) choiceE eval_choice_none eval_rules.intros(6) list.distinct(1) list.set_cases list.set_intros(1) list.set_intros(2) mem_Collect_eq set_ConsD)
  using choice_Single apply blast
  apply force
  apply (metis Collect_cong mem_Collect_eq monotonic_choice) 
      apply (metis (no_types, lifting) Collect_cong mem_Collect_eq monotonic_choice)
     apply (metis (no_types, lifting) Collect_cong mem_Collect_eq monotonic_choice)
      apply (metis Collect_cong mem_Collect_eq monotonic_choice)
  apply (metis (no_types, lifting) Collect_cong mem_Collect_eq monotonic_choice)
  by (smt (verit) Collect_cong mem_Collect_eq monotonic_seq)

lemma eliminate_choice_valid:
  "eval_rules r u e = eval_rules (eliminate_choice r) u e"
  using eliminate_choice_valid_1 by blast

subsection \<open>Combine Rule Optimizations\<close>

definition optimized_export :: "('e, 'cond) Rules \<Rightarrow> ('e, 'cond) Rules" where
  "optimized_export =
    eliminate_choice
    o combine_conditions
    o lift_common
    o lift_match
    o eliminate_noop"

(*
definition optimized_export :: "('e, 'cond) Rules \<Rightarrow> ('e, 'cond) Rules" where
  "optimized_export r =
    eliminate_noop r"*)


(*lemma elim_empty_preserve_def_vars:
  "def_vars m = def_vars (elim_empty m)"
  apply (induction m rule: elim_empty.induct) by simp+

lemma elim_empty_preserve_use_vars:
  "use_vars m = use_vars (elim_empty m)"
  apply (induction m rule: elim_empty.induct) apply simp
  using elim_empty_preserve_def_vars apply auto[1] by simp+

lemma elim_empty_preserve_valid:
  assumes "valid_match m"
  shows "valid_match (elim_empty m)"
    using assms apply (induction m rule: elim_empty.induct) apply simp
    using elim_empty_preserve_def_vars elim_empty_preserve_use_vars apply auto[1] 
    by simp+

lemma eliminate_empty_preserve_valid:
  assumes "valid_rules r"
  shows "valid_rules (eliminate_empty r)"
  using assms apply (induction r rule: eliminate_empty.induct) apply simp
  apply (simp add: elim_empty_preserve_valid) by simp+*)

lemma elim_noop_preserve_def_vars:
  "def_vars m = def_vars (elim_noop m)"
  apply (induction m rule: elim_noop.induct) by simp+

lemma elim_noop_preserve_use_vars:
  "use_vars m = use_vars (elim_noop m)"
  apply (induction m rule: elim_noop.induct) apply simp+
  using def_vars.simps(3) elim_noop_preserve_def_vars apply blast
  apply simp+
  using def_vars.simps(3) elim_noop_preserve_def_vars apply blast
  by simp+

lemma elim_noop_preserve_valid:
  assumes "valid_match m"
  shows "valid_match (elim_noop m)"
  using assms apply (induction m rule: elim_noop.induct) apply simp+
  using elim_noop_preserve_use_vars
  apply (metis use_vars.simps(3))
  apply simp+
  apply (metis DiffE UnE elim_noop_preserve_use_vars use_vars.simps(3))
  apply simp
  apply (metis elim_noop.simps(14) elim_noop.simps(22) elim_noop_preserve_def_vars valid_match.simps(2))
  apply simp
  apply (metis (no_types, lifting) elim_noop.simps(16) elim_noop_preserve_def_vars elim_noop_preserve_use_vars valid_match.simps(2))
  by simp+

lemma eliminate_noop_preserve_valid:
  assumes "valid_rules r"
  shows "valid_rules (eliminate_noop r)"
  using assms apply (induction r rule: eliminate_noop.induct)
  by (simp add: elim_noop_preserve_valid)+

(*
lemma lift_match_preserve_valid:
  assumes "valid_rules r"
  shows "valid_rules (lift_match r)"
  using assms apply (induction r rule: lift_match.induct)
  by simp+


lemma optimized_export_valid:
  assumes "valid_rules r"
  shows "eval_rules r u e = eval_rules (optimized_export r) u e"
  unfolding optimized_export_def comp_def
  using lift_match_valid eliminate_noop_valid 
  using combine_conditions_valid eliminate_choice_valid
  by (metis assms eliminate_noop_preserve_valid lift_common_valid lift_match_preserve_valid)

thm_oracles optimized_export_valid
*)

subsection \<open>Compiling Match Patterns\<close>

(*value "optimized_export
(generate
(Add (Sub (Variable ''x'') (Variable ''y'')) (Variable ''y''))
(Variable ''x'')
((Variable ''y''), \<lambda>x. True))"*)

definition gen_rewrite :: "('a) \<Rightarrow> 'a \<Rightarrow> VarName \<Rightarrow> ('a, 'b) Rules" where
  "gen_rewrite p r v = (
    let (s, lhs) = (match_pattern p v ({|v|}, Map.empty)) in lhs? base (var_expr r s))"

fun compile' :: "('a, 'b, 'c) Strategy \<Rightarrow> ('a, 'b) Rules option" where
  "compile' (s1 \<rightarrow> s2) = Some (gen_rewrite s1 s2 ''e'')" |
  "compile' _ = None"(* |
  "compile (s1?; (v1?; s3; v2!); s2!) = ((gen_pattern s1 ''e'') ? base s2)"*)

fun compile :: "(('a, 'b, 'c) Strategy \<times> 'a) \<Rightarrow> (('a, 'b) Rules \<times> 'a) option" where
  "compile ((s1 \<rightarrow> s2), t) = Some ((gen_rewrite s1 s2 ''e''), t)" |
  "compile _ = None"

(*fun compile :: "'a::Rewritable Strategy \<Rightarrow> Scope \<Rightarrow> 'a Rules" where
  "compile (id; r) s = noop? compile r s" |
  (*"compile (fail; s) = match ''x'' (var ''x'')? compile s"*)
  "compile (m?; r) s = 
    (let (s, lhs) = (match_pattern m ''e'' s) in
     lhs? compile r s)" |
  "compile (r!) s = base (ground_expr r s)" |
  "compile ((v1?; x; v2!); r) s = (if v1 = v2 then (condition x)? compile r s else noop)"*)

end

subsection \<open>Example: Arithmetic\<close>

(*
setup \<open>Locale_Code.open_block\<close>
ML_val \<open>Locale_Code.tracing_enabled\<close>
interpretation ArithmeticCompiled: CompiledRewrites
  size_Arithmetic
  "eval_condition"
  "ground_condition"
  "eval_transformer"
  "ground_transformer"
  rewrite_Arithmetic
  match_Arithmetic
  varof_Arithmetic
  var_Arithmetic
  subexprs_Arithmetic
  chain_Arithmetic
proof
  fix e :: Arithmetic
  show "\<forall>e' \<in> set (subexprs_Arithmetic e). size_Arithmetic e > size_Arithmetic e'"
    by (cases e; simp)
next
  fix f :: "Arithmetic \<Rightarrow> Arithmetic"
  fix e :: Arithmetic
  show "map f (subexprs_Arithmetic e) = subexprs_Arithmetic (snd (chain_Arithmetic (\<lambda>e a. (plus a 1, f e)) e 0))"
    by (cases e; simp)
next
  fix f :: "Arithmetic \<Rightarrow> Arithmetic"
  fix e :: Arithmetic
  show "length (subexprs_Arithmetic e) = fst (chain_Arithmetic (\<lambda>e a. (plus a 1, f e)) e 0)"
    by (cases e; simp)
qed
setup \<open>Locale_Code.close_block\<close>

definition "join = ArithmeticCompiled.join"
definition "compile' = ArithmeticCompiled.compile'"
definition "generate = ArithmeticCompiled.generate"
definition "match_pattern = ArithmeticCompiled.match_pattern"
definition "optimized_export = ArithmeticCompiled.optimized_export"
notation ArithmeticCompiled.choice ("choice _")
notation ArithmeticCompiled.else ("_ else _")

export_code "compile'" checking SML

value "compile' RedundantAdd"
text \<open>@{value[display] "compile' RedundantAdd"}\<close>
value "compile' RedundantSub"
text \<open>@{value[display] "compile' RedundantSub"}\<close>
(*value "compile' ShiftConstRight"
value "compile' EvalMinus1"
value "compile' EvalAdd"*)

value "match_pattern
(Sub (Add (Variable ''x'') (Variable ''y'')) (Variable ''y''))
''e'' ({|''e''|}, Map.empty)"
text \<open>@{value "match_pattern
(Sub (Add (Variable ''x'') (Variable ''y'')) (Variable ''y''))
''e'' ({|''e''|}, Map.empty)"}\<close>

value "match_pattern
(Sub 
    (Add 
        (Sub (Variable ''x'') (Variable ''x''))
        (Sub (Variable ''y'') (Variable ''x'')))
    (Variable ''y''))
''e'' ({|''e''|}, Map.empty)"
text \<open>@{value "match_pattern
(Sub 
    (Add 
        (Sub (Variable ''x'') (Variable ''x''))
        (Sub (Variable ''y'') (Variable ''x'')))
    (Variable ''y''))
''e'' ({|''e''|}, Map.empty)"}\<close>

definition Identity where
  "Identity = generate 
    (Add
      (var ''x'')
      (Number 0))
    (var ''x'')"

value "Identity"
text "@{value[display] \<open>Identity\<close>}"
value "optimized_export Identity"
text "@{value[display] \<open>optimized_export Identity\<close>}"

text \<open>@{text "const x + const y \<longrightarrow> const (x + y)"}\<close>
definition Evaluate where
  "Evaluate = generate 
    (Add
      (var ''x'')
      (var ''y''))
    ((var ''x''))"
(* doesn't support constant evaluation *)
value "Evaluate"
value "(optimized_export (Evaluate))"

(*
text \<open>@{text "x * const y \<longrightarrow> x << const (log2 y)"}\<close>
definition Shift where
  "Shift = generate 
    (BinaryExpr BinMul
      (var ''x'')
      (ConstantVar STR ''y''))
    ((BinaryExpr BinLeftShift (var ''x'') (ConstantVar STR ''y'')))
    (PowerOf2 (ConstantVar STR ''y''))"
(* doesn't support constant evaluation *)
value "Shift"
*)

text \<open>@{text "const x + y \<longrightarrow> y + const x when NotConst y"}\<close>
definition LeftConst where
  "LeftConst = generate 
    (Add
      (var ''x'')
      (var ''y''))
    ((Add (var ''y'') (var ''x'')))"
(* doesn't support constant evaluation *)
value "LeftConst"

value "(choice [LeftConst, Evaluate, Identity])"
text "@{value[display] \<open>choice [LeftConst, Evaluate, Identity]\<close>}"
value "(optimized_export (choice [LeftConst, Evaluate, Identity]))"
text "@{value[display] \<open>(optimized_export (choice [LeftConst, Evaluate, Identity]))\<close>}"
value "(optimized_export (optimized_export (choice [LeftConst, Evaluate, Identity])))"
text "@{value[display] \<open>(optimized_export (optimized_export (choice [LeftConst, Evaluate, Identity])))\<close>}"
*)







(*
value "eval (RedundantAdd <+ RedundantSub) ((Add (Number 10) (Number 0)), fmempty)"

inductive loadStrategy :: "('a::Rewritable Strategy \<times> 'a) \<Rightarrow> ('a Strategy \<times> 'a State \<times> bool) \<Rightarrow> bool" where
  "loadStrategy (s, t) (s, (t, fmempty), False)"
inductive stepStrategy :: "('a::Rewritable Strategy \<times> 'a State \<times> bool) => ('a Strategy \<times> 'a State \<times> bool) \<Rightarrow> bool" where
  "\<lbrakk>eval s state = (state', b');
    snd state = fmempty\<rbrakk> \<Longrightarrow>
   stepStrategy (s, state, b) (s, state', b')"
fun isStrategyTerm :: "('a Strategy \<times> 'a State \<times> bool) \<Rightarrow> bool" where
  "isStrategyTerm (s, state, m) = (snd state \<noteq> fmempty)"

inductive loadRules :: "('a::Rewritable Rules \<times> 'a) \<Rightarrow> ('a::Rewritable Rules \<times> 'a Subst \<times> 'a option \<times> bool) \<Rightarrow> bool" where
  "loadRules (r, t) (r, Map.empty(''e'' \<mapsto> t), None, False)"
inductive stepRules :: "('a::Rewritable Rules \<times> 'a Subst \<times> 'a option \<times> bool) => ('a::Rewritable Rules \<times> 'a Subst \<times> 'a option \<times> bool) \<Rightarrow> bool" where
  "\<lbrakk>eval_rules r u e'\<rbrakk> \<Longrightarrow>
   stepRules (r, u, e, False) (r, u, e', True)"
fun isRulesTerm :: "('a::Rewritable Rules \<times> 'a Subst \<times> 'a option \<times> bool) \<Rightarrow> bool" where
  "isRulesTerm (r, u, e, f) = f"

fun compatible :: "'a::Rewritable Strategy \<Rightarrow> 'a Rules \<Rightarrow> bool" where
  "compatible (s1 \<rightarrow> s2) r = (r = (gen_rewrite s1 s2 ''e''))" |
  "compatible _ _ = False"

inductive match :: "('a::Rewritable Strategy \<times> 'a State \<times> bool) => ('a::Rewritable Rules \<times> 'a Subst \<times> 'a option \<times> bool) \<Rightarrow> bool" where
  NotRun:  
  "\<lbrakk>snd state = fmempty \<and> Some (fst state) = subst ''e'' \<and> compatible s r\<rbrakk>
    \<Longrightarrow> match (s, state, m) (r, subst, None, False)" |
  Succeed:
  "\<lbrakk>snd state \<noteq> fmempty \<and> fst state = out \<and> compatible s r\<rbrakk>
    \<Longrightarrow> match (s, state, True) (r, subst, Some out, True)" |
  Fail:
  "\<lbrakk>snd state \<noteq> fmempty \<and> compatible s r\<rbrakk>
    \<Longrightarrow> match (s, state, False) (r, subst, None, True)"
(*fun compile :: "(IRGraph \<times> Params) \<Rightarrow> (IRGraph \<times> Params) option" where
  "compile (g, p) = Some (g, p)"*)

(*theorem stepDet:
   "(g, p \<turnstile> (nid,m,h) \<rightarrow> next) \<Longrightarrow>
   (\<forall> next'. ((g, p \<turnstile> (nid,m,h) \<rightarrow> next') \<longrightarrow> next = next'))"
proof (induction rule: "step.induct")*)

(* FALSE: eval_rules is nondet
lemma stepRulesDet:
  "stepRules x y \<Longrightarrow> \<forall>z. stepRules x z \<longrightarrow> y = z"
  apply (induction rule: "stepRules.induct")
  using stepRules.simps
*)

lemma compile_correct:
  assumes "eval (s1 \<rightarrow> s2) (e, fmempty) = ((e', b), True)"
  shows "eval_rules (gen_rewrite s1 s2 ''e'') [''e'' \<mapsto> e] (Some e')"
proof -
  obtain u' suc where s1: "eval (s1?) (e, fmempty) = (u', suc)"
    by fastforce
  then have "suc = True"
    using assms prod.inject by fastforce
  have "eval (s1 \<rightarrow> s2) (e, fmempty) = (let (u', suc) = eval (s1?) (e, fmempty) in
        if suc then eval (s2!) u' else eval fail u')"
    by simp
  then have "eval (s1 \<rightarrow> s2) (e, fmempty) = eval (s2!) u'"
    using assms
    by (smt (verit, best) Pair_inject s1 eval.simps(5) old.prod.case)
  have "Stratego.match s1 e = Some b"
    using s1 sorry
  then show ?thesis sorry
qed

lemma preserves_step:
  assumes "compatible s r"
  assumes "snd state = fmempty"
  assumes "Some (fst state) = subst ''e''"
  assumes "stepRules (r, subst, None, False) s2'"
  shows "(\<exists>s1'. stepStrategy\<^sup>+\<^sup>+ (s, state, m) s1' \<and> CompileRewrite.match s1' s2')"
proof -
  obtain e' where eRule: "s2' = (r, subst, e', True)"
    using eval_always_result stepRules.intros
    by (smt (verit, ccfv_threshold) assms(4) fst_conv snd_conv stepRules.simps)
  then have "eval_rules r subst e'"
    using assms(4) stepRules.cases by fastforce
  obtain state' b' where eStrat: "stepStrategy (s, state, m) (s, state', b')"
    by (metis assms(2) prod.collapse stepStrategy.intros)
  then have "eval s state = (state', b')"
    by (simp add: stepStrategy.simps)
  then have compat: "compatible s r"
    using assms(1) by simp
  then obtain s1 s2 where stype: "s = (s1 \<rightarrow> s2)"
    by (meson CompileRewrite.compatible.elims(2))
  then have "r = (gen_rewrite s1 s2 ''e'')"
    using compat by auto
  then have "match (s, state', b') (r, subst, e', True)"
    using stype apply (induction s) apply simp+
    using compile_correct sorry
  also have "stepStrategy\<^sup>+\<^sup>+ (s, state, m) (s, state', b')"
    by (simp add: eStrat tranclp.r_into_trancl)
  then show ?thesis using calculation eRule assms(3)
    by blast
  qed

(*"\<lbrakk>eval s state = (state', b');
    snd state = fmempty\<rbrakk> \<Longrightarrow>
   stepStrategy (s, state, b) (s, state', b')"*)

interpretation compile_valid:
  compiler stepStrategy stepRules isStrategyTerm isRulesTerm
    loadStrategy loadRules
    "\<lambda>_ _. False" "\<lambda>_. match" compile
  apply standard
  using finished_def stepStrategy.cases apply fastforce
  using finished_def stepRules.cases apply fastforce
     apply simp
  using isRulesTerm.simps match.cases apply fastforce
  subgoal for _ s2 s1 s2'
    apply (induction rule: match.induct)
      defer
      apply (simp add: stepRules.simps)
     apply (simp add: stepRules.simps)
    using preserves_step by blast
  subgoal premises p for p1 p2 s1
  proof -
    obtain lhs rhs t where "p1 = (lhs \<rightarrow> rhs, t)"
      using p(1) apply (cases "compile p1")
       apply simp sorry
    then have "p2 = ((gen_rewrite lhs rhs ''e''), t)"
      using p(1) by simp
    have loadS: "loadStrategy p1 (lhs \<rightarrow> rhs, (t, fmempty), False)"
      by (simp add: \<open>p1 = (lhs \<rightarrow> rhs, t)\<close> loadStrategy.intros)
    have loadR: "loadRules p2 ((gen_rewrite lhs rhs ''e''), Map.empty(''e'' \<mapsto> t), None, False)"
      using \<open>p2 = (gen_rewrite lhs rhs ''e'', t)\<close> loadRules.intros by blast
    then have "match (lhs \<rightarrow> rhs, (t, fmempty), False) ((gen_rewrite lhs rhs ''e''), [''e'' \<mapsto> t], None, False)"
    proof -
      have "snd (t, fmempty) = fmempty"
        by simp
      also have "Some (fst (t, fmempty)) = [''e'' \<mapsto> t] ''e''"
        by simp
      then show ?thesis
        using match.NotRun
        using calculation
        using CompileRewrite.compatible.simps(1) by blast
    qed
    then show ?thesis using p
      by (metis \<open>p2 = (gen_rewrite lhs rhs ''e'', t)\<close> loadRules.simps loadS prod.inject)
  qed
  done
*)

end