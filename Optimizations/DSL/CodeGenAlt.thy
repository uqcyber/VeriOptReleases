text_raw "\\newpage"
section \<open>Alternative Code Generation\<close>

theory CodeGenAlt
imports
    Semantics.IRTreeEvalThms
    Semantics.TreeToGraphThms
    Fresh.Fresh_String
    "HOL-Library.Monad_Syntax" Locale_Code.Locale_Code
begin

declare [[show_types=false]]

subsection \<open>IRExpr Matching Semantics\<close>

type_synonym VarName = "String.literal"

type_synonym Subst = "VarName \<rightharpoonup> IRExpr"

fun compatible :: "Subst \<Rightarrow> Subst \<Rightarrow> bool" where
  "compatible \<sigma>\<^sub>1 \<sigma>\<^sub>2 = (\<forall>x \<in> dom \<sigma>\<^sub>1. \<sigma>\<^sub>2 x \<noteq> None \<longrightarrow> \<sigma>\<^sub>1 x = \<sigma>\<^sub>2 x)"

fun substitution_union :: "Subst option \<Rightarrow> Subst option \<Rightarrow> Subst option" (infix "\<uplus>" 70) where
  "substitution_union s\<^sub>1 s\<^sub>2 = do {
      \<sigma>\<^sub>1 <- s\<^sub>1;
      \<sigma>\<^sub>2 <- s\<^sub>2;
      (if compatible \<sigma>\<^sub>1 \<sigma>\<^sub>2 then Some (\<sigma>\<^sub>1 ++ \<sigma>\<^sub>2) else None)
  }"

fun match_tree :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> Subst option" where
  "match_tree (UnaryExpr op x) (UnaryExpr op' x') = 
      (if op = op' then match_tree x x' else None)" |
  "match_tree (BinaryExpr op x y) (BinaryExpr op' x' y') = 
      (if op = op' then (match_tree x x') \<uplus> (match_tree y y') else None)" |
  "match_tree (ConditionalExpr c t f) (ConditionalExpr c' t' f') = 
      (match_tree c c') \<uplus> ((match_tree t t') \<uplus> (match_tree f f'))" |
  "match_tree (ParameterExpr i1 s1) (ParameterExpr i2 s2) = 
      (if i1 = i2 then Some Map.empty else None)" |
  "match_tree (LeafExpr n1 s1) (LeafExpr n2 s2) = 
      (if n1 = n2 then Some Map.empty else None)" |
  "match_tree (ConstantExpr v) (ConstantExpr v') = 
      (if v = v' then Some Map.empty else None)" |
  "match_tree (ConstantVar name) (ConstantExpr v) = 
      Some ([name \<mapsto> (ConstantExpr v)])" |
  "match_tree (VariableExpr name s) e = 
      Some ([name \<mapsto> e])" |
  "match_tree _ _ = None"

subsection \<open>MATCH Datatype\<close>

fun \<L> :: "IRExpr \<Rightarrow> VarName set" where
  "\<L> (VariableExpr vn s) = {vn}" |
  "\<L> (ConstantVar vn) = {vn}" |
  "\<L> (ConstantExpr c) = {}" |
  "\<L> (UnaryExpr op x) = \<L> x" |
  "\<L> (BinaryExpr op x y) = \<L> x \<union> \<L> y" |
  "\<L> (ConditionalExpr c t f) = \<L> c \<union> \<L> t \<union> \<L> f" |
  "\<L> (ParameterExpr nid s) = {}" |
  "\<L> (LeafExpr nid s) = {}"

datatype PatternExpr =
    UnaryPattern IRUnaryOp VarName
  | BinaryPattern IRBinaryOp VarName VarName
  | ConditionalPattern VarName VarName VarName
  | VariablePattern VarName
  | ConstantPattern Value
  | ConstantVarPattern VarName
  | ParameterPattern nat
  | LeafPattern nat

datatype MATCH = \<comment> \<open>Note side conditions are temporarily not handled.\<close>
  match VarName PatternExpr |
  equality VarName VarName (infixl "==" 52) |
  andthen MATCH MATCH (infixr "&&" 50) |
  (*condition SideCondition |*)
  noop VarName

fun pattern_variables :: "PatternExpr \<Rightarrow> String.literal set" where
  "pattern_variables (UnaryPattern op x) = {x}" |
  "pattern_variables (BinaryPattern op x y) = {x, y}" |
  "pattern_variables (ConditionalPattern c t f) = {c, t, f}" |
  "pattern_variables (VariablePattern v) = {}" |
  "pattern_variables (ConstantPattern v) = {}" |
  "pattern_variables (ConstantVarPattern v) = {}" |
  "pattern_variables (ParameterPattern nid) = {}" |
  "pattern_variables (LeafPattern nid) = {}"

fun def_vars :: "MATCH \<Rightarrow> String.literal set" where
  "def_vars (match v p) = pattern_variables p" |
  "def_vars (equality e1 e2) = {e1}" |
  "def_vars (m1 && m2) = def_vars m1 \<union> def_vars m2" |
  "def_vars (noop v) = {}"

fun use_vars :: "MATCH \<Rightarrow> String.literal set" where
  "use_vars (match v p) = {v}" |
  "use_vars (equality e1 e2) = {}" |
  (*"use_vars (m1 && m2) = use_vars m1 \<union> (use_vars m2 - def_vars m1)" |*)
  "use_vars (m1 && m2) = use_vars m1 \<union> use_vars m2" |
  "use_vars (noop v) = {v}"

fun valid_match :: "MATCH \<Rightarrow> bool" where
  "valid_match (match v (UnaryPattern op x)) = (v \<noteq> x)" |
  "valid_match (match v (BinaryPattern op x y)) = (v \<noteq> x \<and> v \<noteq> y \<and> x \<noteq> y)" |
  "valid_match (match v (ConditionalPattern c t f)) = (v \<noteq> c \<and> v \<noteq> t \<and> v \<noteq> f \<and> c \<noteq> t \<and> c \<noteq> f \<and> t \<noteq> f)" |
  "valid_match (m1 && m2) = (valid_match m1 \<and> valid_match m2 \<and> use_vars m1 \<inter> def_vars m2 = {})" |
  "valid_match _ = True"

subsection \<open>Lowering IRExpr\<close>

definition fresh_var :: "VarName set \<Rightarrow> VarName" where
  "fresh_var \<Sigma> = fresh \<Sigma> (STR ''X'')"

lemma X_outofrange:
  "(of_char(last (String.explode (STR ''X'')))::nat) < 97"
  by eval

lemma upChar_preserves_head:
  assumes "length s > 0"
  assumes "hd s = CHR ''X''"
  shows "hd (upChar s) = CHR ''X''"
  using assms proof (induction s)
  case Nil
  then show ?case by simp
next
  case (Cons a s)
  then show ?case proof (cases "of_char(last (a # s)) \<ge> 97 \<and> of_char(last (a # s)) < 122")
    case True
    then show ?thesis unfolding upChar.simps 
      using Cons.prems(2) by auto
  next
    case False
    then show ?thesis
      using Cons.prems(2) by auto
  qed
qed

lemma fresh_string_preserves_head:
  assumes "finite \<Sigma>"
  assumes "length s > 0"
  assumes "hd s = CHR ''X''"
  shows "hd (fresh_string \<Sigma> s) = hd s"
  using assms proof (induction \<Sigma> s rule: fresh_string.induct)
  case (1 Y Xs)
  then show ?case
    by (metis Fresh_String.Fresh Fresh_String.Up leD length_greater_0_conv list.size(3) nat_less_le ordst_def upChar_ordst upChar_preserves_head)
next
  case (2 Y Xs)
  then show ?case
    by auto
qed

lemma fresh_var_head:
  assumes "finite \<Sigma>"
  shows "hd (String.explode (fresh_var \<Sigma>)) = CHR ''X''"
  using assms
  by (simp add: Literal.rep_eq fresh_literal.rep_eq fresh_string_preserves_head fresh_var_def)

definition starts_with :: "VarName \<Rightarrow> char \<Rightarrow> bool" where
  "starts_with v c = (hd (String.explode v) = c)"

definition safe_prefix :: "VarName \<Rightarrow> bool" where
  "safe_prefix v = (\<not>(starts_with v CHR ''X''))"

fun valid_pattern :: "IRExpr \<Rightarrow> bool" where
  "valid_pattern (VariableExpr vn s) = safe_prefix vn" |
  "valid_pattern (ConstantVar vn) = safe_prefix vn" |
  "valid_pattern (ConstantExpr c) = True" |
  "valid_pattern (UnaryExpr op x) = valid_pattern x" |
  "valid_pattern (BinaryExpr op x y) = (valid_pattern x \<and> valid_pattern y)" |
  "valid_pattern (ConditionalExpr c t f) = (valid_pattern c \<and> valid_pattern t \<and> valid_pattern f)" |
  "valid_pattern (ParameterExpr nid s) = True" |
  "valid_pattern (LeafExpr nid s) = True"

lemma fresh_var_prefix:
  assumes "safe_prefix s"
  shows "fresh_var \<Sigma> \<noteq> s"
  using assms unfolding safe_prefix_def starts_with_def
  by (metis Fresh_String.Fresh Literal.rep_eq add_Suc_right fresh_literal.rep_eq fresh_string_preserves_head fresh_var_def list.sel(1) list.size(4) zero_less_Suc)

lemma prefix_preserves_freshness:
  assumes "\<forall>v \<in> \<L> e. safe_prefix v"
  shows "\<forall>\<Sigma>. fresh_var \<Sigma> \<notin> \<L> e"
  using assms
  using fresh_var_prefix by blast

lemma valid_pattern_preserves_freshness:
  assumes "valid_pattern e"
  shows "\<forall>\<Sigma>. fresh_var \<Sigma> \<notin> \<L> e"
  using assms apply (induction e) apply auto
  using fresh_var_prefix safe_prefix_def by blast+

lemma freshness:
  assumes "finite \<Sigma>"
  shows "fresh_var \<Sigma> \<notin> \<Sigma>"
  by (simp add: assms(1) fresh_notIn fresh_var_def)

inductive lower :: "IRExpr \<Rightarrow> VarName set \<Rightarrow> MATCH \<Rightarrow> VarName \<Rightarrow> VarName set \<Rightarrow> bool"
  ("'(_, _') \<leadsto> '(_, _, _')" 70) where
  VariableUnseen:
  "vn \<notin> \<Sigma> \<Longrightarrow> (VariableExpr vn s, \<Sigma>) \<leadsto> (noop vn, vn, \<Sigma> \<union> {vn})" |
  VariableSeen:
  "\<lbrakk>vn \<in> \<Sigma>; v' = fresh_var \<Sigma>\<rbrakk> \<Longrightarrow> (VariableExpr vn s, \<Sigma>) \<leadsto> (v' == vn, v', \<Sigma> \<union> {v'})" |
  ConstantPattern:
  "v' = fresh_var \<Sigma> \<Longrightarrow> (ConstantExpr c, \<Sigma>) \<leadsto> (match v' (ConstantPattern c), v', \<Sigma> \<union> {v'})" |
  UnaryPattern:
  "\<lbrakk>(x, \<Sigma>) \<leadsto> (m\<^sub>x, v\<^sub>x, \<Sigma>\<^sub>x);
    v' = fresh_var \<Sigma>\<^sub>x\<rbrakk>
  \<Longrightarrow> (UnaryExpr op x, \<Sigma>) \<leadsto> (match v' (UnaryPattern op v\<^sub>x) && m\<^sub>x, v', \<Sigma>\<^sub>x \<union> {v'})" |
  BinaryPattern:
  "\<lbrakk>(x, \<Sigma>) \<leadsto> (m\<^sub>x, v\<^sub>x, \<Sigma>\<^sub>x); (y, \<Sigma>\<^sub>x) \<leadsto> (m\<^sub>y, v\<^sub>y, \<Sigma>\<^sub>y);
    v' = fresh_var \<Sigma>\<^sub>y\<rbrakk>
  \<Longrightarrow> (BinaryExpr op x y, \<Sigma>) \<leadsto> (match v' (BinaryPattern op v\<^sub>x v\<^sub>y) && m\<^sub>x && m\<^sub>y, v', \<Sigma>\<^sub>y \<union> {v'})" |
  ConditionalPattern:
  "\<lbrakk>(c, \<Sigma>) \<leadsto> (m\<^sub>c, v\<^sub>c, \<Sigma>\<^sub>c); (t, \<Sigma>\<^sub>c) \<leadsto> (m\<^sub>t, v\<^sub>t, \<Sigma>\<^sub>t);
    (f, \<Sigma>\<^sub>t) \<leadsto> (m\<^sub>f, v\<^sub>f, \<Sigma>\<^sub>f); v' = fresh_var \<Sigma>\<^sub>f\<rbrakk>
  \<Longrightarrow> (ConditionalExpr c t f, \<Sigma>) \<leadsto> (match v' (ConditionalPattern v\<^sub>c v\<^sub>t v\<^sub>f) && m\<^sub>c && m\<^sub>t && m\<^sub>f, v', \<Sigma>\<^sub>f \<union> {v'})" |

  ConstantVariableUnseen:
  "vn \<notin> \<Sigma> \<Longrightarrow> (ConstantVar vn, \<Sigma>) \<leadsto> (noop vn, vn, \<Sigma> \<union> {vn})" | \<comment> \<open>Note that constant variables are also not properly handled currently.\<close>
  ConstantVariableSeen:
  "vn \<in> \<Sigma> \<and> v' = fresh_var \<Sigma> \<Longrightarrow> (ConstantVar vn, \<Sigma>) \<leadsto> (v' == vn, v', \<Sigma> \<union> {v'})" |
  ParameterPattern:
  "v' = fresh_var \<Sigma> \<Longrightarrow> (ParameterExpr nid s, \<Sigma>) \<leadsto> (match v' (ParameterPattern nid), v', \<Sigma> \<union> {v'})" |
  LeafPattern:
  "v' = fresh_var \<Sigma> \<Longrightarrow> (LeafExpr nid s, \<Sigma>) \<leadsto> (match v' (LeafPattern nid), v', \<Sigma> \<union> {v'})"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool as lowerC) lower .

inductive_cases lower_VariableExpr: "(VariableExpr vn s, \<Sigma>) \<leadsto> (m, v, \<Sigma>')"
inductive_cases lower_ConstantExpr: "(ConstantExpr c, \<Sigma>) \<leadsto> (m, v, \<Sigma>')"
inductive_cases lower_UnaryExpr: "(UnaryExpr op x, \<Sigma>) \<leadsto> (m, v, \<Sigma>')"
inductive_cases lower_BinaryExpr: "(BinaryExpr op x y, \<Sigma>) \<leadsto> (m, v, \<Sigma>')"
inductive_cases lower_ConditionalExpr: "(ConditionalExpr c t f, \<Sigma>) \<leadsto> (m, v, \<Sigma>')"
inductive_cases lower_ConstantVar: "(ConstantVar c, \<Sigma>) \<leadsto> (m, v, \<Sigma>')"
inductive_cases lower_ParameterExpr: "(ParameterExpr nid s, \<Sigma>) \<leadsto> (m, v, \<Sigma>')"
inductive_cases lower_LeafExpr: "(LeafExpr nid s, \<Sigma>) \<leadsto> (m, v, \<Sigma>')"

values "{(m, v, \<Sigma>) | m v \<Sigma>. 
(lower ((VariableExpr STR ''x'' default_stamp)) {} m v \<Sigma>)}"
values "{(m, v, \<Sigma>) | m v \<Sigma>. 
(lower (ConditionalExpr (VariableExpr STR ''x'' default_stamp) (VariableExpr STR ''y'' default_stamp) (VariableExpr STR ''x'' default_stamp)) {} m v \<Sigma>)}"

value "Predicate.the (lowerC (ConditionalExpr (VariableExpr STR ''x'' default_stamp) (VariableExpr STR ''y'' default_stamp) (VariableExpr STR ''x'' default_stamp)) {})"

lemma lower_total:
  "\<exists>m v \<Sigma>'. (e, \<Sigma>) \<leadsto> (m, v, \<Sigma>')"
  apply (induction e arbitrary: \<Sigma>)
  by (meson lower.intros)+

lemma lower_deterministic:
  assumes "(e, \<Sigma>) \<leadsto> (m\<^sub>1, v\<^sub>1, \<Sigma>'\<^sub>1)"
  assumes "(e, \<Sigma>) \<leadsto> (m\<^sub>2, v\<^sub>2, \<Sigma>'\<^sub>2)"
  shows "m\<^sub>1 = m\<^sub>2 \<and> v\<^sub>1 = v\<^sub>2 \<and> \<Sigma>'\<^sub>1 = \<Sigma>'\<^sub>2"
  using assms apply (induction e \<Sigma> m\<^sub>1 v\<^sub>1 \<Sigma>'\<^sub>1 arbitrary: m\<^sub>2 v\<^sub>2 \<Sigma>'\<^sub>2 rule: lower.induct)
          apply (metis Un_commute insert_is_Un lower_VariableExpr)
         apply (metis Un_commute insert_is_Un lower_VariableExpr)
        apply (metis Un_commute insert_is_Un lower_ConstantExpr)
       apply (metis Un_commute insert_is_Un lower_UnaryExpr)
      apply (smt (verit, best) Un_empty_right Un_insert_right lower_BinaryExpr)
      apply (smt (z3) Un_commute insert_is_Un lower_ConditionalExpr)
  apply (metis Un_insert_right boolean_algebra.disj_zero_right lower_ConstantVar)
    using lower_ConstantVar apply blast
   using lower_ParameterExpr apply blast
   using lower_LeafExpr by blast

lemma lower_sigma_update:
  assumes "(e, \<Sigma>) \<leadsto> (m, v, \<Sigma>')"
  shows "\<Sigma>' = \<Sigma> \<union> {v} \<union> def_vars m"
  using assms apply (induction rule: lower.induct) apply simp+
  by fastforce+

lemma lower_sigma_update1:
  assumes "(e, \<Sigma>) \<leadsto> (m, v, \<Sigma>')"
  shows "\<Sigma>' = \<Sigma> \<union> {v} \<union> use_vars m \<union> def_vars m"
  using assms apply (induction rule: lower.induct) apply simp+
  by force+

lemma lower_finite:
  assumes "finite \<Sigma>"
  assumes "(e, \<Sigma>) \<leadsto> (m, v, \<Sigma>')"
  shows "finite \<Sigma>'"
  using assms(2,1) apply (induction rule: lower.induct) by simp+

lemma lower_sigma_update2:
  assumes "finite \<Sigma>"
  assumes "(e, \<Sigma>) \<leadsto> (m, v, \<Sigma>')"
  shows "\<Sigma> \<inter> ({v} \<union> use_vars m \<union> def_vars m) = {}"
  using assms(2,1) proof (induction rule: lower.induct)
  case (VariableUnseen vn \<Sigma> s)
  then show ?case by simp
next
  case (VariableSeen vn \<Sigma> v' s)
  then show ?case
    by (simp add: freshness)
next
  case (ConstantPattern v' \<Sigma> c)
  then show ?case
    by (simp add: freshness)
next
  case (UnaryPattern x \<Sigma> m\<^sub>x v\<^sub>x \<Sigma>\<^sub>x v' op)
  have ih: "\<Sigma> \<inter> ({v\<^sub>x} \<union> use_vars m\<^sub>x \<union> def_vars m\<^sub>x) = {}"
    using UnaryPattern by presburger
  have seq: "({v'} \<union> use_vars (match v' (UnaryPattern op v\<^sub>x) && m\<^sub>x) \<union> def_vars (match v' (UnaryPattern op v\<^sub>x) && m\<^sub>x)) 
    = {v'} \<union> use_vars m\<^sub>x \<union> {v\<^sub>x} \<union> def_vars m\<^sub>x"
    by simp
  then show ?case
    by (metis UnaryPattern Int_insert_right UnCI Un_assoc Un_commute freshness insert_is_Un lower_finite lower_sigma_update)
next
  case (BinaryPattern x \<Sigma> m\<^sub>x v\<^sub>x \<Sigma>\<^sub>x y m\<^sub>y v\<^sub>y \<Sigma>\<^sub>y v' op)
  have ihx: "\<Sigma> \<inter> ({v\<^sub>x} \<union> use_vars m\<^sub>x \<union> def_vars m\<^sub>x) = {}"
    using BinaryPattern by blast
  have ihy: "\<Sigma>\<^sub>x \<inter> ({v\<^sub>y} \<union> use_vars m\<^sub>y \<union> def_vars m\<^sub>y) = {}"
    using BinaryPattern lower_finite by presburger
  then have ihy': "(\<Sigma> \<union> {v\<^sub>x} \<union> def_vars m\<^sub>x) \<inter> ({v\<^sub>y} \<union> use_vars m\<^sub>y \<union> def_vars m\<^sub>y) = {}"
    using BinaryPattern lower_sigma_update by presburger
  have seq: "({v'} \<union> use_vars (match v' (BinaryPattern op v\<^sub>x v\<^sub>y) && m\<^sub>x && m\<^sub>y) \<union> def_vars (match v' (BinaryPattern op v\<^sub>x v\<^sub>y) && m\<^sub>x && m\<^sub>y))
    = {v'} \<union> use_vars m\<^sub>x \<union> use_vars m\<^sub>y \<union> {v\<^sub>x, v\<^sub>y} \<union> def_vars m\<^sub>x \<union> def_vars m\<^sub>y"
    by force
  then show ?case using seq ihx ihy' apply simp
    by (smt (verit) BinaryPattern.hyps(1) BinaryPattern.hyps(2) BinaryPattern.hyps(3) BinaryPattern.prems Un_iff disjoint_iff_not_equal freshness lower_finite lower_sigma_update)
next
  case (ConditionalPattern c \<Sigma> m\<^sub>c v\<^sub>c \<Sigma>\<^sub>c t m\<^sub>t v\<^sub>t \<Sigma>\<^sub>t f m\<^sub>f v\<^sub>f \<Sigma>\<^sub>f v')
  have ihc: "\<Sigma> \<inter> ({v\<^sub>c} \<union> use_vars m\<^sub>c \<union> def_vars m\<^sub>c) = {}"
    using ConditionalPattern by auto
  have iht: "\<Sigma>\<^sub>c \<inter> ({v\<^sub>t} \<union> use_vars m\<^sub>t \<union> def_vars m\<^sub>t) = {}"
    using ConditionalPattern lower_finite by blast
  have ihf: "\<Sigma>\<^sub>t \<inter> ({v\<^sub>f} \<union> use_vars m\<^sub>f \<union> def_vars m\<^sub>f) = {}"
    by (meson ConditionalPattern lower_finite)
  have iht': "(\<Sigma> \<union> {v\<^sub>c} \<union> def_vars m\<^sub>c) \<inter> ({v\<^sub>t} \<union> use_vars m\<^sub>t \<union> def_vars m\<^sub>t) = {}"
    using ConditionalPattern iht lower_sigma_update by presburger
  then have ihf': "(\<Sigma> \<union> {v\<^sub>c} \<union> def_vars m\<^sub>c \<union> {v\<^sub>t} \<union> def_vars m\<^sub>t) \<inter> ({v\<^sub>f} \<union> use_vars m\<^sub>f \<union> def_vars m\<^sub>f) = {}"
    using ConditionalPattern ihf lower_sigma_update by presburger
  have seq: "({v'} \<union> use_vars (match v' (ConditionalPattern v\<^sub>c v\<^sub>t v\<^sub>f) && m\<^sub>c && m\<^sub>t && m\<^sub>f) \<union> def_vars (match v' (ConditionalPattern v\<^sub>c v\<^sub>t v\<^sub>f) && m\<^sub>c && m\<^sub>t && m\<^sub>f))
    = {v'} \<union> use_vars m\<^sub>c \<union> use_vars m\<^sub>t \<union> use_vars m\<^sub>f \<union> {v\<^sub>c, v\<^sub>t, v\<^sub>f} \<union> def_vars m\<^sub>c \<union> def_vars m\<^sub>t \<union> def_vars m\<^sub>f"
    by (simp add: Un_assoc)
  then show ?case apply auto
    using ihc apply auto[1] 
    using iht' apply auto[1] 
    using ihf' apply force
    using UnI1 freshness lower_finite lower_sigma_update
    apply (metis ConditionalPattern.hyps(1,2,3,4) ConditionalPattern.prems)
    apply (metis Un_iff disjoint_iff ihc) 
    using iht' mk_disjoint_insert apply fastforce 
    using ihf' mk_disjoint_insert apply fastforce 
    apply (meson Un_iff disjoint_iff ihc) 
    using iht' mk_disjoint_insert apply fastforce
    using ihf' mk_disjoint_insert by fastforce
next
  case (ConstantVariableUnseen vn \<Sigma>)
  then show ?case
    by simp
next
  case (ConstantVariableSeen vn \<Sigma> v')
  then show ?case
    by (simp add: freshness)
next
  case (ParameterPattern v' \<Sigma> nid s)
  then show ?case
    by (simp add: freshness)
next
  case (LeafPattern v' \<Sigma> nid s)
  then show ?case
    by (simp add: freshness)
qed 

lemma lower_valid_matches:
  assumes "finite \<Sigma>"
  assumes "\<forall>v \<Sigma>. v = fresh_var \<Sigma> \<longrightarrow> v \<notin> \<L> e"
  assumes "(e, \<Sigma>) \<leadsto> (m, v, \<Sigma>')"
  shows "valid_match m"
  using assms(3,2,1)
proof (induction rule: lower.induct)
  case (VariableUnseen vn \<Sigma> s)
  then show ?case by simp
next
  case (VariableSeen vn \<Sigma> v' s)
  then show ?case by simp
next
  case (ConstantPattern v' \<Sigma> c)
  then show ?case by simp
next
  case (UnaryPattern x \<Sigma> m\<^sub>x v\<^sub>x \<Sigma>\<^sub>x v' op)
  have "fresh_var \<Sigma>\<^sub>x \<noteq> v\<^sub>x"
    using lower_sigma_update UnaryPattern freshness
    by (metis UnCI insertCI lower_finite)
  have "fresh_var \<Sigma>\<^sub>x \<noteq> v\<^sub>x \<and> fresh_var \<Sigma>\<^sub>x \<notin> def_vars m\<^sub>x"
    by (metis "UnaryPattern.hyps"(1) "UnaryPattern.prems"(2) UnCI \<open>fresh_var \<Sigma>\<^sub>x \<noteq> v\<^sub>x\<close> freshness lower_finite lower_sigma_update)
  then show ?case using UnaryPattern by simp
next
  case (BinaryPattern x \<Sigma> m\<^sub>x v\<^sub>x \<Sigma>\<^sub>x y m\<^sub>y v\<^sub>y \<Sigma>\<^sub>y v' op)
  have vmx: "valid_match m\<^sub>x"
    using BinaryPattern by fastforce
  have vmy: "valid_match m\<^sub>y"
    using BinaryPattern lower_finite
    by (metis UnCI \<L>.simps(5))
  have "fresh_var \<Sigma>\<^sub>y \<noteq> v\<^sub>x" using BinaryPattern
    by (metis UnCI freshness insertCI lower_finite lower_sigma_update)
  also have "fresh_var \<Sigma>\<^sub>y \<noteq> v\<^sub>y" using BinaryPattern
    by (metis UnCI freshness insertCI lower_finite lower_sigma_update)
  moreover have "use_vars m\<^sub>x \<inter> def_vars m\<^sub>y = {}" using BinaryPattern lower_sigma_update2
    by (metis UnCI disjoint_iff_not_equal lower_finite lower_sigma_update1)
  moreover have "v\<^sub>x \<noteq> v\<^sub>y" using BinaryPattern
    by (metis Un_commute Un_insert_right disjoint_insert(2) insertI1 lower_finite lower_sigma_update lower_sigma_update2)
  ultimately have "fresh_var \<Sigma>\<^sub>y \<noteq> v\<^sub>x \<and> fresh_var \<Sigma>\<^sub>y \<noteq> v\<^sub>y \<and> v\<^sub>x \<noteq> v\<^sub>y \<and> use_vars m\<^sub>x \<inter> def_vars m\<^sub>y = {} \<and> fresh_var \<Sigma>\<^sub>y \<notin> def_vars m\<^sub>x \<and> fresh_var \<Sigma>\<^sub>y \<notin> def_vars m\<^sub>y"
    by (metis BinaryPattern.hyps(1,2) BinaryPattern.prems(2) UnCI freshness lower_finite lower_sigma_update)
  then show ?case
    by (simp add: BinaryPattern.hyps(3) vmx vmy)
next
  case (ConditionalPattern c \<Sigma> m\<^sub>c v\<^sub>c \<Sigma>\<^sub>c t m\<^sub>t v\<^sub>t \<Sigma>\<^sub>t f m\<^sub>f v\<^sub>f \<Sigma>\<^sub>f v')
  have vmc: "valid_match m\<^sub>c"
    using ConditionalPattern by force
  have vmt: "valid_match m\<^sub>t"
    using ConditionalPattern lower_finite by auto
  have vmf: "valid_match m\<^sub>f"
    by (metis ConditionalPattern.IH(3) ConditionalPattern.hyps(1,2) ConditionalPattern.prems(1,2) UnI2 \<L>.simps(6) lower_finite)
  have v'ne: "v' \<noteq> v\<^sub>c \<and> v' \<noteq> v\<^sub>t \<and> v' \<noteq> v\<^sub>f"
    by (smt (verit) ConditionalPattern Un_insert_left Un_insert_right freshness insert_iff lower_finite lower_sigma_update)
  have dij: "v\<^sub>c \<noteq> v\<^sub>t \<and> v\<^sub>c \<noteq> v\<^sub>f \<and> v\<^sub>t \<noteq> v\<^sub>f"
    using UnCI Un_insert_left disjoint_insert(2) insertCI lower_finite lower_sigma_update1 lower_sigma_update2
    by (metis ConditionalPattern.hyps(1,2,3) ConditionalPattern.prems(2))
  have cd: "use_vars m\<^sub>c \<inter> (def_vars m\<^sub>t \<union> def_vars m\<^sub>f) = {}"
    using ConditionalPattern lower_sigma_update2
    by (smt (verit, ccfv_threshold) Un_iff disjoint_iff lower_finite lower_sigma_update1)
  have td: "use_vars m\<^sub>t \<inter> def_vars m\<^sub>f = {}"
    using ConditionalPattern lower_sigma_update2
    by (smt (verit, ccfv_SIG) UnCI disjoint_iff lower_finite lower_sigma_update1)
  have "v' \<notin> def_vars m\<^sub>c \<and> v' \<notin> def_vars m\<^sub>t \<and> v' \<notin> def_vars m\<^sub>f"
    using ConditionalPattern
    by (metis UnI1 Un_insert_right freshness insertCI lower_finite lower_sigma_update mk_disjoint_insert)
  then show ?case using vmc vmt vmf v'ne dij cd td
    by simp
next
  case (ConstantVariableUnseen vn \<Sigma>)
  then show ?case
    by simp
next
  case (ConstantVariableSeen vn v' \<Sigma>)
  then show ?case
    by simp
next
  case (ParameterPattern v' \<Sigma> nid s)
  then show ?case
    by simp
next
  case (LeafPattern v' \<Sigma> nid s)
  then show ?case
    by simp
qed


subsection \<open>MATCH Matching Semantics\<close>

inductive unify :: "Subst \<Rightarrow> (VarName \<times> IRExpr) list \<Rightarrow> Subst \<Rightarrow> bool" where
  "unify \<sigma> [] \<sigma>" |
  "\<lbrakk>v \<in> dom \<sigma>; \<sigma> v = Some e; unify \<sigma> xs \<sigma>'\<rbrakk> \<Longrightarrow> unify \<sigma> ((v, e) # xs) \<sigma>'" |
  "\<lbrakk>v \<notin> dom \<sigma>; unify (\<sigma>(v \<mapsto> e)) xs \<sigma>'\<rbrakk> \<Longrightarrow> unify \<sigma> ((v, e) # xs) \<sigma>'"

lemma unify_grows:
  assumes "unify \<sigma> xs \<sigma>'"
  assumes "v \<in> dom \<sigma>"
  shows "\<sigma> v = \<sigma>' v"
  using assms apply (induction \<sigma> xs \<sigma>' rule: unify.induct) apply simp+
  by presburger

lemma unify_preserves:
  assumes "unify \<sigma> xs \<sigma>'"
  assumes "v \<notin> set (map fst xs)"
  shows "\<sigma> v = \<sigma>' v"
  using assms apply (induction \<sigma> xs \<sigma>' rule: unify.induct) by simp+

lemma unify_update:
  assumes "unify \<sigma> xs \<sigma>'"
  shows "\<forall>(v, e) \<in> set xs. \<sigma>' v = Some e"
  using assms apply (induction \<sigma> xs \<sigma>' rule: unify.induct)
  apply simp using unify_grows by fastforce+

inductive eval_match :: "MATCH \<Rightarrow> Subst \<Rightarrow> Subst \<Rightarrow> bool" ("_ \<U> _ = _" 70) where
  UnaryPattern:
  "\<lbrakk>\<sigma> v = Some (UnaryExpr op xe); unify \<sigma> [(x, xe)] \<sigma>'\<rbrakk> \<Longrightarrow> (match v (UnaryPattern op x)) \<U> \<sigma> = \<sigma>'" |
  BinaryPattern:
  "\<lbrakk>\<sigma> v = Some (BinaryExpr op xe ye); unify \<sigma> [(x, xe), (y, ye)] \<sigma>'\<rbrakk> \<Longrightarrow> (match v (BinaryPattern op x y)) \<U> \<sigma> = \<sigma>'" |
  ConditionalPattern:
  "\<lbrakk>\<sigma> v = Some (ConditionalExpr ce te fe); unify \<sigma> [(c, ce), (t, te), (f, fe)] \<sigma>'\<rbrakk> \<Longrightarrow> (match v (ConditionalPattern c t f)) \<U> \<sigma> = \<sigma>'" |
  ConstantPattern:
  "\<sigma> v = Some (ConstantExpr c) \<Longrightarrow> (match v (ConstantPattern c)) \<U> \<sigma> = \<sigma>" |
  ParameterPattern:
  "\<sigma> v = Some (ParameterExpr nid s) \<Longrightarrow> (match v (ParameterPattern nid)) \<U> \<sigma> = \<sigma>" |
  LeafPattern:
  "\<sigma> v = Some (LeafExpr nid s) \<Longrightarrow> (match v (LeafPattern nid)) \<U> \<sigma> = \<sigma>" |
  Equality:
  "v\<^sub>1 \<in> dom \<sigma> \<and> v\<^sub>2 \<in> dom \<sigma> \<and> \<sigma> v\<^sub>1 = \<sigma> v\<^sub>2 \<Longrightarrow> (v\<^sub>1 == v\<^sub>2) \<U> \<sigma> = \<sigma>" |
  AndThen:
  "(m\<^sub>1 \<U> \<sigma> = \<sigma>') \<and> (m\<^sub>2 \<U> \<sigma>' = \<sigma>'') \<Longrightarrow> (m\<^sub>1 && m\<^sub>2) \<U> \<sigma> = \<sigma>''" |
  Noop:
  "v \<in> dom \<sigma> \<Longrightarrow> noop v \<U> \<sigma> = \<sigma>"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as eval_matchC) eval_match .

inductive_cases eval_match_UnaryPattern: "(match v (UnaryPattern op x)) \<U> \<sigma> = \<sigma>'"
inductive_cases eval_match_BinaryPattern: "(match v (BinaryPattern op x y)) \<U> \<sigma> = \<sigma>'"
inductive_cases eval_match_ConditionalExpr: "(match v (ConditionalPattern c t f)) \<U> \<sigma> = \<sigma>'"
inductive_cases eval_match_ConstantExpr: "(match v (ConstantPattern c)) \<U> \<sigma> = \<sigma>'"
inductive_cases eval_match_ParameterExpr: "(match v (ParameterPattern nid)) \<U> \<sigma> = \<sigma>'"
inductive_cases eval_match_LeafExpr: "(match v (LeafPattern nid)) \<U> \<sigma> = \<sigma>'"
inductive_cases eval_match_equality: "(v\<^sub>1 == v\<^sub>2) \<U> \<sigma> = \<sigma>'"
inductive_cases eval_match_andthen: "(m\<^sub>1 && m\<^sub>2) \<U> \<sigma> = \<sigma>'"
inductive_cases eval_match_noop: "noop v \<U> \<sigma> = \<sigma>'"

inductive_cases unify_empty: "unify \<sigma> [] \<sigma>'"
inductive_cases unify_unempty: "unify \<sigma> (x # xs) \<sigma>'"

lemma unify_deterministic:
  assumes "unify \<sigma> xs \<sigma>'"
  assumes "unify \<sigma> xs \<sigma>''"
  shows "\<sigma>' = \<sigma>''"
  using assms apply (induction \<sigma> xs \<sigma>' arbitrary: \<sigma>'' rule: unify.induct)
  using unify.cases apply auto[1]
  by (metis Pair_inject unify_unempty)+

lemma unify_partition:
  assumes "(v, e) \<in> set xs"
  assumes "unify \<sigma> xs \<sigma>'"
  assumes "\<sigma>' \<subseteq>\<^sub>m \<sigma>''"
  assumes "m \<U> \<sigma>'' = \<sigma>'''"
  shows  "\<exists>\<sigma>'. (m \<U> \<sigma>'(v \<mapsto> e) = \<sigma>''')"
proof -
  have "\<sigma>' v = Some e" 
    using assms unify_update by fastforce
  then have "\<sigma>'' v = Some e"
    by (metis assms(3) domI map_le_def)
  then show ?thesis
    by (metis assms(4) fun_upd_triv)
qed

lemma eval_match_deterministic:
  assumes "m \<U> \<sigma> = \<sigma>'"
  assumes "m \<U> \<sigma> = \<sigma>''"
  shows "\<sigma>' = \<sigma>''"
  using assms apply (induction m \<sigma> \<sigma>' arbitrary: \<sigma>'' rule: eval_match.induct)
        apply (metis IRExpr.sel(2) eval_match_UnaryPattern option.sel unify_deterministic)
       apply (metis IRExpr.inject(2) eval_match_BinaryPattern option.inject unify_deterministic)
      apply (metis IRExpr.inject(3) eval_match_ConditionalExpr option.sel unify_deterministic)
  using eval_match_ConstantExpr apply blast
  using eval_match_ParameterExpr apply blast
  using eval_match_LeafExpr apply blast
  using eval_match_equality apply blast
  using eval_match_andthen apply metis
  using eval_match_noop by auto

lemma eval_match_preserves:
  assumes "m \<U> \<sigma> = \<sigma>'"
  shows "\<forall>v. v \<notin> def_vars m \<longrightarrow> \<sigma> v = \<sigma>' v"
  using assms apply (induction m \<sigma> \<sigma>' rule: eval_match.induct)
  using unify_preserves by force+

lemma eval_match_subset:
  assumes "m \<U> \<sigma> = \<sigma>'"
  assumes "valid_match m"
  shows "\<sigma> \<subseteq>\<^sub>m \<sigma>'"
  using assms proof (induction m arbitrary: \<sigma> \<sigma>')
  case (match x1 x2)
  then show ?case proof (cases x2)
    case (UnaryPattern x11 x12)
    then show ?thesis using match apply simp
      by (meson eval_match_UnaryPattern map_le_def unify_grows)
  next
    case (BinaryPattern x21 x22 x23)
    then show ?thesis using match apply simp
      by (meson eval_match_BinaryPattern map_le_def unify_grows)
  next
    case (ConditionalPattern x31 x32 x33)
    then show ?thesis using match apply simp
      by (meson eval_match_ConditionalExpr map_le_def unify_grows)
  next
    case (VariablePattern x4)
    then show ?thesis 
      using match.prems(1)  eval_match.cases by fastforce
  next
    case (ConstantPattern x5)
    then show ?thesis
      by (metis def_vars.simps(1) empty_iff map_le_def match.prems(1) eval_match_preserves pattern_variables.simps(5))
  next
    case (ConstantVarPattern x6)
    then show ?thesis 
      using match.prems(1) eval_match.cases by fastforce
  next
    case (ParameterPattern x7)
    then show ?thesis
      by (metis eval_match_ParameterExpr map_le_refl match.prems(1))
  next
    case (LeafPattern x8)
    then show ?thesis
      by (metis eval_match_LeafExpr map_le_refl match.prems(1))
  qed
next
  case (equality x1 x2)
  then show ?case
    by (metis eval_match_equality map_le_refl)
next
  case (andthen m1 m2)
  then show ?case
    by (meson eval_match_andthen map_le_trans valid_match.simps(4))
next
  case noop
  then show ?case
    by (metis eval_match_noop map_le_refl)
qed


lemma eval_match_adds_patterns:
  assumes "(e, \<Sigma>) \<leadsto> (m, v, \<Sigma>')"
  assumes "valid_match m"
  assumes "m \<U> \<sigma> = \<sigma>'"
  shows "\<L> e \<subseteq> dom \<sigma>'"
  using assms proof (induct arbitrary: v \<Sigma>' \<sigma> \<sigma>' rule: lower.induct)
  case (VariableUnseen vn \<Sigma> s)
  then show ?case
    by (metis \<L>.simps(1) eval_match_noop singletonD subsetI)
next
  case (VariableSeen vn \<Sigma> v' s)
  then show ?case 
    by (metis \<L>.simps(1) eval_match_equality singletonD subsetI)
next
  case (ConstantPattern v' \<Sigma> c)
  then show ?case by simp
next
  case (UnaryPattern x \<Sigma> m\<^sub>x v\<^sub>x \<Sigma>\<^sub>x v' op)
  then show ?case
    by (metis \<L>.simps(4) eval_match_andthen valid_match.simps(4))
next
  case (BinaryPattern x \<Sigma> m\<^sub>x v\<^sub>x \<Sigma>\<^sub>x y m\<^sub>y v\<^sub>y \<Sigma>\<^sub>y v' op)
  obtain \<sigma>\<^sub>m where \<sigma>\<^sub>m: "match v' (BinaryPattern op v\<^sub>x v\<^sub>y) \<U> \<sigma> = \<sigma>\<^sub>m"
    by (meson BinaryPattern.prems eval_match_andthen)
  then obtain \<sigma>\<^sub>x where \<sigma>\<^sub>x: "m\<^sub>x \<U> \<sigma>\<^sub>m = \<sigma>\<^sub>x"
    by (metis BinaryPattern.prems(2) eval_match_andthen eval_match_deterministic)
  then obtain \<sigma>\<^sub>y where \<sigma>\<^sub>y: "m\<^sub>y \<U> \<sigma>\<^sub>x = \<sigma>\<^sub>y"
    by (metis BinaryPattern.prems(2) \<open>match v' (BinaryPattern op v\<^sub>x v\<^sub>y) \<U> \<sigma> = \<sigma>\<^sub>m\<close> eval_match_andthen eval_match_deterministic)
  have xs: "\<L> x \<subseteq> dom \<sigma>\<^sub>x"
    using BinaryPattern.hyps(2) \<sigma>\<^sub>x BinaryPattern.prems(1) by auto
  have ys: "\<L> y \<subseteq> dom \<sigma>\<^sub>y"
    using BinaryPattern.hyps(4) \<sigma>\<^sub>y BinaryPattern.prems(1) by auto
  have "\<L> (BinaryExpr op x y) = \<L> x \<union> \<L> y"
    by simp
  have "dom \<sigma>\<^sub>x \<union> dom \<sigma>\<^sub>y \<subseteq> dom \<sigma>'"
    by (metis BinaryPattern.prems(1,2) \<sigma>\<^sub>m \<sigma>\<^sub>x \<sigma>\<^sub>y dual_order.eq_iff eval_match.intros(8) eval_match_deterministic eval_match_subset map_le_implies_dom_le sup_absorb2 valid_match.simps(4))
  then show ?case
    by (metis Un_subset_iff \<open>\<L> (BinaryExpr op x y) = \<L> x \<union> \<L> y\<close> sup.absorb_iff1 xs ys)
next
  case (ConditionalPattern c \<Sigma> m\<^sub>c v\<^sub>c \<Sigma>\<^sub>c t m\<^sub>t v\<^sub>t \<Sigma>\<^sub>t f m\<^sub>f v\<^sub>f \<Sigma>\<^sub>f v')
  then show ?case sorry
next
  case (ConstantVariableUnseen vn \<Sigma>)
  then show ?case
    by (metis \<L>.simps(2) eval_match_noop singletonD subsetI)
next
  case (ConstantVariableSeen vn \<Sigma> v')
  then show ?case
    by (metis \<L>.simps(2) eval_match_equality singletonD subsetI)
next
  case (ParameterPattern v' \<Sigma> nid s)
  then show ?case by simp
next
  case (LeafPattern v' \<Sigma> nid s)
  then show ?case by simp
qed

lemma restricted_union:
  "(\<sigma> |` x) ++ (\<sigma> |` y) = (\<sigma> |` (x \<union> y))"
  unfolding restrict_map_def map_add_def apply auto
proof - \<comment> \<open>A lovely sledgehammer generated ISAR proof\<close>
  { fix aa :: 'a and aaa :: 'a
    have "aa \<in> y \<and> aaa \<notin> y \<and> aaa \<notin> x \<or> aa \<in> x \<and> aaa \<notin> y \<and> aaa \<notin> x \<or> aa \<in> x \<and> (case if aaa \<in> y then \<sigma> aaa else None of None \<Rightarrow> if aaa \<in> x then \<sigma> aaa else None | Some x \<Rightarrow> Some x) = \<sigma> aaa \<or> aa \<in> y \<and> (case if aaa \<in> y then \<sigma> aaa else None of None \<Rightarrow> if aaa \<in> x then \<sigma> aaa else None | Some x \<Rightarrow> Some x) = \<sigma> aaa \<or> (case if aa \<in> y then \<sigma> aa else None of None \<Rightarrow> if aa \<in> x then \<sigma> aa else None | Some x \<Rightarrow> Some x) = None \<and> aaa \<notin> y \<and> aaa \<notin> x \<or> (case if aa \<in> y then \<sigma> aa else None of None \<Rightarrow> if aa \<in> x then \<sigma> aa else None | Some x \<Rightarrow> Some x) = None \<and> (case if aaa \<in> y then \<sigma> aaa else None of None \<Rightarrow> if aaa \<in> x then \<sigma> aaa else None | Some x \<Rightarrow> Some x) = \<sigma> aaa"
      by (simp add: option.case_eq_if) }
  then show "(\<lambda>a. case if a \<in> y then \<sigma> a else None of None \<Rightarrow> if a \<in> x then \<sigma> a else None | Some x \<Rightarrow> Some x) = (\<lambda>a. if a \<in> x \<or> a \<in> y then \<sigma> a else None)"
    by fastforce
qed

lemma restricted_unchanged:
  assumes "(dom \<sigma>' - dom \<sigma>) \<inter> x = {}"
  assumes "\<sigma> \<subseteq>\<^sub>m \<sigma>'"
  shows "(\<sigma> |` x) = (\<sigma>' |` x)"
  using assms unfolding restrict_map_def map_add_def map_le_def
  by (metis (no_types, opaque_lifting) DiffI disjoint_iff domIff)

subsection \<open>Lowering Sound\<close>

theorem lower_sound:
  assumes "valid_pattern e\<^sub>p"
  assumes "finite \<Sigma>"
  assumes "(e\<^sub>p, \<Sigma>) \<leadsto> (m, v, \<Sigma>')"
  assumes "m \<U> \<sigma>(v \<mapsto> e\<^sub>g) = \<sigma>'"
  shows "match_tree e\<^sub>p e\<^sub>g = Some (\<sigma>'|`(\<L> e\<^sub>p))"
  using assms(3,2,1,4) proof (induct arbitrary: \<sigma> e\<^sub>g \<sigma>' rule: lower.induct)
  case (VariableUnseen vn \<Sigma> s)
  have "\<sigma>' = \<sigma>(vn \<mapsto> e\<^sub>g)"
    using VariableUnseen.prems
    by (meson eval_match_noop)
  then have "(\<sigma>' |` \<L> (VariableExpr vn s)) = (\<sigma> |` \<L> (VariableExpr vn s))(vn \<mapsto> e\<^sub>g)"
    by simp
  then show ?case
    by force
next
  case (VariableSeen vn \<Sigma> v' s)
  have "v' \<noteq> vn"
    using VariableSeen.hyps VariableSeen.prems(2) valid_pattern_preserves_freshness by fastforce
  also have "\<sigma>' = \<sigma>(v' \<mapsto> e\<^sub>g)"
    using VariableSeen.prems(3) calculation(1) 
    using eval_match.simps by blast
  ultimately show ?case
    using VariableSeen.prems(3) eval_match_equality by fastforce
next
  case (ConstantPattern v' \<Sigma> c)
  have "e\<^sub>g = ConstantExpr c"
    by (meson ConstantPattern.prems(3) eval_match_ConstantExpr map_upd_Some_unfold)
  then show ?case
    by simp
next
  case (UnaryPattern x \<Sigma> m\<^sub>x v\<^sub>x \<Sigma>\<^sub>x v' op)
  obtain \<sigma>\<^sub>m where m1: "match v' (UnaryPattern op v\<^sub>x) \<U> \<sigma>(v' \<mapsto> e\<^sub>g) = \<sigma>\<^sub>m"
    by (meson UnaryPattern.prems(3) eval_match_andthen)
  then obtain e\<^sub>x where  e\<^sub>g: "e\<^sub>g = UnaryExpr op e\<^sub>x" using UnaryPattern
    by (meson eval_match_UnaryPattern map_upd_Some_unfold)
  then have "match_tree x e\<^sub>x = Some (\<sigma>' |` \<L> x)"
  proof -
    have u1: "unify (\<sigma>(v' \<mapsto> e\<^sub>g)) [(v\<^sub>x, e\<^sub>x)] \<sigma>\<^sub>m" 
      using UnaryPattern e\<^sub>g
      by (metis IRExpr.sel(2) m1 eval_match_UnaryPattern fun_upd_same option.sel)
    have "m\<^sub>x \<U> \<sigma>\<^sub>m = \<sigma>'"
      by (metis UnaryPattern.prems(3) m1 eval_match_andthen eval_match_deterministic)
    then obtain \<sigma>\<^sub>x where xm: "m\<^sub>x \<U> \<sigma>\<^sub>x(v\<^sub>x \<mapsto> e\<^sub>x) = \<sigma>'"
      using u1 unify_partition
      by (meson list.set_intros(1) map_le_refl)
    then show ?thesis
      using UnaryPattern by fastforce
  qed
  then show ?case
    using e\<^sub>g by auto
next
  case (BinaryPattern x \<Sigma> m\<^sub>x v\<^sub>x \<Sigma>\<^sub>x y m\<^sub>y v\<^sub>y \<Sigma>\<^sub>y v' op)
  obtain \<sigma>\<^sub>m where s1: "match v' (BinaryPattern op v\<^sub>x v\<^sub>y) \<U> \<sigma>(v' \<mapsto> e\<^sub>g) = \<sigma>\<^sub>m"
    by (meson BinaryPattern.prems(3) eval_match_andthen)
  then obtain e\<^sub>x e\<^sub>y where e\<^sub>g: "e\<^sub>g = BinaryExpr op e\<^sub>x e\<^sub>y"
    by (meson eval_match_BinaryPattern map_upd_Some_unfold)
  have u1: "unify (\<sigma>(v' \<mapsto> e\<^sub>g)) [(v\<^sub>x, e\<^sub>x), (v\<^sub>y, e\<^sub>y)] \<sigma>\<^sub>m"
      using e\<^sub>g IRExpr.inject(2) s1 eval_match_BinaryPattern by fastforce
  then obtain \<sigma>\<^sub>x where m1: "m\<^sub>x \<U> \<sigma>\<^sub>m = \<sigma>\<^sub>x"
    by (metis BinaryPattern.prems(3) eval_match_andthen eval_match_deterministic s1)
  then have mx: "\<sigma>\<^sub>m \<subseteq>\<^sub>m \<sigma>\<^sub>x"
    using BinaryPattern.prems(2) eval_match_subset m1 
    by (metis BinaryPattern.hyps(1) BinaryPattern.prems(1) lower_valid_matches valid_pattern.simps(5) valid_pattern_preserves_freshness)
  then have mt1: "match_tree x e\<^sub>x = Some (\<sigma>\<^sub>x |` \<L> x)"
  proof -
    obtain \<sigma>\<^sub>x' where xm: "m\<^sub>x \<U> \<sigma>\<^sub>x'(v\<^sub>x \<mapsto> e\<^sub>x) = \<sigma>\<^sub>x"
      using m1 u1 unify_partition
      by (meson list.set_intros(1) map_le_refl)
    then show ?thesis
      using BinaryPattern by fastforce
  qed
  then have mt2: "match_tree y e\<^sub>y = Some (\<sigma>' |` \<L> y)"
  proof -
    have m2: "m\<^sub>y \<U> \<sigma>\<^sub>x = \<sigma>'"
      by (metis BinaryPattern.prems(3) eval_match_andthen eval_match_deterministic m1 s1)
    then have "\<sigma>\<^sub>m \<subseteq>\<^sub>m \<sigma>\<^sub>x"
      using BinaryPattern.prems(3) eval_match_subset m1
      using mx by fastforce
    then obtain \<sigma>\<^sub>y' where ym: "m\<^sub>y \<U> \<sigma>\<^sub>y'(v\<^sub>y \<mapsto> e\<^sub>y) = \<sigma>'"
      using m1 u1 unify_partition
      by (metis list.set_intros(1) m2 unify_unempty)
    then show ?thesis
      using BinaryPattern
      using lower_finite valid_pattern.simps(5) by blast
  qed
  have comp: "compatible \<sigma>\<^sub>x \<sigma>'" using mx
    using  CodeGenAlt.compatible.elims(3) eval_match_andthen eval_match_deterministic eval_match_subset m1 map_le_def s1 valid_match.simps(4)
    by (metis BinaryPattern.hyps(1,3) BinaryPattern.prems(1,2,3) lower_finite lower_valid_matches valid_pattern.simps(5) valid_pattern_preserves_freshness)
  then have comp': "compatible (\<sigma>\<^sub>x |` \<L> x) (\<sigma>' |` \<L> y)"
    by (metis (full_types) CodeGenAlt.compatible.elims(2) CodeGenAlt.compatible.elims(3) domIff restrict_in restrict_out)
  have "\<sigma>\<^sub>x ++ \<sigma>' = \<sigma>'"
    using mx
    by (metis BinaryPattern.hyps(1,3) BinaryPattern.prems(1,2,3) eval_match_andthen eval_match_deterministic eval_match_subset lower_finite lower_valid_matches m1 map_add_subsumed1 s1 valid_pattern.simps(5) valid_pattern_preserves_freshness)
  have "(dom \<sigma>' - dom \<sigma>\<^sub>x) \<inter> \<L> x = {}" \<comment> \<open>Ian: This is the troublesome case\<close>
    using eval_match_adds_patterns
    by (metis BinaryPattern.hyps(1) BinaryPattern.prems(1,2) DiffD2 disjoint_iff lower_valid_matches m1 subset_eq valid_pattern.simps(5) valid_pattern_preserves_freshness)
  then have "(\<sigma>\<^sub>x |` \<L> x) ++ (\<sigma>' |` \<L> y) = (\<sigma>' |` \<L> x) ++ (\<sigma>' |` \<L> y)"
    by (metis (no_types, lifting) CodeGenAlt.compatible.elims(2) \<open>\<sigma>\<^sub>x ++ \<sigma>' = \<sigma>'\<close> comp map_add_None map_le_def restricted_unchanged)
  then have "(\<sigma>\<^sub>x |` \<L> x) ++ (\<sigma>' |` \<L> y) = (\<sigma>' |` (\<L> x \<union> \<L> y))"
    by (simp add: restricted_union)
  then have "(\<sigma>\<^sub>x |` \<L> x) ++ (\<sigma>' |` \<L> y) = (\<sigma>' |` \<L> (BinaryExpr op x y))"
    by auto
  then have "Some (\<sigma>\<^sub>x |` \<L> x) \<uplus> Some (\<sigma>' |` \<L> y) = Some (\<sigma>' |` \<L> (BinaryExpr op x y))"
    using comp' unfolding substitution_union.simps
    by fastforce
  then show ?case using mt1 mt2 e\<^sub>g
    using match_tree.simps(2) by presburger
next
  case (ConditionalPattern c \<Sigma> m\<^sub>c v\<^sub>c \<Sigma>\<^sub>c t m\<^sub>t v\<^sub>t \<Sigma>\<^sub>t f m\<^sub>f v\<^sub>f \<Sigma>\<^sub>f v')
  then show ?case sorry
next
  case (ConstantVariableUnseen vn \<Sigma>)
  then show ?case sorry
next
  case (ConstantVariableSeen vn \<Sigma> v')
  have "v' \<noteq> vn"
    using ConstantVariableSeen valid_pattern_preserves_freshness
    using freshness by force
  also have "\<sigma>' = \<sigma>(v' \<mapsto> e\<^sub>g)"
    using ConstantVariableSeen calculation(1) 
    using eval_match.simps by blast
  ultimately show ?case
    using ConstantVariableSeen eval_match_equality sorry
next
  case (ParameterPattern v' \<Sigma> nid s)
  then show ?case
    using eval_match_ParameterExpr by fastforce
next
  case (LeafPattern v' \<Sigma> nid s)
  then show ?case
    using eval_match_LeafExpr by fastforce
qed

class substitutable =
  fixes substitute :: "'a \<Rightarrow> (VarName \<Rightarrow> VarName option) \<Rightarrow> 'a" (infix "\<Zhide>" 70)
  assumes identity: "r \<Zhide> Map.empty = r"
  (*TODO: assumes idempotent: "(r \<Zhide> \<sigma>) \<Zhide> \<sigma> = r \<Zhide> \<sigma>"*)

instantiation IRExpr :: substitutable begin
fun substitute_IRExpr :: "IRExpr \<Rightarrow> (VarName \<Rightarrow> VarName option) \<Rightarrow> IRExpr" where
  "UnaryExpr op x \<Zhide> \<sigma> = UnaryExpr op (x \<Zhide> \<sigma>)" |
  "BinaryExpr op x y \<Zhide> \<sigma> = BinaryExpr op (x \<Zhide> \<sigma>) (y \<Zhide> \<sigma>)" |
  "ConditionalExpr c t f \<Zhide> \<sigma> = ConditionalExpr (c \<Zhide> \<sigma>) (t \<Zhide> \<sigma>) (f \<Zhide> \<sigma>)" |
  "VariableExpr vn s \<Zhide> \<sigma> = 
    (case \<sigma> vn of None \<Rightarrow> VariableExpr vn s 
                | Some v' \<Rightarrow> VariableExpr v' s)" |
  "substitute_IRExpr e \<sigma> = e"
instance apply standard
  subgoal for r apply (induction r)
    by simp+
  done
end

class groundable =
  fixes ground :: "'a \<Rightarrow> (VarName \<Rightarrow> IRExpr option) \<Rightarrow> 'a option" (infix "$" 70)
  fixes varset :: "'a \<Rightarrow> VarName set"
  (*assumes grounds: "(e $ \<sigma>) = Some g \<Longrightarrow> varset g = {}"
  assumes idempotent: "(e $ \<sigma>) = Some g \<Longrightarrow> g $ \<sigma>' = Some g"*)
  assumes restricted: "varset e \<subseteq> S \<Longrightarrow> e $ \<sigma> = e $ (\<sigma>|`S)"

definition is_ground :: "'a::groundable \<Rightarrow> bool" where
  "is_ground e = (varset e = {})"

instantiation IRExpr :: groundable begin
fun ground_IRExpr :: "IRExpr \<Rightarrow> (VarName \<Rightarrow> IRExpr option) \<Rightarrow> IRExpr option" where
  "UnaryExpr op x $ \<sigma> = do {
    x' <- x $ \<sigma>;
    Some (UnaryExpr op x')
  }" |
  "BinaryExpr op x y $ \<sigma> = do {
    x' <- x $ \<sigma>;
    y' <- y $ \<sigma>;
    Some (BinaryExpr op x' y')
  }" |
  "(ConditionalExpr c t f) $ \<sigma> = do {
    c' <- c $ \<sigma>;
    t' <- t $ \<sigma>;
    f' <- f $ \<sigma>;
    Some (ConditionalExpr c' t' f')
  }" |
  "(VariableExpr vn s) $ \<sigma> = 
    (case \<sigma> vn of None \<Rightarrow> None
                | Some e \<Rightarrow> Some e)" |
  "ground_IRExpr e \<sigma> = Some e"
definition varset_IRExpr where
  "varset_IRExpr = \<L>"
instance apply standard
  subgoal for e apply (induction e)
    by (simp add: varset_IRExpr_def)+
  done
end

datatype Rules =
  base IRExpr |
  cond MATCH Rules (infixl "?" 52) |
  else Rules Rules (infixl "else" 50) |
  seq Rules Rules (infixl "\<Zsemi>" 49) |
  choice "Rules list"

fun match_entry_var :: "MATCH \<Rightarrow> VarName option" where
  "match_entry_var (match v p) = Some v" |
  "match_entry_var (v1 == v2) = None" |
  "match_entry_var (m1 && m2) = (case match_entry_var m1 of Some v \<Rightarrow> Some v | None \<Rightarrow> match_entry_var m2)" |
  "match_entry_var (noop v) = None"

abbreviation map_filter :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "map_filter f xs \<equiv> map (the \<circ> f) (filter (\<lambda>x. f x \<noteq> None) xs)"

fun entry_var :: "Rules \<Rightarrow> VarName option" where
  "entry_var (m ? r) = (case match_entry_var m of Some v \<Rightarrow> Some v | None \<Rightarrow> entry_var r)" |
  "entry_var (base e) = None" |
  "entry_var (r1 else r2) = (case entry_var r1 of Some v \<Rightarrow> Some v | None \<Rightarrow> entry_var r2)" |
  "entry_var (choice xs) = find (\<lambda>_.True) (map_filter entry_var xs)" |
  "entry_var (r1 \<Zsemi> r2) = (case entry_var r1 of Some v \<Rightarrow> Some v | None \<Rightarrow> entry_var r2)"

inductive eval_rules :: "Rules \<Rightarrow> Subst \<Rightarrow> IRExpr option \<Rightarrow> bool" where
  \<comment> \<open>Evaluate the result\<close>
  "eval_rules (base e) \<sigma> (e $ \<sigma>)" |

  \<comment> \<open>Evaluate a condition\<close>
  "\<lbrakk>m \<U> \<sigma> = \<sigma>';
    eval_rules r \<sigma>' e\<rbrakk>
   \<Longrightarrow> eval_rules (m ? r) \<sigma> e" |

  \<comment> \<open>Evaluate else\<close>
  "\<lbrakk>eval_rules r\<^sub>1 \<sigma> e\<rbrakk>
   \<Longrightarrow> eval_rules (r\<^sub>1 else r2) \<sigma> e" |
  "\<lbrakk> eval_rules r\<^sub>1 \<sigma> None;
    eval_rules r\<^sub>2 \<sigma> e\<rbrakk>
   \<Longrightarrow> eval_rules (r\<^sub>1 else r\<^sub>2) \<sigma> e" |

  \<comment> \<open>Evaluate choice\<close>
  "\<lbrakk>rule \<in> set rules;
    eval_rules rule \<sigma> (Some r)\<rbrakk>
   \<Longrightarrow> eval_rules (choice rules) \<sigma> (Some r)" |
  "\<lbrakk>\<forall> rule \<in> set rules. eval_rules rule \<sigma> None\<rbrakk>
   \<Longrightarrow> eval_rules (choice rules) \<sigma> None" |
  "eval_rules (choice []) \<sigma> None" |

  \<comment> \<open>Evaluate sequential\<close>
  "\<lbrakk>eval_rules r1 \<sigma> (Some e');
    entry_var r2 = Some v;
    eval_rules r2 (\<sigma>(v \<mapsto> e')) r\<rbrakk>
   \<Longrightarrow> eval_rules (r1 \<Zsemi> r2) \<sigma> r" |
  "\<lbrakk>eval_rules r1 \<sigma> (Some e');
    entry_var r2 = None\<rbrakk>
   \<Longrightarrow> eval_rules (r1 \<Zsemi> r2) u None" |
  "\<lbrakk>eval_rules r1 \<sigma> None;
    eval_rules r2 \<sigma> r\<rbrakk>
   \<Longrightarrow> eval_rules (r1 \<Zsemi> r2) \<sigma> r"

inductive_cases baseE: "eval_rules (base e') u e"
inductive_cases condE: "eval_rules (cond m r) u e"
inductive_cases elseE: "eval_rules (r1 else r2) u e"
inductive_cases choiceE: "eval_rules (choice r) u e"
inductive_cases seqE: "eval_rules (r1 \<Zsemi> r2) u e"


inductive generate :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> VarName \<Rightarrow> Rules \<Rightarrow> bool"
  ("'(_, _') \<leadsto> '(_, _')" 70) where
  "(e\<^sub>p, {}) \<leadsto> (m, v, \<Sigma>) \<Longrightarrow> (e\<^sub>p, e\<^sub>r) \<leadsto> (v, m ? base e\<^sub>r)"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool as generateC) generate .

value "Predicate.the (generateC 
    (BinaryExpr BinSub (BinaryExpr BinAdd (VariableExpr STR ''x'' default_stamp) (VariableExpr STR ''y'' default_stamp)) (VariableExpr STR ''x'' default_stamp))
    (VariableExpr STR ''x'' default_stamp))"

definition exec :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> IRExpr \<Rightarrow> IRExpr option" where
  "exec p b e = (case match_tree p e of Some \<sigma> \<Rightarrow> b $ \<sigma> | None \<Rightarrow> None)"

lemma ground_restriction:
  assumes "\<L> e \<subseteq> S"
  shows "e $ \<sigma> = e $ (\<sigma>|`S)"
  using assms
  by (metis restricted varset_IRExpr_def)

theorem generate_sound:
  assumes "(e\<^sub>p, e\<^sub>r) \<leadsto> (v, r)"
  assumes "eval_rules r [v \<mapsto> e\<^sub>g] e"
  assumes "valid_pattern e\<^sub>p"
  assumes "\<L> e\<^sub>r \<subseteq> \<L> e\<^sub>p"
  shows "e = exec e\<^sub>p e\<^sub>r e\<^sub>g"
proof -
  obtain m \<Sigma> where mgen: "(e\<^sub>p, {}) \<leadsto> (m, v, \<Sigma>)"
    using assms(1) generate.simps by blast
  then obtain \<sigma>' where meval: "m \<U> [v \<mapsto> e\<^sub>g] = \<sigma>'"
    by (metis assms(1) assms(2) condE generate.cases lower_deterministic)
  then have "eval_rules (base e\<^sub>r) \<sigma>' e"
    by (smt (z3) Rules.distinct(1) Rules.distinct(11) Rules.distinct(13) Rules.distinct(9) Rules.inject(2) assms(1) assms(2) eval_match_deterministic eval_rules.cases generate.simps lower_deterministic mgen)
  then have e: "e = (e\<^sub>r $ \<sigma>')"
    using eval_rules.simps by blast
  have "valid_match m"
    using mgen assms(3) lower_valid_matches valid_pattern_preserves_freshness by blast
  then have "match_tree e\<^sub>p e\<^sub>g = Some (\<sigma>'|`(\<L> e\<^sub>p))"
    using lower_sound
    using mgen meval assms(3) by blast
  then have "e\<^sub>r $ the (match_tree e\<^sub>p e\<^sub>g) = e\<^sub>r $ \<sigma>'"
    using ground_restriction assms(4)
    by (metis option.sel)
  then show ?thesis using ground_restriction unfolding exec_def using e
    using \<open>match_tree e\<^sub>p e\<^sub>g = Some (\<sigma>' |` \<L> e\<^sub>p)\<close> by auto
qed



section \<open>Meta-optimizations\<close>

locale metaopt =
  fixes opt :: "Rules \<Rightarrow> Rules option"
  fixes size :: "Rules \<Rightarrow> nat"
  assumes sound: "opt r = Some r' \<Longrightarrow> eval_rules r \<sigma> = eval_rules r' \<sigma>"
  assumes terminates: "opt r = Some r' \<Longrightarrow> size r' < size r"
  assumes size_else: "size r1 < size (r1 else r2) \<and> size r2 < size (r1 else r2)"
  assumes size_choice: "\<forall>r \<in> set rules. size r < size (choice rules)"
  assumes size_cond: "size r < size (m ? r)"
  assumes size_base: "size (base e) = size (base e)"
  assumes size_seq: "size r1 < size (r1 \<Zsemi> r2) \<and> size r2 < size (r1 \<Zsemi> r2)"
begin

function apply_meta :: "Rules \<Rightarrow> Rules" where
  "apply_meta m = (case opt m of Some m' \<Rightarrow> apply_meta m' | None \<Rightarrow> 
    (case m of
      (r1 else r2) \<Rightarrow> ((apply_meta r1) else (apply_meta r2)) |
      (choice rules) \<Rightarrow> choice (map (apply_meta) rules) |
      (m ? r) \<Rightarrow> m ? (apply_meta r) |
      (base e) \<Rightarrow> (base e) |
      (r1 \<Zsemi> r2) \<Rightarrow> (apply_meta r1 \<Zsemi> apply_meta r2)
  ))"
  apply pat_completeness+
  by simp+

termination apply_meta apply standard
  apply (relation "measure size")
  apply simp
  using size_cond apply force
  using size_else apply force
  using size_else apply force
  using size_seq apply force
  using size_seq apply force
  using size_choice apply force
  by (simp add: terminates)

theorem apply_meta_sound:
  "eval_rules r \<sigma> = eval_rules (apply_meta r) \<sigma>"
proof (induction r arbitrary: \<sigma> rule: apply_meta.induct)
  case (1 m)
  then show ?case proof (cases "opt m")
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
      have app: "apply_meta m = x21 ? apply_meta r"
        using None cond by fastforce
      have "\<forall>e. eval_rules (x21 ? r) \<sigma> e = eval_rules (x21 ? (apply_meta r)) \<sigma> e"
        using ih condE
        by (smt (verit) "1.IH"(1) None cond eval_rules.simps)
      then show ?thesis 
        using app cond
        by auto
    next
      case (else r1 r2)
      have ih1: "eval_rules r1 \<sigma> = eval_rules (apply_meta r1) \<sigma>"
        using None 1
        using else by blast
      have ih2: "eval_rules r2 \<sigma> = eval_rules (apply_meta r2) \<sigma>"
        using None 1
        using else by blast
      have app: "apply_meta m = (apply_meta r1 else apply_meta r2)"
        using None else by fastforce
      have "\<forall>e. eval_rules (r1 else r2) \<sigma> e = eval_rules (apply_meta r1 else apply_meta r2) \<sigma> e"
        using ih1 ih2 elseE
        by (metis eval_rules.intros(3) eval_rules.intros(4))
      then show ?thesis
        using app else by auto
    next
      case (seq r1 r2)
      have ih1: "eval_rules r1 \<sigma> = eval_rules (apply_meta r1) \<sigma>"
        using None 1
        using seq by blast
      have ih2: "eval_rules r2 \<sigma> = eval_rules (apply_meta r2) \<sigma>"
        using None 1
        using seq by blast
      have app: "apply_meta m = (apply_meta r1 \<Zsemi> apply_meta r2)"
        using None seq by fastforce
      have "\<forall>e. eval_rules (r1 \<Zsemi> r2) \<sigma> e = eval_rules (apply_meta r1 \<Zsemi> apply_meta r2) \<sigma> e"
        using ih1 ih2 seqE eval_rules.intros(8) eval_rules.intros(9) eval_rules.intros(10) sorry (* match_var *)
      then show ?thesis
        using app seq by auto
    next
      case (choice rules)
      have ih: "\<forall>r \<in> set rules. eval_rules r \<sigma> = eval_rules (apply_meta r) \<sigma>"
        using None 1
        using choice by blast
      have app: "apply_meta m = (choice (map apply_meta rules))"
        using None choice by fastforce
      have "\<forall>e. eval_rules (choice rules) \<sigma> e = eval_rules (choice (map apply_meta rules)) \<sigma> e"
        using ih sorry
      then show ?thesis
        using app choice by auto
    qed
  next
    case (Some a)
    then show ?thesis using 1
      using sound by fastforce
  qed
qed

definition run :: "Rules \<Rightarrow> Rules" where
  "run r = apply_meta r"

end

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
  "combined_size (base e) = 0" |
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

setup \<open>Locale_Code.open_block\<close>
interpretation lift_cond : metaopt
  lift_cond
  combined_size
  apply standard
  using lift_cond_sound apply (smt (verit) lift_cond.elims option.distinct(1) option.sel)
  using combined_size_decreases lift_cond.elims apply force
      apply simp
  subgoal for rules apply (induction rules; auto) done
  by simp+
setup \<open>Locale_Code.close_block\<close>

fun run where "run x = lift_cond.apply_meta x"

value "(snd (Predicate.the (generateC 
    (BinaryExpr BinSub (BinaryExpr BinAdd (VariableExpr STR ''x'' default_stamp) (VariableExpr STR ''y'' default_stamp)) (VariableExpr STR ''x'' default_stamp))
    (VariableExpr STR ''x'' default_stamp))))"

value "run (snd (Predicate.the (generateC 
    (BinaryExpr BinSub (BinaryExpr BinAdd (VariableExpr STR ''x'' default_stamp) (VariableExpr STR ''y'' default_stamp)) (VariableExpr STR ''x'' default_stamp))
    (VariableExpr STR ''x'' default_stamp))))"



subsection \<open>Eliminate Noop Operations\<close>

fun elim_noop :: "Rules \<Rightarrow> Rules option" where
  "elim_noop ((noop x) ? r) = Some (r)" |
  "elim_noop _ = None"

lemma elim_noop_sound:
  "eval_rules (noop x ? r) \<sigma> = eval_rules (r) \<sigma>"
proof -
  have "\<forall>e. eval_rules (noop x ? r) \<sigma> e = eval_rules (r) \<sigma> e"
    using condE apply auto[1] 
     apply (smt (verit, ccfv_threshold) eval_match_andthen eval_match_noop eval_rules.intros(2))
    sorry (* doesn't hold due to our little noop = assert situation *)
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


subsection \<open>Combined Meta-optimizations\<close>

fun reduce where "reduce x = (elim_noop.apply_meta o lift_cond.apply_meta) x"

theorem sound:
  "eval_rules r \<sigma> = eval_rules (reduce r) \<sigma>"
  by (metis comp_def elim_noop.metaopt_axioms lift_cond.metaopt_axioms metaopt.apply_meta_sound reduce.elims)


value "reduce (snd (Predicate.the (generateC 
    (BinaryExpr BinSub (BinaryExpr BinAdd (VariableExpr STR ''x'' default_stamp) (VariableExpr STR ''y'' default_stamp)) (VariableExpr STR ''x'' default_stamp))
    (VariableExpr STR ''x'' default_stamp))))"



end