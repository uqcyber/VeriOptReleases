text_raw "\\newpage"
section \<open>Alternative Code Generation\<close>

theory CodeGenAlt
imports
    Semantics.IRTreeEvalThms
    Semantics.TreeToGraphThms
    Fresh.Fresh_String
    "HOL-Library.Monad_Syntax"
    Locale_Code.Locale_Code
    ConditionDSL
begin

hide_const is_ground compatible
declare [[show_types=false]]

subsection \<open>IRExpr Matching Semantics\<close>

type_synonym VarName = "String.literal"

type_synonym Subst = "VarName \<rightharpoonup> IRExpr"

fun compatible :: "Subst \<Rightarrow> Subst \<Rightarrow> bool" where
  "compatible \<sigma>\<^sub>1 \<sigma>\<^sub>2 = (\<forall>x \<in> dom \<sigma>\<^sub>1 \<inter> dom \<sigma>\<^sub>2. \<sigma>\<^sub>1 x = \<sigma>\<^sub>2 x)"

lemma compatible_alt:
  "compatible \<sigma>\<^sub>1 \<sigma>\<^sub>2 = (\<forall>x \<in> dom \<sigma>\<^sub>1. \<sigma>\<^sub>2 x \<noteq> None \<longrightarrow> \<sigma>\<^sub>1 x = \<sigma>\<^sub>2 x)"
  by auto

fun substitution_union :: "Subst option \<Rightarrow> Subst option \<Rightarrow> Subst option" (infix "\<uplus>" 70) where
  "substitution_union s\<^sub>1 s\<^sub>2 = do {
      \<sigma>\<^sub>1 <- s\<^sub>1;
      \<sigma>\<^sub>2 <- s\<^sub>2;
      (if compatible \<sigma>\<^sub>1 \<sigma>\<^sub>2 then Some (\<sigma>\<^sub>1 ++ \<sigma>\<^sub>2) else None)
  }"

lemma substitution_union:
  "(\<exists>\<sigma>'. substitution_union s\<^sub>1 s\<^sub>2 = Some \<sigma>') = (\<exists>\<sigma>\<^sub>1 \<sigma>\<^sub>2. s\<^sub>1 = Some \<sigma>\<^sub>1 \<and> s\<^sub>2 = Some \<sigma>\<^sub>2 \<and> compatible \<sigma>\<^sub>1 \<sigma>\<^sub>2)"
  by (smt (z3) Option.is_none_def bind_eq_Some_conv is_none_code(2) substitution_union.simps)

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
  "match_tree (ConstantVar vn) (ConstantExpr v) = 
      Some ([vn \<mapsto> (ConstantExpr v)])" |
  "match_tree (VariableExpr vn s) e = 
      Some ([vn \<mapsto> e])" |
  "match_tree _ _ = None"

lemma match_tree_UnaryExpr:
  assumes "match_tree (UnaryExpr op x) g = Some \<sigma>"
  shows "\<exists>x'. g = UnaryExpr op x' \<and> match_tree x x' = Some \<sigma>"
  using assms apply (cases g; auto)
  apply (metis is_none_simps(1) is_none_simps(2))
  by (meson option.distinct(1))

lemma match_tree_BinaryExpr:
  assumes "match_tree (BinaryExpr op x y) g = Some \<sigma>"
  shows "\<exists>x' y'. g = BinaryExpr op x' y' \<and> match_tree x x' \<uplus> match_tree y y' = Some \<sigma>"
  using assms apply (cases g; auto)
   apply (metis is_none_simps(1) is_none_simps(2))
  unfolding substitution_union.simps
  by (smt (verit, ccfv_threshold) CodeGenAlt.compatible.simps bind_eq_Some_conv option.distinct(1))

lemma match_tree_BinaryExpr':
  assumes "match_tree (BinaryExpr op x y) g = Some \<sigma>"
  shows "\<exists>x' y' \<sigma>\<^sub>x \<sigma>\<^sub>y. g = BinaryExpr op x' y' \<and> Some \<sigma>\<^sub>x = match_tree x x' \<and> Some \<sigma>\<^sub>y = match_tree y y' \<and> compatible \<sigma>\<^sub>x \<sigma>\<^sub>y \<and> \<sigma>\<^sub>x ++ \<sigma>\<^sub>y = \<sigma>"
  using assms apply (cases g; auto) 
  apply (metis option.simps(3))
  by (smt (verit, best) CodeGenAlt.compatible.simps bind_eq_Some_conv option.distinct(1) option.simps(1) substitution_union.simps)

lemma match_tree_ConditionalExpr:
  assumes "match_tree (ConditionalExpr c t f) g = Some \<sigma>"
  shows "\<exists>c' t' f'. g = ConditionalExpr c' t' f' \<and> match_tree c c' \<uplus> (match_tree t t' \<uplus> match_tree f f') = Some \<sigma>"
  using assms by (cases g; auto)

lemma match_tree_ConditionalExpr':
  assumes "match_tree (ConditionalExpr c t f) g = Some \<sigma>"
  shows "\<exists>c' t' f' \<sigma>\<^sub>c \<sigma>\<^sub>t \<sigma>\<^sub>f. g = ConditionalExpr c' t' f' \<and> Some \<sigma>\<^sub>c = match_tree c c' \<and> Some \<sigma>\<^sub>t = match_tree t t' \<and> Some \<sigma>\<^sub>f = match_tree f f' 
        \<and> compatible \<sigma>\<^sub>c (\<sigma>\<^sub>t ++ \<sigma>\<^sub>f) \<and> compatible \<sigma>\<^sub>t \<sigma>\<^sub>f \<and> \<sigma>\<^sub>c ++ (\<sigma>\<^sub>t ++ \<sigma>\<^sub>f) = \<sigma>"
  using assms
  by (smt (z3) bind_eq_Some_conv match_tree_ConditionalExpr option.distinct(1) option.inject substitution_union.simps)

lemma match_tree_ParameterExpr:
  assumes "match_tree (ParameterExpr nid s) g = Some \<sigma>"
  shows "\<exists>s. g = ParameterExpr nid s"
  using assms apply (cases g; auto)
  by (metis option.distinct(1))

lemma match_tree_LeafExpr:
  assumes "match_tree (LeafExpr nid s) g = Some \<sigma>"
  shows "\<exists>s. g = LeafExpr nid s"
  using assms apply (cases g; auto)
  by (metis option.distinct(1))

lemma match_tree_ConstantExpr:
  assumes "match_tree (ConstantExpr c) g = Some \<sigma>"
  shows "\<exists>s. g = ConstantExpr c"
  using assms apply (cases g; auto)
  by (metis option.distinct(1))

lemma match_tree_ConstantVar:
  assumes "match_tree (ConstantVar v) g = Some \<sigma>"
  shows "\<exists>c. g = ConstantExpr c \<and> \<sigma> v = Some (ConstantExpr c)"
  using assms by (cases g; auto)

fun vars :: "IRExpr \<Rightarrow> VarName set" where
  "vars (VariableExpr vn s) = {vn}" |
  "vars (ConstantVar vn) = {vn}" |
  "vars (ConstantExpr c) = {}" |
  "vars (UnaryExpr op x) = vars x" |
  "vars (BinaryExpr op x y) = vars x \<union> vars y" |
  "vars (ConditionalExpr c t f) = vars c \<union> vars t \<union> vars f" |
  "vars (ParameterExpr nid s) = {}" |
  "vars (LeafExpr nid s) = {}"

class groundable =
  fixes ground :: "'a \<Rightarrow> (VarName \<Rightarrow> IRExpr option) \<Rightarrow> 'a option" (infix "$" 70)
  fixes \<L> :: "'a \<Rightarrow> VarName set"
  (*assumes grounds: "(e $ \<sigma>) = Some g \<Longrightarrow> varset g = {}"
  assumes idempotent: "(e $ \<sigma>) = Some g \<Longrightarrow> g $ \<sigma>' = Some g"*)
  assumes restricted: "\<L> e \<subseteq> S \<Longrightarrow> e $ \<sigma> = e $ (\<sigma>|`S)"

definition is_ground :: "'a::groundable \<Rightarrow> bool" where
  "is_ground e = (\<L> e = {})"

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
  "(ConstantVar vn) $ \<sigma> =
    (case \<sigma> vn of Some (ConstantExpr c) \<Rightarrow> Some (ConstantExpr c)
                | _ \<Rightarrow> None)" |
  "ground_IRExpr e \<sigma> = Some e"
definition \<L>_IRExpr where
  "\<L>_IRExpr = vars"
instance apply standard
  subgoal for e apply (induction e)
    by (simp add: \<L>_IRExpr_def)+
  done
end

(*fun map_option :: "('a \<Rightarrow> 'a option) \<Rightarrow> 'a list \<Rightarrow> ('a list) option" where
  "map_option f [] = Some []" |
  "map_option f (x # xs) = do {
    x' <- f x;
    xs' <- map_option f xs;
    Some (x' # xs')
  }"

definition map_option :: "('a \<Rightarrow> 'a option) \<Rightarrow> 'a list \<Rightarrow> ('a list) option" where
  "map_option f xs = (fold (\<lambda>x y. case y of None \<Rightarrow> None | Some xs' \<Rightarrow> (case f x of None \<Rightarrow> None | Some x' \<Rightarrow> (Some (x' # xs')))) xs (Some []))"
*)

(*definition maybe_list :: "'a option list \<Rightarrow> 'a list option"*)

instantiation Condition :: groundable begin
fun ground_Condition :: "Condition \<Rightarrow> (VarName \<Rightarrow> IRExpr option) \<Rightarrow> Condition option" where
  "Unary op x $ \<sigma> = do {
    x' <- x $ \<sigma>;
    Some (Unary op x')
  }" |
  "Binary op x y $ \<sigma> = do {
    x' <- x $ \<sigma>;
    y' <- y $ \<sigma>;
    Some (Binary op x' y')
  }" |
  "Variable vn $ \<sigma> = do {
    e <- (\<sigma> vn);
    Some (Expr e)
  }" |
  "Combine lhs rhs $ \<sigma> = do {
    lhs' <- lhs $ \<sigma>;
    rhs' <- rhs $ \<sigma>;
    Some (Combine lhs' rhs')
  }" |
  "InstanceOf obj cn $ \<sigma> = do {
    obj' <- obj $ \<sigma>;
    Some (InstanceOf obj' cn)
  }" |
  "Method obj mn ps $ \<sigma> = do {
    obj' <- obj $ \<sigma>;
    ps' <- List.those (map (\<lambda>c. (c $ \<sigma>)) ps);
    Some (Method obj' mn ps')
  }" |
  "ground_Condition e \<sigma> = Some e"

fun varset_Condition where
  "varset_Condition (Unary op x) = varset_Condition x" |
  "varset_Condition (Binary op x y) = varset_Condition x \<union> varset_Condition y" |
  "varset_Condition (Variable vn) = {vn}" |
  "varset_Condition (Combine lhs rhs) = varset_Condition lhs \<union> varset_Condition rhs" |
  "varset_Condition (InstanceOf obj cn) = varset_Condition obj" |
  "varset_Condition (Method obj mn ps) = varset_Condition obj \<union> (\<Union>(set (map varset_Condition ps)))" |
  "varset_Condition e = {}"

definition \<L>_Condition where
  "\<L>_Condition = varset_Condition"

instance apply standard
  subgoal for e apply (induction e) unfolding \<L>_Condition_def
    apply simp+
    by (smt (verit, del_insts) Option.bind_cong UN_subset_iff map_eq_conv)
  done
end

instantiation option :: (groundable)groundable begin
fun ground_option :: "('a::groundable) option \<Rightarrow> (VarName \<Rightarrow> IRExpr option) \<Rightarrow> 'a option option" where
  "Some a $ \<sigma> = Some (a $ \<sigma>)" |
  "None $ \<sigma> = None"

fun \<L>_option where
  "\<L>_option (Some a) = \<L> a" |
  "\<L>_option None = {}"

instance apply standard
  subgoal for e apply (induction e) unfolding \<L>_Condition_def
    apply simp+
    using restricted by blast
  done
end

lemma is_ground_IRExpr:
  "is_ground (e::IRExpr) = (\<L> e = {})"
  by (simp add: is_ground_def \<L>_IRExpr_def)

(*lemma
  "\<L> e \<subseteq> dom \<sigma> \<Longrightarrow> \<exists>e'. e $ \<sigma> = Some e'"
  apply (induction e arbitrary: \<sigma>) 
  apply (metis \<L>.simps(4) bind.bind_lunit ground_IRExpr.simps(1)) 
  apply (metis Un_subset_iff \<L>.simps(5) bind.bind_lunit ground_IRExpr.simps(2)) 
  apply (metis Un_subset_iff \<L>.simps(6) bind.bind_lunit ground_IRExpr.simps(3))
  apply simp+ sorry*)

definition ground_substitution :: "Subst \<Rightarrow> bool" where
  "ground_substitution \<sigma> = (\<forall>v \<in> dom \<sigma>. (\<forall>e. \<sigma> v = Some e \<longrightarrow> is_ground e))"

lemma ground_substitution:
  fixes e :: IRExpr
  assumes "ground_substitution \<sigma>"
  assumes "e $ \<sigma> = Some e'"
  shows "is_ground e'"
  using assms(2,1) apply (induction e arbitrary: e' \<sigma>)  
  apply (smt (verit, best) vars.simps(4) bind_eq_Some_conv ground_IRExpr.simps(1) is_ground_def option.sel \<L>_IRExpr_def)
  apply (smt (z3) Un_empty_right vars.simps(5) bind_eq_Some_conv ground_IRExpr.simps(2) is_ground_def option.sel \<L>_IRExpr_def) 
  apply (smt (z3) Un_empty_right vars.simps(6) bind_eq_Some_conv ground_IRExpr.simps(3) is_ground_def option.sel \<L>_IRExpr_def) 
  using is_ground_IRExpr \<L>_IRExpr_def apply force+
  apply (smt (verit, best) IRExpr.case_eq_if IRExpr.collapse(6) domD domIff ground_IRExpr.simps(5) ground_substitution_def option.case_eq_if option.distinct(1) option.sel)
  by (metis domIff ground_IRExpr.simps(4) ground_substitution_def option.case_eq_if option.collapse option.distinct(1))

definition rewrite :: "IRExpr \<Rightarrow> Condition option \<Rightarrow> IRExpr \<Rightarrow> IRExpr \<Rightarrow> IRExpr option" where
  "rewrite e\<^sub>p c e\<^sub>r e\<^sub>g = (case match_tree e\<^sub>p e\<^sub>g of 
                          Some \<sigma> \<Rightarrow> 
                           (case c of 
                            None \<Rightarrow> e\<^sub>r $ \<sigma> | 
                            Some c' \<Rightarrow> (case c' $ \<sigma> of None \<Rightarrow> None | Some c'' \<Rightarrow> if evalCondition c'' then e\<^sub>r $ \<sigma> else None))
                        | None \<Rightarrow> None)"

subsection \<open>MATCH Datatype\<close>

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
  equality VarName VarName |
  andthen MATCH MATCH |
  condition Condition |
  noop VarName

bundle match_syntax begin

notation equality (infixl "==" 52)
notation andthen (infixr "&&" 50)

end

context
  includes match_syntax
begin

fun pattern_variables :: "PatternExpr \<Rightarrow> String.literal set" where
  "pattern_variables (UnaryPattern op x) = {x}" |
  "pattern_variables (BinaryPattern op x y) = {x, y}" |
  "pattern_variables (ConditionalPattern c t f) = {c, t, f}" |
  "pattern_variables (VariablePattern v) = {v}" |
  "pattern_variables (ConstantPattern v) = {}" |
  "pattern_variables (ConstantVarPattern v) = {v}" |
  "pattern_variables (ParameterPattern nid) = {}" |
  "pattern_variables (LeafPattern nid) = {}"

fun valid_patternx :: "PatternExpr \<Rightarrow> bool" where
  "valid_patternx (BinaryPattern op x y) = (x \<noteq> y)" |
  "valid_patternx (ConditionalPattern c t f) = (c \<noteq> t \<and> c \<noteq> f \<and> t \<noteq> f)" |
  "valid_patternx _ = True"

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
  "valid_match (match v p) = (v \<notin> pattern_variables p \<and> valid_patternx p)" |
  "valid_match (m1 && m2) = (valid_match m1 \<and> valid_match m2 \<and> use_vars m1 \<inter> def_vars m2 = {})" |
  "valid_match _ = True"

(*
fun valid_match :: "MATCH \<Rightarrow> bool" where
  "valid_match (match v (UnaryPattern op x)) = (v \<noteq> x)" |
  "valid_match (match v (BinaryPattern op x y)) = (v \<noteq> x \<and> v \<noteq> y \<and> x \<noteq> y)" |
  "valid_match (match v (ConditionalPattern c t f)) = (v \<noteq> c \<and> v \<noteq> t \<and> v \<noteq> f \<and> c \<noteq> t \<and> c \<noteq> f \<and> t \<noteq> f)" |
  "valid_match (m1 && m2) = (valid_match m1 \<and> valid_match m2 \<and> use_vars m1 \<inter> def_vars m2 = {})" |
  "valid_match _ = True"
*)

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
  using assms \<L>_IRExpr_def apply (induction e) apply auto
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
  "\<lbrakk>vn \<notin> \<Sigma>; v' = fresh_var \<Sigma>\<rbrakk> \<Longrightarrow> (ConstantVar vn, \<Sigma>) \<leadsto> (match v' (ConstantVarPattern vn), v', \<Sigma> \<union> {vn, v'})" | 
  ConstantVariableSeen:
  "\<lbrakk>vn \<in> \<Sigma>; v' = fresh_var \<Sigma>; v'' = fresh_var (\<Sigma> \<union> {v'})\<rbrakk>
   \<Longrightarrow> (ConstantVar vn, \<Sigma>) \<leadsto> (match v' (ConstantVarPattern v'') && v'' == vn, v', \<Sigma> \<union> {v', v''})" |
  (*ConstantVariableUnseen:
  "vn \<notin> \<Sigma> \<Longrightarrow> (ConstantVar vn, \<Sigma>) \<leadsto> (noop vn, vn, \<Sigma> \<union> {vn})" | \<comment> \<open>Note that constant variables are also not properly handled currently.\<close>
  ConstantVariableSeen:
  "vn \<in> \<Sigma> \<and> v' = fresh_var \<Sigma> \<Longrightarrow> (ConstantVar vn, \<Sigma>) \<leadsto> (v' == vn, v', \<Sigma> \<union> {v'})" |*)
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
    apply (metis Un_insert_right lower_ConstantVar sup_bot_right)
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
    using freshness by auto
next
  case (ConstantVariableSeen vn \<Sigma> v')
  then show ?case
    by (metis Int_empty_right Int_insert_right_if0 UnCI Un_insert_right def_vars.simps(1) def_vars.simps(2) def_vars.simps(3) finite_insert freshness pattern_variables.simps(6) sup_bot_right use_vars.simps(1) use_vars.simps(2) use_vars.simps(3))
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
  then show ?case using UnaryPattern \<L>_IRExpr_def by simp
next
  case (BinaryPattern x \<Sigma> m\<^sub>x v\<^sub>x \<Sigma>\<^sub>x y m\<^sub>y v\<^sub>y \<Sigma>\<^sub>y v' op)
  have vmx: "valid_match m\<^sub>x"
    using BinaryPattern \<L>_IRExpr_def by fastforce
  have vmy: "valid_match m\<^sub>y"
    using BinaryPattern lower_finite
    by (metis UnCI \<L>_IRExpr_def vars.simps(5))
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
    using ConditionalPattern \<L>_IRExpr_def by force
  have vmt: "valid_match m\<^sub>t"
    using ConditionalPattern lower_finite \<L>_IRExpr_def by auto
  have vmf: "valid_match m\<^sub>f"
    by (metis ConditionalPattern.IH(3) ConditionalPattern.hyps(1,2) ConditionalPattern.prems(1,2) UnI2 vars.simps(6) \<L>_IRExpr_def lower_finite)
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
    using \<L>_IRExpr_def by simp
next
  case (ConstantVariableSeen vn v' \<Sigma>)
  then show ?case
    by (metis Int_empty_right Int_insert_right_if0 UnI2 def_vars.simps(2) finite.emptyI finite.insertI finite_UnI freshness insertE insert_absorb insert_not_empty pattern_variables.simps(6) use_vars.simps(1) valid_match.simps(1) valid_match.simps(2) valid_match.simps(3) valid_patternx.simps(6))
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
  ConstantVarPattern:
  "\<lbrakk>\<sigma> v = Some (ConstantExpr c); \<sigma> v = \<sigma> v'\<rbrakk> \<Longrightarrow> (match v (ConstantVarPattern v')) \<U> \<sigma> = \<sigma>" |
  ParameterPattern:
  "\<sigma> v = Some (ParameterExpr nid s) \<Longrightarrow> (match v (ParameterPattern nid)) \<U> \<sigma> = \<sigma>" |
  LeafPattern:
  "\<sigma> v = Some (LeafExpr nid s) \<Longrightarrow> (match v (LeafPattern nid)) \<U> \<sigma> = \<sigma>" |
  Equality:
  "v\<^sub>1 \<in> dom \<sigma> \<and> v\<^sub>2 \<in> dom \<sigma> \<and> \<sigma> v\<^sub>1 = \<sigma> v\<^sub>2 \<Longrightarrow> (v\<^sub>1 == v\<^sub>2) \<U> \<sigma> = \<sigma>" |
  AndThen:
  "(m\<^sub>1 \<U> \<sigma> = \<sigma>') \<and> (m\<^sub>2 \<U> \<sigma>' = \<sigma>'') \<Longrightarrow> (m\<^sub>1 && m\<^sub>2) \<U> \<sigma> = \<sigma>''" |
  Noop:
  "v \<in> dom \<sigma> \<Longrightarrow> noop v \<U> \<sigma> = \<sigma>" |
  Condition:
  "\<lbrakk>c $ \<sigma> = Some c' \<and> evalCondition c'\<rbrakk> \<Longrightarrow> condition c \<U> \<sigma> = \<sigma>"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as eval_matchC) eval_match .

inductive_cases eval_match_UnaryPattern: "(match v (UnaryPattern op x)) \<U> \<sigma> = \<sigma>'"
inductive_cases eval_match_BinaryPattern: "(match v (BinaryPattern op x y)) \<U> \<sigma> = \<sigma>'"
inductive_cases eval_match_ConditionalPattern: "(match v (ConditionalPattern c t f)) \<U> \<sigma> = \<sigma>'"
inductive_cases eval_match_ConstantPattern: "(match v (ConstantPattern c)) \<U> \<sigma> = \<sigma>'"
inductive_cases eval_match_ConstantVarPattern: "(match v (ConstantVarPattern c)) \<U> \<sigma> = \<sigma>'"
inductive_cases eval_match_ParameterPattern: "(match v (ParameterPattern nid)) \<U> \<sigma> = \<sigma>'"
inductive_cases eval_match_LeafPattern: "(match v (LeafPattern nid)) \<U> \<sigma> = \<sigma>'"
inductive_cases eval_match_equality: "(v\<^sub>1 == v\<^sub>2) \<U> \<sigma> = \<sigma>'"
inductive_cases eval_match_andthen: "(m\<^sub>1 && m\<^sub>2) \<U> \<sigma> = \<sigma>'"
inductive_cases eval_match_noop: "noop v \<U> \<sigma> = \<sigma>'"
inductive_cases eval_match_condition: "condition c \<U> \<sigma> = \<sigma>'"

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
      apply (metis IRExpr.inject(3) eval_match_ConditionalPattern option.sel unify_deterministic)
  using eval_match_ConstantPattern apply blast
  using eval_match_ConstantVarPattern apply blast
  using eval_match_ParameterPattern apply blast
  using eval_match_LeafPattern apply blast
  using eval_match_equality apply blast
  using eval_match_andthen apply metis
  using eval_match_noop apply auto
  using eval_match_condition by blast

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
      by (meson eval_match_ConditionalPattern map_le_def unify_grows)
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
      by (metis eval_match_ParameterPattern map_le_refl match.prems(1))
  next
    case (LeafPattern x8)
    then show ?thesis
      by (metis eval_match_LeafPattern map_le_refl match.prems(1))
  qed
next
  case (equality x1 x2)
  then show ?case
    by (metis eval_match_equality map_le_refl)
next
  case (andthen m1 m2)
  then show ?case
    by (meson eval_match_andthen map_le_trans valid_match.simps(2))
next
  case noop
  then show ?case
    by (metis eval_match_noop map_le_refl)
next
  case condition
  then show ?case
    by (metis eval_match_condition map_le_refl)
qed

lemma unify_idempotent:
  assumes "unify \<sigma> xs \<sigma>'"
  shows "unify \<sigma>' xs \<sigma>'"
  using assms apply (induction xs arbitrary: \<sigma> \<sigma>') 
  using unify.intros(1) apply simp
  by (smt (verit, del_insts) domI fun_upd_same unify.intros(2) unify_grows unify_unempty)

lemma unify_superset_idempotence:
  assumes "unify \<sigma> xs \<sigma>"
  assumes "\<sigma> \<subseteq>\<^sub>m \<sigma>'"
  shows "unify \<sigma>' xs \<sigma>'"
  using assms apply (induction xs arbitrary: \<sigma> \<sigma>') 
  apply (simp add: unify.intros(1))
  by (smt (verit, best) domIff fun_upd_same map_le_def option.discI unify.intros(2) unify_grows unify_unempty)

lemma ground_condition_subset:
  fixes c :: Condition
  assumes "c $ \<sigma> = Some c'"
  assumes "\<sigma> \<subseteq>\<^sub>m \<sigma>'"
  shows "c $ \<sigma>' = Some c'"
  using assms apply (induction c arbitrary: \<sigma> \<sigma>' c')
  apply (smt (verit, ccfv_threshold) bind_eq_Some_conv ground_Condition.simps(1))
          apply (smt (verit, ccfv_threshold) bind_eq_Some_conv ground_Condition.simps(2))
         apply simp+ 
       apply (metis bind_eq_None_conv domIff map_le_def option.discI) apply simp apply simp
    apply (smt (verit, ccfv_threshold) bind_eq_Some_conv ground_Condition.simps(4))
   apply (smt (verit) bind_eq_None_conv bind_split_asm ground_Condition.simps(5) is_none_code(2))
  using ground_Condition.simps(6) unfolding Option.bind_def sorry

lemma eval_match_superset_idempotence:
  assumes "m \<U> \<sigma> = \<sigma>"
  assumes "\<sigma> \<subseteq>\<^sub>m \<sigma>'"
  assumes "valid_match m"
  shows "m \<U> \<sigma>' = \<sigma>'"
  using assms proof (induction m arbitrary: \<sigma> \<sigma>')
  case (match x1 x2)
  then show ?case proof (cases x2)
    case (UnaryPattern x11 x12)
    then show ?thesis 
      using eval_match_UnaryPattern unify_superset_idempotence
      by (smt (verit, best) domI eval_match.UnaryPattern map_le_def match.prems(1) match.prems(2))
  next
    case (BinaryPattern x21 x22 x23)
    then show ?thesis
      using eval_match_BinaryPattern unify_superset_idempotence
      by (smt (verit, best) domI eval_match.BinaryPattern map_le_def match.prems(1) match.prems(2))
  next
    case (ConditionalPattern x31 x32 x33)
    then show ?thesis
      using eval_match_ConditionalPattern unify_superset_idempotence
      by (smt (verit, best) domI eval_match.ConditionalPattern map_le_def match.prems(1) match.prems(2))
  next
    case (VariablePattern x4)
    then show ?thesis
      by (smt (verit) MATCH.distinct(6) MATCH.distinct(7) MATCH.inject(1) MATCH.simps(7) MATCH.simps(9) PatternExpr.simps(14) PatternExpr.simps(26) PatternExpr.simps(36) PatternExpr.simps(46) PatternExpr.simps(48) PatternExpr.simps(50) PatternExpr.simps(52) eval_match.simps match.prems(1))
  next
    case (ConstantPattern x5)
    then show ?thesis
      using eval_match_ConditionalPattern
      by (metis domI eval_match.ConstantPattern eval_match_ConstantPattern map_le_def match.prems(1) match.prems(2))
  next
    case (ConstantVarPattern x6)
    then show ?thesis
      by (smt (verit) domI eval_match.simps eval_match_ConstantVarPattern map_le_def match.prems(1) match.prems(2))
  next
    case (ParameterPattern x7)
    then show ?thesis
      using eval_match_ParameterPattern match
      by (smt (verit) domI eval_match.simps map_le_def)
  next
    case (LeafPattern x8)
    then show ?thesis
      using eval_match_LeafPattern match
      by (smt (verit) domI eval_match.simps map_le_def)
  qed
next
  case (equality x1 x2)
  from equality show ?case
    by (metis Equality domIff eval_match_equality map_le_def)
next
  case (andthen m1 m2)
  obtain \<sigma>'' where m1eval: "m1 \<U> \<sigma> = \<sigma>''"
    by (meson andthen.prems(1) eval_match_andthen)
  then have m2eval: "m2 \<U> \<sigma>'' = \<sigma>"
    by (metis andthen.prems(1) eval_match_andthen eval_match_deterministic)
  then have "\<sigma>'' \<subseteq>\<^sub>m \<sigma>"
    using andthen.prems(3) eval_match_subset valid_match.simps(2) by blast
  then show ?case
    by (metis AndThen andthen.IH(1) andthen.IH(2) andthen.prems(2) andthen.prems(3) eval_match_subset m1eval m2eval map_le_antisym valid_match.simps(2))
next
  case noop
  then show ?case
    by (metis Noop domIff eval_match_noop map_le_def)
next
  case (condition c)
  then show ?case
    using Condition eval_match_condition ground_condition_subset
    by metis
qed

lemma eval_match_idempotent:
  assumes "m \<U> \<sigma> = \<sigma>'"
  assumes "valid_match m"
  shows "m \<U> \<sigma>' = \<sigma>'"
  using assms proof (induction m arbitrary: \<sigma> \<sigma>')
  case (match v p)
  then show ?case proof (cases p)
    case (UnaryPattern op x)
    then show ?thesis
      using eval_match_UnaryPattern match unify_grows unify_idempotent
      by (smt (verit, ccfv_SIG) domI eval_match.UnaryPattern)
  next
    case (BinaryPattern x21 x22 x23)
    then show ?thesis
      using eval_match_BinaryPattern match unify_grows unify_idempotent
      by (smt (verit, best) domI eval_match.BinaryPattern)
  next
    case (ConditionalPattern x31 x32 x33)
    then show ?thesis
      using eval_match_ConditionalPattern match unify_grows unify_idempotent
      by (smt (verit, ccfv_SIG) domI eval_match.ConditionalPattern)
  next
    case (VariablePattern x4)
    then show ?thesis
      using match unify_grows unify_idempotent
      by (smt (verit) MATCH.distinct(3) domI eval_match.simps)
  next
    case (ConstantPattern x5)
    then show ?thesis
      using eval_match_ConstantPattern match
      by blast
  next
    case (ConstantVarPattern x6)
    then show ?thesis
      by (smt (verit) MATCH.distinct(3) domI eval_match.simps match unify_grows unify_idempotent)
  next
    case (ParameterPattern x7)
    then show ?thesis
      using eval_match_ParameterPattern match
      by blast
  next
    case (LeafPattern x8)
    then show ?thesis
      using eval_match_LeafPattern match by blast
  qed
next
  case (equality x1 x2)
  then show ?case
    using eval_match_equality by blast
next
  case (andthen m1 m2)
  obtain \<sigma>'' where m1eval: "m1 \<U> \<sigma> = \<sigma>''"
    by (meson andthen.prems eval_match_andthen)
  have validm1: "valid_match m1"
    using andthen.prems(2) by auto
  have m1idem: "m1 \<U> \<sigma>'' = \<sigma>''"
    using andthen.IH(1) m1eval validm1 by auto
  have m2eval: "m2 \<U> \<sigma>'' = \<sigma>'"
    by (metis andthen.prems(1) eval_match_andthen eval_match_deterministic m1eval)
  have validm2: "valid_match m2"
    using andthen.prems(2) by auto
  have m2idem: "m2 \<U> \<sigma>' = \<sigma>'"
    using andthen.IH(2) m2eval validm2 by blast
  have "\<sigma>'' \<subseteq>\<^sub>m \<sigma>'"
    using eval_match_subset m2eval validm2 by blast
  then have "m1 \<U> \<sigma>' = \<sigma>'"
    using eval_match_superset_idempotence m1idem validm1 by blast
  then show ?case
    using AndThen m2idem by auto
next
  case noop
  then show ?case
    using eval_match_noop by blast
next
  case condition
  then show ?case
    using eval_match_condition by blast
qed

lemma eval_match_adds_patterns:
  assumes "(e, \<Sigma>) \<leadsto> (m, v, \<Sigma>')"
  assumes "valid_match m"
  assumes "m \<U> \<sigma> = \<sigma>'"
  shows "\<L> e \<subseteq> dom \<sigma>'"
  using assms proof (induct arbitrary: v \<Sigma>' \<sigma> \<sigma>' rule: lower.induct)
  case (VariableUnseen vn \<Sigma> s)
  then show ?case
    by (metis \<L>_IRExpr_def vars.simps(1) eval_match_noop singletonD subsetI)
next
  case (VariableSeen vn \<Sigma> v' s)
  then show ?case 
    by (metis \<L>_IRExpr_def vars.simps(1) eval_match_equality singletonD subsetI)
next
  case (ConstantPattern v' \<Sigma> c)
  then show ?case using \<L>_IRExpr_def by simp
next
  case (UnaryPattern x \<Sigma> m\<^sub>x v\<^sub>x \<Sigma>\<^sub>x v' op)
  then show ?case
    by (metis \<L>_IRExpr_def vars.simps(4) eval_match_andthen valid_match.simps(2))
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
    using \<L>_IRExpr_def by simp
  have "dom \<sigma>\<^sub>x \<union> dom \<sigma>\<^sub>y \<subseteq> dom \<sigma>'"
    by (metis AndThen BinaryPattern.prems(1) BinaryPattern.prems(2) \<sigma>\<^sub>m \<sigma>\<^sub>x \<sigma>\<^sub>y eval_match_deterministic eval_match_subset map_le_implies_dom_le subset_iff_psubset_eq sup_absorb2 valid_match.simps(2))
  then show ?case
    by (metis Un_subset_iff \<open>\<L> (BinaryExpr op x y) = \<L> x \<union> \<L> y\<close> sup.absorb_iff1 xs ys)
next
  case (ConditionalPattern c \<Sigma> m\<^sub>c v\<^sub>c \<Sigma>\<^sub>c t m\<^sub>t v\<^sub>t \<Sigma>\<^sub>t f m\<^sub>f v\<^sub>f \<Sigma>\<^sub>f v')
  obtain \<sigma>\<^sub>m where \<sigma>\<^sub>m: "match v' (ConditionalPattern v\<^sub>c v\<^sub>t v\<^sub>f) \<U> \<sigma> = \<sigma>\<^sub>m"
    by (meson ConditionalPattern.prems eval_match_andthen)
  then obtain \<sigma>\<^sub>c where \<sigma>\<^sub>c: "m\<^sub>c \<U> \<sigma>\<^sub>m = \<sigma>\<^sub>c"
    by (metis ConditionalPattern.prems(2) eval_match_andthen eval_match_deterministic)
  then obtain \<sigma>\<^sub>t where \<sigma>\<^sub>t: "m\<^sub>t \<U> \<sigma>\<^sub>c = \<sigma>\<^sub>t"
    by (metis ConditionalPattern.prems(2) \<sigma>\<^sub>m eval_match_andthen eval_match_deterministic)
  then obtain \<sigma>\<^sub>f where \<sigma>\<^sub>f: "m\<^sub>f \<U> \<sigma>\<^sub>t = \<sigma>\<^sub>f"
    by (metis ConditionalPattern.prems(2) \<sigma>\<^sub>c \<sigma>\<^sub>m eval_match_andthen eval_match_deterministic)
  have cs: "\<L> c \<subseteq> dom \<sigma>\<^sub>c"
    using ConditionalPattern.hyps(2) \<sigma>\<^sub>c ConditionalPattern.prems(1) by auto
  have ts: "\<L> t \<subseteq> dom \<sigma>\<^sub>t"
    using ConditionalPattern.hyps(4) \<sigma>\<^sub>t ConditionalPattern.prems(1) by auto
  have fs: "\<L> f \<subseteq> dom \<sigma>\<^sub>f"
    using ConditionalPattern.hyps(4) \<sigma>\<^sub>f ConditionalPattern.prems(1)
    by (simp add: ConditionalPattern.hyps(6))
  have "\<L> (ConditionalExpr c t f) = \<L> c \<union> \<L> t \<union> \<L> f"
    using \<L>_IRExpr_def by simp
  have "dom \<sigma>\<^sub>c \<union> dom \<sigma>\<^sub>t \<union> dom \<sigma>\<^sub>f \<subseteq> dom \<sigma>'"
    by (metis ConditionalPattern.prems(1) ConditionalPattern.prems(2) Un_absorb1 \<sigma>\<^sub>c \<sigma>\<^sub>f \<sigma>\<^sub>m \<sigma>\<^sub>t eval_match_andthen eval_match_deterministic eval_match_subset map_le_implies_dom_le set_eq_subset valid_match.simps(2))
  then show ?case
    by (metis \<open>\<L> (ConditionalExpr c t f) = \<L> c \<union> \<L> t \<union> \<L> f\<close> cs fs order.trans sup_mono ts)
next
  case (ConstantVariableUnseen vn \<Sigma>)
  then show ?case
    by (metis \<L>_IRExpr_def vars.simps(2) domI eval_match_ConstantVarPattern singletonD subset_iff)
next
  case (ConstantVariableSeen vn \<Sigma> v')
  then show ?case
    by (metis \<L>_IRExpr_def vars.simps(2) eval_match_andthen eval_match_equality singletonD subsetI)
next
  case (ParameterPattern v' \<Sigma> nid s)
  then show ?case using \<L>_IRExpr_def by simp
next
  case (LeafPattern v' \<Sigma> nid s)
  then show ?case using \<L>_IRExpr_def by simp
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
    using \<L>_IRExpr_def by simp
  then show ?case
    using \<L>_IRExpr_def by force
next
  case (VariableSeen vn \<Sigma> v' s)
  have "v' \<noteq> vn"
    using VariableSeen.hyps VariableSeen.prems(2) valid_pattern_preserves_freshness \<L>_IRExpr_def by fastforce
  also have "\<sigma>' = \<sigma>(v' \<mapsto> e\<^sub>g)"
    using VariableSeen.prems(3) calculation(1) 
    using eval_match.simps by blast
  ultimately show ?case
    using VariableSeen.prems(3) eval_match_equality \<L>_IRExpr_def by fastforce
next
  case (ConstantPattern v' \<Sigma> c)
  have "e\<^sub>g = ConstantExpr c"
    by (meson ConstantPattern.prems(3) eval_match_ConstantPattern map_upd_Some_unfold)
  then show ?case
    using \<L>_IRExpr_def by simp
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
    using e\<^sub>g \<L>_IRExpr_def by auto
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
    compatible_alt by (metis BinaryPattern.hyps(1,3) BinaryPattern.prems(1,2,3) lower_finite lower_valid_matches valid_pattern.simps(5) valid_pattern_preserves_freshness)
  then have comp': "compatible (\<sigma>\<^sub>x |` \<L> x) (\<sigma>' |` \<L> y)"
    using compatible_alt by (metis (full_types) domIff restrict_in restrict_out)
  have "\<sigma>\<^sub>x ++ \<sigma>' = \<sigma>'"
    using mx
    by (metis BinaryPattern.hyps(1,3) BinaryPattern.prems(1,2,3) eval_match_andthen eval_match_deterministic eval_match_subset lower_finite lower_valid_matches m1 map_add_subsumed1 s1 valid_pattern.simps(5) valid_pattern_preserves_freshness)
  have "(dom \<sigma>' - dom \<sigma>\<^sub>x) \<inter> \<L> x = {}" \<comment> \<open>Ian: This is the troublesome case\<close>
    using eval_match_adds_patterns
    by (metis BinaryPattern.hyps(1) BinaryPattern.prems(1,2) DiffD2 disjoint_iff lower_valid_matches m1 subset_eq valid_pattern.simps(5) valid_pattern_preserves_freshness)
  then have "(\<sigma>\<^sub>x |` \<L> x) ++ (\<sigma>' |` \<L> y) = (\<sigma>' |` \<L> x) ++ (\<sigma>' |` \<L> y)"
    using compatible_alt by (metis (no_types, lifting) \<open>\<sigma>\<^sub>x ++ \<sigma>' = \<sigma>'\<close> comp map_add_None map_le_def restricted_unchanged)
  then have "(\<sigma>\<^sub>x |` \<L> x) ++ (\<sigma>' |` \<L> y) = (\<sigma>' |` (\<L> x \<union> \<L> y))"
    by (simp add: restricted_union)
  then have "(\<sigma>\<^sub>x |` \<L> x) ++ (\<sigma>' |` \<L> y) = (\<sigma>' |` \<L> (BinaryExpr op x y))"
    using \<L>_IRExpr_def by auto
  then have "Some (\<sigma>\<^sub>x |` \<L> x) \<uplus> Some (\<sigma>' |` \<L> y) = Some (\<sigma>' |` \<L> (BinaryExpr op x y))"
    using comp' unfolding substitution_union.simps
    by fastforce
  then show ?case using mt1 mt2 e\<^sub>g
    using match_tree.simps(2) by presburger
next
  case (ConditionalPattern c \<Sigma> m\<^sub>c v\<^sub>c \<Sigma>\<^sub>c t m\<^sub>t v\<^sub>t \<Sigma>\<^sub>t f m\<^sub>f v\<^sub>f \<Sigma>\<^sub>f v')
  obtain \<sigma>\<^sub>m where s1: "match v' (ConditionalPattern v\<^sub>c v\<^sub>t v\<^sub>f) \<U> \<sigma>(v' \<mapsto> e\<^sub>g) = \<sigma>\<^sub>m"
    by (meson ConditionalPattern.prems(3) eval_match_andthen)
  then obtain e\<^sub>c e\<^sub>t e\<^sub>f where e\<^sub>g: "e\<^sub>g = ConditionalExpr e\<^sub>c e\<^sub>t e\<^sub>f"
    by (meson eval_match_ConditionalPattern map_upd_Some_unfold)
  have u1: "unify (\<sigma>(v' \<mapsto> e\<^sub>g)) [(v\<^sub>c, e\<^sub>c), (v\<^sub>t, e\<^sub>t), (v\<^sub>f, e\<^sub>f)] \<sigma>\<^sub>m"
      using e\<^sub>g IRExpr.inject(2) s1 eval_match_ConditionalPattern by fastforce
  then obtain \<sigma>\<^sub>c where m1: "m\<^sub>c \<U> \<sigma>\<^sub>m = \<sigma>\<^sub>c"
    by (metis ConditionalPattern.prems(3) eval_match_andthen eval_match_deterministic s1)
  then have mx: "\<sigma>\<^sub>m \<subseteq>\<^sub>m \<sigma>\<^sub>c"
    using ConditionalPattern.prems(2) eval_match_subset m1
    by (metis ConditionalPattern.hyps(1) ConditionalPattern.prems(1) lower_valid_matches valid_pattern.simps(6) valid_pattern_preserves_freshness)
  then have mt1: "match_tree c e\<^sub>c = Some (\<sigma>\<^sub>c |` \<L> c)"
  proof -
    obtain \<sigma>\<^sub>c' where xm: "m\<^sub>c \<U> \<sigma>\<^sub>c'(v\<^sub>c \<mapsto> e\<^sub>c) = \<sigma>\<^sub>c"
      using m1 u1 unify_partition
      by (meson list.set_intros(1) map_le_refl)
    then show ?thesis
      using ConditionalPattern by fastforce
  qed
  obtain \<sigma>\<^sub>t where m2: "m\<^sub>t \<U> \<sigma>\<^sub>c = \<sigma>\<^sub>t"
    by (metis ConditionalPattern.prems(3) eval_match_andthen eval_match_deterministic m1 s1)
  then have mxt: "\<sigma>\<^sub>c \<subseteq>\<^sub>m \<sigma>\<^sub>t"
    by (metis ConditionalPattern.hyps(1) ConditionalPattern.hyps(3) ConditionalPattern.prems(1) ConditionalPattern.prems(2) eval_match_subset lower_finite lower_valid_matches valid_pattern.simps(6) valid_pattern_preserves_freshness)
  then have mt2: "match_tree t e\<^sub>t = Some (\<sigma>\<^sub>t |` \<L> t)"
  proof -
    obtain \<sigma>\<^sub>t' where tm: "m\<^sub>t \<U> \<sigma>\<^sub>t'(v\<^sub>t \<mapsto> e\<^sub>t) = \<sigma>\<^sub>t"
      using m1 m2 u1 unify_partition
      by (metis list.set_intros(1) mx unify_unempty)
    then show ?thesis
      using ConditionalPattern
      using lower_finite valid_pattern.simps(6)
      by meson
  qed
  then have mt3: "match_tree f e\<^sub>f = Some (\<sigma>' |` \<L> f)"
  proof -
    have "m\<^sub>f \<U> \<sigma>\<^sub>t = \<sigma>'"
      using m1 m2 u1 unify_partition
      by (metis ConditionalPattern.prems(3) eval_match_andthen eval_match_deterministic s1)
    then obtain \<sigma>\<^sub>f' where fm: "m\<^sub>f \<U> \<sigma>\<^sub>f'(v\<^sub>f \<mapsto> e\<^sub>f) = \<sigma>'"
      using m1 m2 u1 unify_partition
      by (meson list.set_intros(1) list.set_intros(2) map_le_trans mx mxt)
    then show ?thesis
      using ConditionalPattern
      using lower_finite valid_pattern.simps(6)
      by meson
  qed
  then have mxs: "\<sigma>\<^sub>t \<subseteq>\<^sub>m \<sigma>'"
    by (metis ConditionalPattern.hyps(1) ConditionalPattern.hyps(3) ConditionalPattern.hyps(5) ConditionalPattern.prems(1) ConditionalPattern.prems(2) ConditionalPattern.prems(3) eval_match_andthen eval_match_deterministic eval_match_subset lower_finite lower_valid_matches m1 m2 s1 valid_pattern.simps(6) valid_pattern_preserves_freshness)
  have comp: "compatible \<sigma>\<^sub>c \<sigma>'" using mx
    by (metis ConditionalPattern.hyps(1) ConditionalPattern.hyps(3) ConditionalPattern.hyps(5) ConditionalPattern.prems(1) ConditionalPattern.prems(2) ConditionalPattern.prems(3) compatible_alt eval_match_andthen eval_match_deterministic eval_match_subset lower_finite lower_valid_matches m1 map_le_def map_le_trans s1 valid_pattern.simps(6) valid_pattern_preserves_freshness)
  then have compc: "compatible (\<sigma>\<^sub>c |` \<L> c) (\<sigma>\<^sub>t |` \<L> t)"
    by (smt (verit, best) compatible_alt domIff map_le_def mxt restrict_in restrict_out)
  have compt: "compatible (\<sigma>\<^sub>t |` \<L> t) (\<sigma>' |` \<L> f)"
    using comp compatible_alt domIff map_le_def mxt restrict_in restrict_out
    by (smt (verit, best) mxs)
  from comp have comp': "compatible (\<sigma>\<^sub>c |` \<L> c) (\<sigma>' |` \<L> f)"
    using compatible_alt by (metis (full_types) domIff restrict_in restrict_out)
  have "(\<sigma>\<^sub>c ++ \<sigma>\<^sub>t) ++ \<sigma>' = \<sigma>'"
    using mx
    by (metis ConditionalPattern.hyps(1) ConditionalPattern.hyps(3) ConditionalPattern.hyps(5) ConditionalPattern.prems(1) ConditionalPattern.prems(2) ConditionalPattern.prems(3) eval_match_andthen eval_match_deterministic eval_match_subset lower_finite lower_valid_matches m1 m2 map_add_subsumed1 s1 valid_pattern.simps(6) valid_pattern_preserves_freshness)
  have "(dom \<sigma>\<^sub>t - dom \<sigma>\<^sub>c) \<inter> \<L> c= {}" \<comment> \<open>Ian: This is the troublesome case\<close>
    using eval_match_adds_patterns
    by (metis ConditionalPattern.hyps(1) ConditionalPattern.prems(1) ConditionalPattern.prems(2) DiffD2 disjoint_iff in_mono lower_valid_matches m1 valid_pattern.simps(6) valid_pattern_preserves_freshness)
  then have tplus: "(\<sigma>\<^sub>c |` \<L> c) ++ (\<sigma>\<^sub>t |` \<L> t) = (\<sigma>\<^sub>t |` \<L> c) ++ (\<sigma>\<^sub>t |` \<L> t)"
    by (simp add: mxt restricted_unchanged)
  have "(dom \<sigma>' - dom \<sigma>\<^sub>t - dom \<sigma>\<^sub>c) \<inter> \<L> t \<inter> \<L> c= {}" \<comment> \<open>Ian: This is the troublesome case\<close>
    using eval_match_adds_patterns
    using ConditionalPattern.hyps(1) ConditionalPattern.prems(1) ConditionalPattern.prems(2) lower_valid_matches m1 valid_pattern_preserves_freshness by fastforce
  then have tplus: "(\<sigma>\<^sub>c |` \<L> c) ++ (\<sigma>\<^sub>t |` \<L> t) = (\<sigma>' |` \<L> c) ++ (\<sigma>' |` \<L> t)"
    using tplus mxs
    by (smt (verit, ccfv_threshold) ConditionalPattern.hyps(1) ConditionalPattern.hyps(3) ConditionalPattern.prems(1) ConditionalPattern.prems(2) Diff_disjoint disjoint_iff eval_match_adds_patterns in_mono lower_finite lower_valid_matches m1 m2 map_le_trans mxt restricted_unchanged valid_pattern.simps(6) valid_pattern_preserves_freshness)
  then have "(\<sigma>\<^sub>c |` \<L> c) ++ ((\<sigma>\<^sub>t |` \<L> t) ++ (\<sigma>' |` \<L> f)) = ((\<sigma>' |` \<L> c) ++ (\<sigma>' |` \<L> t)) ++ (\<sigma>' |` \<L> f)"
    by simp
  then have uadd: "(\<sigma>\<^sub>c |` \<L> c) ++ ((\<sigma>\<^sub>t |` \<L> t) ++ (\<sigma>' |` \<L> f)) = (\<sigma>' |` (\<L> c \<union> \<L> t \<union> \<L> f))"
    by (simp add: restricted_union)
  then have "(\<sigma>\<^sub>c |` \<L> c) ++ ((\<sigma>\<^sub>t |` \<L> t) ++ (\<sigma>' |` \<L> f)) = (\<sigma>' |` \<L> (ConditionalExpr c t f))"
    using \<L>_IRExpr_def by auto
  then have "Some (\<sigma>\<^sub>c |` \<L> c) \<uplus> (Some (\<sigma>\<^sub>t |` \<L> t) \<uplus> Some (\<sigma>' |` \<L> f)) = Some (\<sigma>' |` \<L> (ConditionalExpr c t f))"
    using compc compt unfolding substitution_union.simps apply simp
    using uadd
    by (metis Int_iff UnE domIff map_add_dom_app_simps(1) map_add_dom_app_simps(3) map_le_def mxs mxt restrict_in restrict_out)
  then show ?case using mt1 mt2 mt3 e\<^sub>g
    using match_tree.simps(3) by presburger
next
  case (ConstantVariableUnseen vn \<Sigma> v')
  obtain c where "e\<^sub>g = ConstantExpr c"
    by (meson ConstantVariableUnseen.prems(3) eval_match_ConstantVarPattern map_upd_Some_unfold)
  then have mt: "match_tree (ConstantVar vn) e\<^sub>g = Some [vn \<mapsto> ConstantExpr c]"
    by auto
  have "\<sigma>' vn = Some (ConstantExpr c)"
    by (metis ConstantVariableUnseen.prems(3) \<open>e\<^sub>g = ConstantExpr c\<close> eval_match_ConstantVarPattern fun_upd_same)
  also have "\<sigma>' |` {vn} = [vn \<mapsto> ConstantExpr c]"
    using calculation by auto
  then show ?case using mt \<L>_IRExpr_def by auto
next
  case (ConstantVariableSeen vn \<Sigma> v' v'')
  obtain c where "e\<^sub>g = ConstantExpr c"
    by (meson ConstantVariableSeen.prems(3) eval_match_ConstantVarPattern eval_match_andthen map_upd_Some_unfold)
  then have mt: "match_tree (ConstantVar vn) e\<^sub>g = Some [vn \<mapsto> ConstantExpr c]"
    by auto
  have "\<sigma>' vn = Some (ConstantExpr c)"
    by (metis ConstantVariableSeen.prems(3) \<open>e\<^sub>g = ConstantExpr c\<close> eval_match_ConstantVarPattern eval_match_andthen eval_match_equality fun_upd_same)
  also have "\<sigma>' |` {vn} = [vn \<mapsto> ConstantExpr c]"
    using calculation by auto
  then show ?case using mt \<L>_IRExpr_def by auto
next
  case (ParameterPattern v' \<Sigma> nid s)
  then show ?case
    using eval_match_ParameterPattern \<L>_IRExpr_def by fastforce
next
  case (LeafPattern v' \<Sigma> nid s)
  then show ?case
    using eval_match_LeafPattern \<L>_IRExpr_def by fastforce
qed

end

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

datatype Rules =
  base IRExpr |
  cond MATCH Rules |
  either Rules Rules |
  seq Rules Rules |
  choice "Rules list"

bundle match_pattern_syntax begin

notation cond (infixl "?" 52)
notation either (infixl "else" 50)
notation seq (infixl "\<Zsemi>" 49)

end

context 
  includes match_syntax match_pattern_syntax
begin

fun valid_rules :: "Rules \<Rightarrow> bool" where
  "valid_rules (m ? r) = (valid_match m \<and> valid_rules r)" |
  "valid_rules (r1 else r2) = (valid_rules r1 \<and> valid_rules r2)" |
  "valid_rules (r1 \<Zsemi> r2) = (valid_rules r1 \<and> valid_rules r2)" |
  "valid_rules (choice rules) = (\<forall>r \<in> set rules. valid_rules r)" |
  "valid_rules _ = True"

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


inductive generate :: "IRExpr \<Rightarrow> Condition option \<Rightarrow> IRExpr \<Rightarrow> VarName \<Rightarrow> Rules \<Rightarrow> bool"
  ("'(_, _, _') \<leadsto> '(_, _')" 70) where
  "(e\<^sub>p, {}) \<leadsto> (m, v, \<Sigma>) \<Longrightarrow> (e\<^sub>p, Some c, e\<^sub>r) \<leadsto> (v, m ? (condition c ? base e\<^sub>r))" |
  "(e\<^sub>p, {}) \<leadsto> (m, v, \<Sigma>) \<Longrightarrow> (e\<^sub>p, None, e\<^sub>r) \<leadsto> (v, m ? base e\<^sub>r)"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool as generateC) generate .

definition generateRule :: "IRExpr \<Rightarrow> Condition option \<Rightarrow> IRExpr \<Rightarrow> (VarName \<times> Rules)" where
  "generateRule p c r = Predicate.the (generateC p c r)"

value "Predicate.the (generateC 
    (BinaryExpr BinSub (BinaryExpr BinAdd (VariableExpr STR ''x'' default_stamp) (VariableExpr STR ''y'' default_stamp)) (VariableExpr STR ''x'' default_stamp))
    None 
    (VariableExpr STR ''x'' default_stamp))"

lemma ground_restriction:
  assumes "\<L> e \<subseteq> S"
  shows "e $ \<sigma> = e $ (\<sigma>|`S)"
  using assms
  by (metis restricted)

theorem generate_sound:
  assumes "(e\<^sub>p, c, e\<^sub>r) \<leadsto> (v, r)"
  assumes "eval_rules r [v \<mapsto> e\<^sub>g] e"
  assumes "valid_pattern e\<^sub>p"
  assumes "\<L> e\<^sub>r \<subseteq> \<L> e\<^sub>p"
  assumes "\<L> c \<subseteq> \<L> e\<^sub>p"
  shows "e = rewrite e\<^sub>p c e\<^sub>r e\<^sub>g"
proof -
  obtain m \<Sigma> where mgen: "(e\<^sub>p, {}) \<leadsto> (m, v, \<Sigma>)"
    using assms(1) generate.simps by blast
  then obtain \<sigma>' where meval: "m \<U> [v \<mapsto> e\<^sub>g] = \<sigma>'"
    by (metis assms(1) assms(2) condE generate.cases lower_deterministic)
  then have "eval_rules (base e\<^sub>r) \<sigma>' e"
    by (smt (verit, ccfv_threshold) assms(1) assms(2) condE eval_match_condition eval_match_deterministic generate.simps lower_deterministic mgen)
  then have e: "e = (e\<^sub>r $ \<sigma>')"
    using eval_rules.simps by blast
  have "valid_match m"
    using mgen assms(3) lower_valid_matches valid_pattern_preserves_freshness by blast
  then have mt: "match_tree e\<^sub>p e\<^sub>g = Some (\<sigma>'|`(\<L> e\<^sub>p))"
    using lower_sound
    using mgen meval assms(3) by blast
  then have mtsimp: "e\<^sub>r $ the (match_tree e\<^sub>p e\<^sub>g) = e\<^sub>r $ \<sigma>'"
    using ground_restriction assms(4)
    by (metis option.sel \<L>_IRExpr_def)
  then show ?thesis proof (cases c)
    case None
    then show ?thesis
      using \<open>e\<^sub>r $ the (match_tree e\<^sub>p e\<^sub>g) = e\<^sub>r $ \<sigma>'\<close> \<open>match_tree e\<^sub>p e\<^sub>g = Some (\<sigma>' |` \<L> e\<^sub>p)\<close> e rewrite_def by auto
  next
    case (Some c)
    obtain c' where "c $ \<sigma>' = Some c'"
      by (metis Some assms(1) assms(2) condE eval_match_condition eval_match_deterministic generate.simps lower_deterministic meval mgen option.distinct(1) option.sel)
    have "evalCondition c'"
      by (metis Some \<open>c $ \<sigma>' = Some c'\<close> assms(1) assms(2) condE eval_match_condition eval_match_deterministic generate.simps lower_deterministic meval mgen option.discI option.sel)
    then show ?thesis unfolding rewrite_def using mt mtsimp
      by (smt (verit, del_insts) Some \<L>_option.simps(1) \<open>c $ \<sigma>' = Some c'\<close> assms(5) e ground_restriction option.sel option.simps(5))
  qed
qed

thm_oracles generate_sound


section \<open>Optimizations\<close>

inductive groundof :: "Subst \<Rightarrow> IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" ("_ \<turnstile> _ \<preceq> _" 60) where
  "\<lbrakk>\<sigma> \<turnstile> x \<preceq> x'\<rbrakk>
    \<Longrightarrow> \<sigma> \<turnstile> (UnaryExpr op x) \<preceq> (UnaryExpr op x')" |
  "\<lbrakk>\<sigma> \<turnstile> x \<preceq> x'; \<sigma> \<turnstile> y \<preceq> y'\<rbrakk>
    \<Longrightarrow> \<sigma> \<turnstile> (BinaryExpr op x y) \<preceq> (BinaryExpr op x' y')" |
  "\<lbrakk>\<sigma> \<turnstile> c \<preceq> c'; \<sigma> \<turnstile> t \<preceq> t'; \<sigma> \<turnstile> f \<preceq> f'\<rbrakk>
    \<Longrightarrow> \<sigma> \<turnstile> (ConditionalExpr c t f) \<preceq> (ConditionalExpr c' t' f')" |
  "\<sigma> \<turnstile> (ParameterExpr i s) \<preceq> (ParameterExpr i s')" |
  "\<sigma> \<turnstile> (LeafExpr nid s) \<preceq> (LeafExpr nid s')" |
  "\<sigma> \<turnstile> (ConstantExpr c) \<preceq> (ConstantExpr c)" |
  "\<lbrakk>\<sigma> vn = Some (ConstantExpr c)\<rbrakk>
    \<Longrightarrow> \<sigma> \<turnstile> (ConstantExpr c) \<preceq> (ConstantVar vn)" |
  "\<lbrakk>\<sigma> vn = Some e\<rbrakk>
    \<Longrightarrow> \<sigma> \<turnstile> e \<preceq> (VariableExpr vn s)"


inductive_cases groundof_UnaryExpr: "\<sigma> \<turnstile> g \<preceq> (UnaryExpr op x)"
inductive_cases groundof_BinaryExpr: "\<sigma> \<turnstile> g \<preceq> (BinaryExpr op x y)"
inductive_cases groundof_ConditionalExpr: "\<sigma> \<turnstile> g \<preceq> (ConditionalExpr c t f)"
inductive_cases groundof_ParameterExpr: "\<sigma> \<turnstile> g \<preceq> (ParameterExpr i s)"
inductive_cases groundof_LeafExpr: "\<sigma> \<turnstile> g \<preceq> (LeafExpr nid s)"
inductive_cases groundof_ConstantExpr: "\<sigma> \<turnstile> g \<preceq> (ConstantExpr c)"
inductive_cases groundof_ConstantVar: "\<sigma> \<turnstile> g \<preceq> (ConstantVar v)"
inductive_cases groundof_VariableExpr: "\<sigma> \<turnstile> g \<preceq> (VariableExpr vn s)"


(*
definition pattern_refinement :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
  "pattern_refinement e\<^sub>1 e\<^sub>2 = (\<forall>\<sigma>. (ground_substitution \<sigma> \<and> (\<forall>var \<in> \<L> e\<^sub>1. (\<exists>e. \<sigma> var = Some e))) 
                                \<longrightarrow> (\<forall>ge\<^sub>1 ge\<^sub>2. ((\<sigma> \<turnstile> ge\<^sub>1 \<preceq> e\<^sub>1) \<and> (\<sigma> \<turnstile> ge\<^sub>2 \<preceq> e\<^sub>2)) \<longrightarrow> ge\<^sub>1 \<le> ge\<^sub>2))"

definition pattern_refinement :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
  "pattern_refinement e\<^sub>1 e\<^sub>2 = (\<forall>\<sigma>. (ground_substitution \<sigma> \<and> \<L> e\<^sub>1 \<subseteq> dom \<sigma>) 
                                \<longrightarrow> (\<forall>ge\<^sub>1 ge\<^sub>2. ((\<sigma> \<turnstile> ge\<^sub>1 \<preceq> e\<^sub>1) \<and> (\<sigma> \<turnstile> ge\<^sub>2 \<preceq> e\<^sub>2)) \<longrightarrow> ge\<^sub>1 \<le> ge\<^sub>2))"
*)
definition pattern_refinement :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
  "pattern_refinement e\<^sub>1 e\<^sub>2 = (\<forall>\<sigma>. \<forall>ge\<^sub>1 ge\<^sub>2. (\<sigma> \<turnstile> ge\<^sub>1 \<preceq> e\<^sub>1) \<and> (\<sigma> \<turnstile> ge\<^sub>2 \<preceq> e\<^sub>2) \<longrightarrow> ge\<^sub>1 \<le> ge\<^sub>2)"

lemma ground_requires_mdom:
  assumes "m \<turnstile> ge1 \<preceq> e1"
  shows "(\<forall>var \<in> \<L> e1. (\<exists>e. m var = Some e))"
  using assms \<L>_IRExpr_def apply (induction rule: groundof.induct) by auto

lemma ground_refinement:
  assumes "pattern_refinement e\<^sub>1 e\<^sub>2"
  assumes "ground_substitution \<sigma>"
  assumes "\<sigma> \<turnstile> ge\<^sub>1 \<preceq> e\<^sub>1"
  assumes "\<sigma> \<turnstile> ge\<^sub>2 \<preceq> e\<^sub>2"
  shows "ge\<^sub>1 \<le> ge\<^sub>2"
proof -
  have "(\<forall>var \<in> \<L> e\<^sub>1. (\<exists>e. \<sigma> var = Some e))"
    using ground_requires_mdom assms(3) by simp
  then have f: "(\<And>ge1 ge2. ((\<sigma> \<turnstile> ge1 \<preceq> e\<^sub>1) \<and> (\<sigma> \<turnstile> ge2 \<preceq> e\<^sub>2)) \<Longrightarrow> ge1 \<le> ge2)"
    using assms(1,2) unfolding pattern_refinement_def by auto
  show ?thesis
    apply (rule f)
    using assms(3,4) by simp
qed

lemma is_ground_UnaryExpr:
  "is_ground (UnaryExpr op x) = is_ground x"
  by (simp add: is_ground_def \<L>_IRExpr_def)

lemma is_ground_BinaryExpr:
  "is_ground (BinaryExpr op x y) = (is_ground x \<and> is_ground y)"
  by (simp add: is_ground_def \<L>_IRExpr_def)

lemma is_ground_ConditionalExpr:
  "is_ground (ConditionalExpr c t f) = (is_ground c \<and> is_ground t \<and> is_ground f)"
  by (simp add: is_ground_def \<L>_IRExpr_def)

lemma ground_substitution_union:
  assumes "ground_substitution \<sigma>\<^sub>1"
  assumes "ground_substitution \<sigma>\<^sub>2"
  shows "ground_substitution (\<sigma>\<^sub>1 ++ \<sigma>\<^sub>2)"
  using assms
  using ground_substitution_def by auto

lemma match_tree_ground:
  assumes "is_ground e\<^sub>g"
  assumes "match_tree e\<^sub>p e\<^sub>g = Some \<sigma>"
  shows "ground_substitution \<sigma>"
  using assms apply (induction e\<^sub>p arbitrary: e\<^sub>g \<sigma>)
  using is_ground_UnaryExpr match_tree_UnaryExpr apply blast
  apply (metis ground_substitution_union is_ground_BinaryExpr match_tree_BinaryExpr')
  apply (smt (verit) ground_substitution_union is_ground_ConditionalExpr match_tree_ConditionalExpr')
  apply (metis domIff ground_substitution_def match_tree.simps(4) match_tree_ParameterExpr option.sel)
  apply (metis domIff ground_substitution_def match_tree.simps(5) match_tree_LeafExpr option.sel)
  apply (metis domIff ground_substitution_def match_tree.simps(6) match_tree_ConstantExpr option.sel)
  apply (smt (verit, ccfv_SIG) domI dom_empty equals0D ground_substitution_def map_upd_Some_unfold match_tree.simps(7) match_tree_ConstantVar option.inject)
  by (metis domI domIff dom_empty dom_fun_upd fun_upd_same ground_substitution_def match_tree.simps(8) option.inject singleton_iff)

lemma ground_groundof:
  assumes "Some g = p $ \<sigma>"
  shows "\<sigma> \<turnstile> g \<preceq> p"
  using assms proof (induction p arbitrary: \<sigma> g)
  case (UnaryExpr op x)
  obtain xg where xg: "Some xg = x $ \<sigma>"
    by (metis UnaryExpr.prems bind_eq_Some_conv ground_IRExpr.simps(1))
  have "g = UnaryExpr op xg"
    by (metis UnaryExpr.prems bind.bind_lunit ground_IRExpr.simps(1) option.sel xg)
  then show ?case
    using UnaryExpr.IH groundof.intros(1) xg by blast
next
  case (BinaryExpr op x y)
  obtain xg where xg: "Some xg = x $ \<sigma>"
    by (metis BinaryExpr.prems bind_eq_Some_conv ground_IRExpr.simps(2))
  obtain yg where yg: "Some yg = y $ \<sigma>"
    by (metis (no_types, lifting) BinaryExpr.prems bind_eq_Some_conv ground_IRExpr.simps(2))
  have "g = BinaryExpr op xg yg"
    by (metis BinaryExpr.prems bind.bind_lunit ground_IRExpr.simps(2) option.sel xg yg)
  then show ?case
    by (meson BinaryExpr.IH(1) BinaryExpr.IH(2) groundof.intros(2) xg yg)
next
  case (ConditionalExpr c t f)
  obtain cg where cg: "Some cg = c $ \<sigma>"
    by (metis (no_types, lifting) ConditionalExpr.prems bind_split ground_IRExpr.simps(3) is_none_code(2) is_none_simps(1))
  obtain tg where tg: "Some tg = t $ \<sigma>"
    by (metis (no_types, lifting) ConditionalExpr.prems bind_eq_None_conv ground_IRExpr.simps(3) option.collapse)
  obtain fg where fg: "Some fg = f $ \<sigma>"
    by (metis (no_types, lifting) ConditionalExpr.prems bind_eq_None_conv ground_IRExpr.simps(3) option.collapse)
  have "g = ConditionalExpr cg tg fg"
    by (metis ConditionalExpr.prems bind.bind_lunit cg fg ground_IRExpr.simps(3) option.inject tg)
  then show ?case
    by (simp add: ConditionalExpr.IH(1) ConditionalExpr.IH(2) ConditionalExpr.IH(3) cg fg groundof.intros(3) tg)
next
  case (ParameterExpr x1 x2)
  then show ?case
    using groundof.intros(4) by force
next
  case (LeafExpr x1 x2)
  then show ?case
    by (simp add: groundof.intros(5))
next
  case (ConstantExpr x)
  then show ?case
    using groundof.intros(6) by force
next
  case (ConstantVar x)
  obtain c where "\<sigma> x = Some (ConstantExpr c)"
    by (smt (verit, ccfv_threshold) ConstantVar IRExpr.case_eq_if IRExpr.collapse(6) ground_IRExpr.simps(5) option.case_eq_if option.collapse option.distinct(1))  
  then show ?case
    using groundof.intros(7) ground_IRExpr.simps(5)
    using ConstantVar by auto
next
  case (VariableExpr x1 x2)
  then show ?case
    by (simp add: groundof.intros(8) option.split_sel)
qed

(*
lemma
  "(\<sigma> \<turnstile> g \<preceq> p) = (p $ \<sigma> = Some g)"
  apply (induction p arbitrary: \<sigma> g)
  apply (metis (no_types, lifting) bind.bind_lunit ground_IRExpr.simps(1) ground_groundof groundof_UnaryExpr) 
  apply (smt (verit, best) bind.bind_lunit ground_IRExpr.simps(2) ground_groundof groundof_BinaryExpr) 
  apply (smt (verit, del_insts) bind.bind_lunit ground_IRExpr.simps(3) ground_groundof groundof_ConditionalExpr) sorry
*)

lemma compatible_add:
  assumes "compatible \<sigma> \<sigma>'"
  shows "compatible \<sigma> (\<sigma> ++ \<sigma>')"
  using assms compatible_alt unfolding compatible.simps
  by (metis map_add_dom_app_simps(1) map_add_dom_app_simps(3))

lemma compatible_map_add_assoc:
  assumes "compatible \<sigma> \<sigma>'"
  shows "\<sigma> ++ \<sigma>' = \<sigma>' ++ \<sigma>"
  using assms compatible_alt unfolding compatible.simps
  by (smt (verit, ccfv_threshold) domIff map_add_dom_app_simps(1) map_add_dom_app_simps(3) map_le_def map_le_iff_map_add_commute)

lemma groundof_add_lhs:
  assumes "compatible \<sigma> \<sigma>'"
  assumes "\<sigma> \<turnstile> e \<preceq> e'"
  assumes "\<sigma>'' = \<sigma> ++ \<sigma>'"
  shows "\<sigma>'' \<turnstile> e \<preceq> e'"
  using assms apply (induction e' arbitrary: \<sigma> \<sigma>' e)
  apply (metis groundof.intros(1) groundof_UnaryExpr)
  apply (metis groundof.intros(2) groundof_BinaryExpr)
  apply (metis groundof.intros(3) groundof_ConditionalExpr)
  apply (metis groundof.intros(4) groundof_ParameterExpr) 
  apply (metis groundof.intros(5) groundof_LeafExpr)
  apply (metis groundof.intros(6) groundof_ConstantExpr)
   apply (metis (no_types, opaque_lifting) compatible_alt domI groundof.intros(7) groundof_ConstantVar map_add_Some_iff)
  by (metis (mono_tags, lifting) compatible_alt domI groundof.intros(8) groundof_VariableExpr map_add_Some_iff)

lemma groundof_add_rhs:
  assumes "compatible \<sigma> \<sigma>'"
  assumes "\<sigma>' \<turnstile> e \<preceq> e'"
  assumes "\<sigma>'' = \<sigma> ++ \<sigma>'"
  shows "\<sigma>'' \<turnstile> e \<preceq> e'"
  using groundof_add_lhs compatible_map_add_assoc
  by (metis compatible_alt assms(1) assms(2) assms(3) domIff)

lemma match_tree_groundof:
  assumes "match_tree p g = Some \<sigma>"
  shows "\<sigma> \<turnstile> g \<preceq> p"
  using assms apply (induction p arbitrary: g \<sigma>)
  using groundof.intros(1) match_tree_UnaryExpr apply blast
  using groundof.intros(2) match_tree_BinaryExpr'
  using groundof_add_lhs groundof_add_rhs apply metis
  using groundof.intros(3) match_tree_ConditionalExpr'
  apply (smt (verit, ccfv_threshold) groundof_add_lhs groundof_add_rhs)
  using groundof.intros(4) match_tree_ParameterExpr apply blast 
  using groundof.intros(5) match_tree_LeafExpr apply blast
  apply (metis groundof.intros(6) match_tree_ConstantExpr)
  apply (metis groundof.intros(7) match_tree_ConstantVar)
  by (simp add: groundof.intros(8))


theorem sound_exec:
  assumes "pattern_refinement e\<^sub>r e\<^sub>p"
  assumes "is_ground e\<^sub>g"
  assumes "Some e' = rewrite e\<^sub>p c e\<^sub>r e\<^sub>g"
  shows "e' \<le> e\<^sub>g"
proof -
  obtain \<sigma> where m: "match_tree e\<^sub>p e\<^sub>g = Some \<sigma>"
    using assms(3) rewrite_def by fastforce
  then have "ground_substitution \<sigma>"
    using assms(2) match_tree_ground by auto
  then have g1: "\<sigma> \<turnstile> e' \<preceq> e\<^sub>r"
    by (smt (verit, best) assms(3) ground_groundof m option.case_eq_if option.simps(3) option.simps(5) rewrite_def)
  then have g2: "\<sigma> \<turnstile> e\<^sub>g \<preceq> e\<^sub>p"
    using m match_tree_groundof by presburger
  then show ?thesis using ground_refinement
    using \<open>ground_substitution \<sigma>\<close> assms(1) g1 by blast
qed

thm_oracles sound_exec

(*
theorem sound_conditional_exec:
  assumes "evalCondition c \<Longrightarrow> pattern_refinement e\<^sub>r e\<^sub>p"
  assumes "is_ground e\<^sub>g"
  assumes "Some e' = rewrite e\<^sub>p (Some c) e\<^sub>r e\<^sub>g"
  shows "evalCondition c \<Longrightarrow> e' \<le> e\<^sub>g"
proof -
  obtain \<sigma> where m: "match_tree e\<^sub>p e\<^sub>g = Some \<sigma>"
    using assms(3) rewrite_def by fastforce
  then have "ground_substitution \<sigma>"
    using assms(2) match_tree_ground by auto
  then have g1: "\<sigma> \<turnstile> e' \<preceq> e\<^sub>r"
    by (smt (verit, best) assms(3) ground_groundof m option.case_eq_if option.simps(3) option.simps(5) rewrite_def)
  then have g2: "\<sigma> \<turnstile> e\<^sub>g \<preceq> e\<^sub>p"
    using m match_tree_groundof by presburger
  then show ?thesis using ground_refinement
    using \<open>ground_substitution \<sigma>\<close> assms(1) g1 sorry
qed
*)


theorem sound_rules:
  assumes "pattern_refinement e\<^sub>r e\<^sub>p"
  assumes "(e\<^sub>p, c, e\<^sub>r) \<leadsto> (v, r)"
  assumes "eval_rules r [v \<mapsto> e\<^sub>g] (Some e')"
  assumes "valid_pattern e\<^sub>p"
  assumes "\<L> e\<^sub>r \<subseteq> \<L> e\<^sub>p"
  assumes "\<L> c \<subseteq> \<L> e\<^sub>p"
  assumes "is_ground e\<^sub>g"
  shows "e' \<le> e\<^sub>g"
  using assms
  using generate_sound sound_exec by blast

thm_oracles sound_rules

lemma det_variable_match:
  assumes "(e\<^sub>p, {}) \<leadsto> (m, v, \<Sigma>)"
  assumes "m \<U> [v' \<mapsto> e\<^sub>g] = \<sigma>'"
  shows "v = v'"
  using assms(2,1) apply (induction m arbitrary: e\<^sub>g e\<^sub>p \<Sigma> \<sigma>' v v')
  apply (smt (verit) MATCH.distinct(7) MATCH.inject(1) MATCH.simps(10) MATCH.simps(6) MATCH.simps(8) eval_match.cases fun_upd_apply lower.cases option.distinct(1))
     apply (smt (verit) MATCH.distinct(13) MATCH.distinct(9) MATCH.simps(6) empty_iff lower.cases)
  apply (smt (verit) MATCH.distinct(7) MATCH.inject(1) MATCH.inject(3) MATCH.simps(10) MATCH.simps(6) MATCH.simps(8) domI dom_empty dom_fun_upd empty_iff eval_match.cases eval_match_andthen eval_match_noop lower.cases singletonD)
    apply (smt (verit) MATCH.simps(10) MATCH.simps(21) MATCH.simps(25) empty_iff lower.cases)
  by (smt (verit) MATCH.distinct(17) MATCH.distinct(7) dom_empty dom_fun_upd empty_iff eval_match_noop lower.cases option.distinct(1) singleton_iff)

lemma det_variable_rules:
  assumes "(e\<^sub>p, c, e\<^sub>r) \<leadsto> (v, r)"
  assumes "eval_rules r [v' \<mapsto> e\<^sub>g] (Some e')"
  shows "v = v'"
  using assms det_variable_match
  by (smt (verit) Rules.distinct(1) Rules.distinct(11) Rules.distinct(13) Rules.distinct(9) Rules.inject(2) eval_rules.simps generate.simps)

lemma lift_choice:
  assumes "\<forall> r \<in> set rules. \<exists>e\<^sub>r c e\<^sub>p v. pattern_refinement e\<^sub>r e\<^sub>p \<and> (e\<^sub>p, c, e\<^sub>r) \<leadsto> (v, r) \<and> valid_pattern e\<^sub>p \<and> \<L> e\<^sub>r \<subseteq> \<L> e\<^sub>p \<and> \<L> c \<subseteq> \<L> e\<^sub>p"
  assumes "eval_rules (choice rules) [v \<mapsto> e\<^sub>g] (Some e')"
  assumes "is_ground e\<^sub>g"
  shows "e' \<le> e\<^sub>g"
  using assms using det_variable_rules
  by (metis (no_types, lifting) choiceE option.distinct(1) sound_rules)

lemma lift_else:
  assumes "\<exists>e\<^sub>r c e\<^sub>p v. pattern_refinement e\<^sub>r e\<^sub>p \<and> valid_pattern e\<^sub>p \<and> \<L> e\<^sub>r \<subseteq> \<L> e\<^sub>p \<and> \<L> c \<subseteq> \<L> e\<^sub>p \<and> (e\<^sub>p, c, e\<^sub>r) \<leadsto> (v, r1)"
  assumes "\<exists>e\<^sub>r c e\<^sub>p v. pattern_refinement e\<^sub>r e\<^sub>p \<and> valid_pattern e\<^sub>p \<and> \<L> e\<^sub>r \<subseteq> \<L> e\<^sub>p \<and> \<L> c \<subseteq> \<L> e\<^sub>p \<and> (e\<^sub>p, c, e\<^sub>r) \<leadsto> (v, r2)"
  assumes "eval_rules (r1 else r2) [v \<mapsto> e\<^sub>g] (Some e')"
  assumes "is_ground e\<^sub>g"
  shows "e' \<le> e\<^sub>g"
  using assms using det_variable_rules
  by (metis elseE sound_rules)

thm_oracles lift_choice

lemma inductive_choice:
  assumes "\<forall>a \<in> set rules. eval_rules a \<sigma> = eval_rules (f a) \<sigma>"
  shows "\<forall>e. eval_rules (choice rules) \<sigma> e = eval_rules (choice (map f rules)) \<sigma> e"
proof (rule allI; rule iffI)
  fix e
  assume A1: "eval_rules (choice rules) \<sigma> e"
  show "eval_rules (choice (map f rules)) \<sigma> e"
  proof (cases e)
    case None
    then show ?thesis
      apply (cases rules)
      apply (simp add: eval_rules.intros(7))
      by (smt (verit, ccfv_SIG) A1 assms choiceE eval_rules.intros(6) imageE list.distinct(1) list.set_map option.distinct(1))
  next
    case (Some a)
    then obtain rule where "rule \<in> set rules \<and> eval_rules rule \<sigma> (Some a)"
      by (metis A1 choiceE option.discI)
    then have "eval_rules (f rule) \<sigma> (Some a)"
      using assms by fastforce
    also have "f rule \<in> set (map f rules)"
      by (simp add: \<open>rule \<in> set rules \<and> eval_rules rule \<sigma> (Some a)\<close>)
    then have "eval_rules (choice (map f rules)) \<sigma> (Some a)"
      using calculation eval_rules.intros(5) by blast
    then show ?thesis using Some by simp
  qed
next
  fix e
  assume A1: "eval_rules (choice (map f rules)) \<sigma> e"
  show "eval_rules (choice rules) \<sigma> e"
  proof (cases e)
    case None
    have "\<forall>rule \<in> set (map f rules). eval_rules rule \<sigma> None"
      by (metis A1 None choiceE empty_iff list.set(1) option.distinct(1))
    then have "\<forall>rule \<in> set rules. eval_rules rule \<sigma> None"
      by (simp add: assms)
    then show ?thesis
      using eval_rules.intros(7)
      using None eval_rules.intros(6) by blast
  next
    case (Some a)
    then obtain rule where ruled: "rule \<in> set rules \<and> eval_rules (f rule) \<sigma> (Some a)"
      by (smt (verit, del_insts) A1 choiceE imageE image_set option.simps(3))
    then have "eval_rules rule \<sigma> (Some a)"
      using assms by simp
    then have "eval_rules (choice rules) \<sigma> (Some a)"
      using eval_rules.intros(5)
      using ruled by blast
    then show ?thesis using Some by simp
  qed
qed

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
  assumes size_base: "size (base e) = size (base e)"
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
      (base e) \<Rightarrow> (base e) |
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

value "(snd (Predicate.the (generateC 
    (BinaryExpr BinSub (BinaryExpr BinAdd (VariableExpr STR ''x'' default_stamp) (VariableExpr STR ''y'' default_stamp)) (VariableExpr STR ''x'' default_stamp))
    None
    (VariableExpr STR ''x'' default_stamp))))"

value "run (snd (Predicate.the (generateC 
    (BinaryExpr BinSub (BinaryExpr BinAdd (VariableExpr STR ''x'' default_stamp) (VariableExpr STR ''y'' default_stamp)) (VariableExpr STR ''x'' default_stamp))
    None
    (VariableExpr STR ''x'' default_stamp))))"



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

value "reduce (snd (Predicate.the (generateC 
    (BinaryExpr BinSub (BinaryExpr BinAdd (VariableExpr STR ''x'' default_stamp) (VariableExpr STR ''y'' default_stamp)) (VariableExpr STR ''x'' default_stamp))
    None
    (VariableExpr STR ''x'' default_stamp))))"


text \<open>Identity\<close>
value "Predicate.the (generateC 
  (BinaryExpr BinMul (VariableExpr STR ''x'' default_stamp) (ConstantExpr (IntVal 32 1)))
  None
  (VariableExpr STR ''x'' default_stamp))"

text \<open>Eval\<close>
value "Predicate.the (generateC 
  (BinaryExpr BinMul (ConstantVar STR ''x'') (ConstantVar STR ''y''))
  None
  (ConstantExpr (IntVal 32 1)))"

text \<open>Left Shift\<close> \<comment> \<open>TODO: if lhs != const\<close>
value "Predicate.the (generateC 
  (BinaryExpr BinMul (VariableExpr STR ''x'' default_stamp) (ConstantVar STR ''y''))
  (Some (Unary UnaryLogicNegation (Variable STR ''x'' instanceof ConstantExpr)))
  (BinaryExpr BinMul (ConstantVar STR ''y'') (VariableExpr STR ''x'' default_stamp)))"

(*
lemma groundof_det:
  assumes "\<sigma> \<turnstile> g \<preceq> p"
  assumes "\<sigma> \<turnstile> g' \<preceq> p"
  shows "g = g'"
  using assms proof (induction arbitrary: g' rule: groundof.induct)
  case (1 \<sigma> x x' op)
  then show ?case unfolding equiv_exprs_def
    by (smt (verit, best) groundof_UnaryExpr unfold_unary)
next
  case (2 \<sigma> x x' y y' op)
  then show ?case unfolding equiv_exprs_def
    by (smt (verit, best) groundof_BinaryExpr unfold_binary)
next
  case (3 \<sigma> c c' t t' f f')
  then show ?case unfolding equiv_exprs_def 
    using groundof_ConditionalExpr
    by (metis evaltree_not_undef)
next
  case (4 \<sigma> i s s')
  then show ?case sorry
next
  case (5 \<sigma> nid s s')
  then show ?case sorry
next
  case (6 \<sigma> c)
  then show ?case sorry
next
  case (7 \<sigma> vn c)
  then show ?case sorry
next
  case (8 \<sigma> vn e s)
  then show ?case sorry
qed

lemma lift_mul:
  assumes "\<forall>x. x \<le> (BinaryExpr BinMul x (ConstantExpr (IntVal 32 1)))"
  shows "pattern_refinement (VariableExpr STR ''x'' default_stamp) (BinaryExpr BinMul (VariableExpr STR ''x'' default_stamp) (ConstantExpr (IntVal 32 1)))"
  unfolding pattern_refinement_def
  using assms groundof_BinaryExpr groundof_ConstantExpr groundof_det
  by metis
*)

context includes match_syntax match_pattern_syntax
begin
value "(match STR ''X'' (BinaryPattern BinMul STR ''x'' STR ''Xa'') && match STR ''Xa'' (ConstantPattern (IntVal 32 1)))
         ? base (VariableExpr STR ''x'' default_stamp)"

value "(match STR ''X'' (BinaryPattern BinMul STR ''Xa'' STR ''Xb'') && match STR ''Xa'' (ConstantVarPattern STR ''x'')
        && match STR ''Xb'' (ConstantVarPattern STR ''y'')) ? base (ConstantVar x)"
end

end