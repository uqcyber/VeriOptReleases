theory TermRewrites
  imports Semantics.IRTreeEvalThms Semantics.TreeToGraphThms
begin

(*
typedef Substitution = "{\<sigma> :: string \<Rightarrow> IRExpr option . finite (dom \<sigma>)}"
proof -
  have "finite(dom(Map.empty)) \<and> ran Map.empty = {}" by auto
  then show ?thesis
    by fastforce
qed
*)

fun expr_at_node :: "IRGraph \<Rightarrow> ID \<Rightarrow> IRExpr"
  (infix "@@" 50) where
  "expr_at_node g n = (SOME e . (g \<turnstile> n \<simeq> e))"
                          
lemma expr_at_node: "g \<turnstile> n \<simeq> e \<Longrightarrow> g \<turnstile> n \<simeq> (g @@ n)"
  using expr_at_node.simps repDet 
  by (simp add: someI)

lemma graph_refinement:
  "graph_refinement g1 g2 \<Longrightarrow> (\<forall>n m p v. n \<in> ids g1 \<longrightarrow> ([g1, m, p] \<turnstile> n \<mapsto> v) \<longrightarrow> ([g2, m, p] \<turnstile> n \<mapsto> v))"
  unfolding graph_refinement_def expr_at_node.simps
  apply auto[1]
  using expr_at_node.simps encodeeval_def graph_refinement_def le_expr_def 
  by (meson term_graph_evaluation)

datatype SubValue = SubExpr(s_expr: IRExpr) | SubConst(s_val: Value)

typedef Substitution = "{s :: String.literal \<rightharpoonup> SubValue . finite (dom s)}"
  using finite_dom_map_of by blast

setup_lifting type_definition_Substitution

lift_definition subst :: "(String.literal \<times> SubValue) list \<Rightarrow> Substitution"
  is "map_of"
  by (simp add: finite_dom_map_of)

lift_definition subst_set :: "Substitution \<Rightarrow> (String.literal \<times> SubValue) set"
  is "Map.graph" .

lemma subst_reconstruct:
  "distinct (map fst x) \<Longrightarrow> set x = subst_set (subst x)"
  by (simp add: graph_map_of_if_distinct_dom subst.rep_eq subst_set.rep_eq)

lift_definition dom :: "Substitution \<Rightarrow> String.literal set"
  is Map.dom .

lift_definition maps_to :: "Substitution \<Rightarrow> String.literal \<Rightarrow> SubValue option"
  is "\<lambda> \<sigma> x . \<sigma> x" .

code_datatype subst Abs_Substitution

lemma [code]: "Rep_Substitution (subst m) = map_of m"
  using Abs_Substitution_inverse
  using subst.rep_eq by blast

lemma dom_code[code]: "dom (subst m) = set (map fst m)"
  by (simp add: dom.rep_eq dom_map_of_conv_image_fst subst.rep_eq)

lemma in_dom: "x \<in> dom \<sigma> \<Longrightarrow> maps_to \<sigma> x \<noteq> None"
  by (simp add: dom.rep_eq domIff maps_to.rep_eq)
  
fun substitute :: "Substitution \<Rightarrow> IRExpr \<Rightarrow> IRExpr" (infix "$" 60) where
  "substitute \<sigma> (UnaryExpr op e) = UnaryExpr op (\<sigma> $ e)" |
  "substitute \<sigma> (BinaryExpr op e1 e2) = BinaryExpr op (\<sigma> $ e1) (\<sigma> $ e2)" |
  "substitute \<sigma> (ConditionalExpr b e1 e2) = ConditionalExpr (\<sigma> $ b) (\<sigma> $ e1) (\<sigma> $ e2)" |
  "substitute \<sigma> (ParameterExpr i s) = ParameterExpr i s" |
  "substitute \<sigma> (LeafExpr n s) = LeafExpr n s" |
  "substitute \<sigma> (ConstantExpr v) = ConstantExpr v" |
  "substitute \<sigma> (ConstantVar x) = 
      (case maps_to \<sigma> x of Some (SubConst v) \<Rightarrow> ConstantExpr v | _ \<Rightarrow> ConstantVar x)" |
  "substitute \<sigma> (VariableExpr x s) = 
      (case maps_to \<sigma> x of None \<Rightarrow> (VariableExpr x s) | Some (SubExpr y) \<Rightarrow> y)"

lift_definition union :: "Substitution \<Rightarrow> Substitution \<Rightarrow> Substitution"
  is "\<lambda>\<sigma>1 \<sigma>2. \<sigma>1 ++ \<sigma>2"
  by simp

(*fun union :: "Substitution \<Rightarrow> Substitution \<Rightarrow> Substitution" where
  "union \<sigma>1 \<sigma>2 = Abs_Substitution (\<lambda>name. if maps_to \<sigma>1 name = None then maps_to \<sigma>2 name else maps_to \<sigma>1 name)"
*)

lemma not_empty_has_member:
  assumes "xs \<noteq> []"
  shows "\<exists> k v. List.member xs (k, v)"
  using assms apply (cases xs; auto)
  by (meson member_rec(1))

value "map_of ([(x, xv1), (y, yv)] @ [(z, zv), (x, xv2)]) x"

lemma equal_mapping_implies_equal:
  assumes "\<forall>k. maps_to \<sigma>1 k = maps_to \<sigma>2 k"
  shows "\<sigma>1 = \<sigma>2"
  using assms unfolding maps_to_def using Rep_Substitution
  by (metis Rep_Substitution_inverse ext id_def map_fun_apply)

(*
lemma 
  "maps_to (union (subst \<sigma>1) (subst \<sigma>2)) k = maps_to (subst (\<sigma>1 @ \<sigma>2)) k"
  (is "maps_to ?union k = maps_to ?add k")
proof (cases "\<exists> v. List.member \<sigma>1 (k, v)"; cases "\<exists> v. List.member \<sigma>2 (k, v)")
  case True \<comment>\<open>key has mapping in both\<close>
  then show ?thesis sorry
next
  case False \<comment>\<open>key in \<sigma>1 but not \<sigma>2\<close>
  then show ?thesis sorry
next
  \<comment>\<open>key in \<sigma>2 but not \<sigma>1\<close>
  assume a1: "\<nexists>v. List.member \<sigma>1 (k, v)"
  assume a2: "\<exists>v. List.member \<sigma>2 (k, v)"
  obtain v where v: "List.member \<sigma>2 (k, v)"
    using a2 by auto
  from a1 v have "maps_to ?add k = Some v"
    unfolding maps_to_def subst_def using map_of_append sledgehammer
  then show ?thesis sorry
next
  \<comment>\<open>key in neither\<close>
  assume a1: "\<nexists>v. List.member \<sigma>1 (k, v)"
  assume a2: "\<nexists>v. List.member \<sigma>2 (k, v)"
  from a1 a2 have "maps_to ?add k = None"
    by (metis domD in_set_member map_add_dom_app_simps(2) map_of_SomeD map_of_append maps_to.rep_eq opt_to_list.cases option.discI subst.rep_eq)
  then show ?thesis
    by (metis map_add_None map_of_append maps_to.rep_eq subst.rep_eq union.rep_eq)
qed
*)

lemma union_code[code]:
  "union (subst \<sigma>1) (subst \<sigma>2) = (subst (\<sigma>2 @ \<sigma>1))"
  (is "?union = ?add")
  using map_of_append unfolding subst_def union_def
  using subst.abs_eq subst.rep_eq by auto

(*
proof (cases "\<sigma>1 = []")
  case True
  then show ?thesis
    by (metis Rep_Substitution_inverse append.right_neutral append_Nil map_of_append subst.rep_eq union.rep_eq)
next
  case False
  then obtain k v where v: "List.member \<sigma>1 (k, v)"
    using not_empty_has_member by blast
  show ?thesis
  proof (cases "\<exists>v. List.member \<sigma>2 (k, v)")
    case True
    obtain v' where v': "List.member \<sigma>2 (k, v')"
      using True
      by blast
    have rhs: "maps_to (?add) k = Some v"
      using v v' unfolding maps_to_def subst_def sorry
    have lhs: "maps_to (?union) k = Some v"
      sorry
    from lhs rhs have "maps_to (?add) k = maps_to (?union) k"
      sorry
    then show ?thesis using equal_mapping_implies_equal sorry
  next
    case False
    then show ?thesis
      by simp
  qed
qed
  
  apply (induction \<sigma>1; induction \<sigma>2; auto)
  apply (metis append_Nil map_of_append subst.abs_eq subst.rep_eq)
  apply (metis map_of_append self_append_conv subst.abs_eq subst.rep_eq)
   apply (metis append_Nil map_of_append subst.abs_eq subst.rep_eq)
  sorry
*)

fun compatible :: "Substitution \<Rightarrow> Substitution \<Rightarrow> bool" where
  "compatible \<sigma>1 \<sigma>2 = (\<forall>x \<in> dom \<sigma>1. maps_to \<sigma>2 x \<noteq> None \<longrightarrow> maps_to \<sigma>1 x = maps_to \<sigma>2 x)"

fun substitution_union :: "Substitution option \<Rightarrow> Substitution option \<Rightarrow> Substitution option" (infix "\<uplus>" 70) where
  "substitution_union s1 s2 = 
      (case s1 of
       None \<Rightarrow> None |
       Some \<sigma>1 \<Rightarrow> 
           (case s2 of
            None \<Rightarrow> None |
            Some \<sigma>2 \<Rightarrow> (if compatible \<sigma>1 \<sigma>2 then Some (union \<sigma>1 \<sigma>2) else None)
           )
      )"

(*lemma "sup x y = x"*)

definition EmptySubstitution :: "Substitution" where 
  "EmptySubstitution = subst []"

fun match :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> Substitution option" where
  "match (UnaryExpr op e) (UnaryExpr op' e') = 
      (if op = op' then match e e' else None)" |
  "match (BinaryExpr op e1 e2) (BinaryExpr op' e1' e2') = 
      (if op = op' then (match e1 e1') \<uplus> (match e2 e2') else None)" |
  "match (ConditionalExpr b e1 e2) (ConditionalExpr b' e1' e2') = 
      (match b b') \<uplus> ((match e1 e1') \<uplus> (match e2 e2'))" |
  "match (ParameterExpr i1 s1) (ParameterExpr i2 s2) = 
      (if i1 = i2 \<and> s1 = s2 then Some EmptySubstitution else None)" |
  "match (LeafExpr n1 s1) (LeafExpr n2 s2) = 
      (if n1 = n2 \<and> s1 = s2 then Some EmptySubstitution else None)" |
  "match (ConstantExpr v1) (ConstantExpr v2) = 
      (if v1 = v2 then Some EmptySubstitution else None)" |
  "match (ConstantVar name) (ConstantExpr v) = 
      Some (subst [(name, (SubConst v))])" |
  "match (VariableExpr name s) e = 
      Some (subst [(name, (SubExpr e))])" |
  "match _ _ = None"


fun vars :: "IRExpr \<Rightarrow> String.literal fset" where
  "vars (UnaryExpr op e) = vars e" |
  "vars (BinaryExpr op e1 e2) = vars e1 |\<union>| vars e2" |
  "vars (ConditionalExpr b e1 e2) = vars b |\<union>| vars e1 |\<union>| vars e2" |
  "vars (ParameterExpr i s) = {||}" |
  "vars (LeafExpr n s) = {||}" |
  "vars (ConstantExpr v) = {||}" |
  "vars (ConstantVar x) = {|x|}" |
  "vars (VariableExpr x s) = {|x|}"

(*
typedef Rewrite = "{ (e1,e2,cond) :: IRExpr \<times> IRExpr \<times> (Substitution \<Rightarrow> bool) | e1 e2 cond . vars e2 |\<subseteq>| vars e1 }" 
proof -
  have "\<exists>v. vars (ConstantExpr v) |\<subseteq>| vars (ConstantExpr v)" by simp
  then show ?thesis
    by blast
qed

setup_lifting type_definition_Rewrite


fun construct_rewrite :: "IRExpr \<times> IRExpr \<times> (Substitution \<Rightarrow> bool) \<Rightarrow> Rewrite option" where
  "construct_rewrite (e1, e2, cond) =
    (if vars e2 |\<subseteq>| vars e1 then Some (Abs_Rewrite (e1, e2, cond)) else None)"

code_datatype Abs_Rewrite

lemma "Abs_Rewrite (Rep_Rewrite r) = r"
  by (simp add: Rep_Rewrite_inverse)

lemma [code]: "Rep_Rewrite (Abs_Rewrite (e1, e2)) = (e1, e2)"
  sorry

fun rewrite :: "Rewrite \<Rightarrow> IRExpr \<Rightarrow> IRExpr option" where
  "rewrite r e = (let (e1,e2,cond) = Rep_Rewrite r in 
                   (case match e1 e of
                    Some \<sigma> \<Rightarrow> 
                      (if cond \<sigma> then Some (\<sigma> $ e2) else None) |
                    None \<Rightarrow> None))"

definition rewrite_valid :: "Rewrite \<Rightarrow> bool" where
  "rewrite_valid r = (let (e1,e2,cond) = Rep_Rewrite r in
    (\<forall>\<sigma> e. is_ground e \<longrightarrow> match e1 e = Some \<sigma> \<longrightarrow> (e \<ge> (\<sigma> $ e2))))"

definition rewrite_valid_rep :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
  "rewrite_valid_rep e1 e2 = (vars e1 |\<subseteq>| vars e2 \<longrightarrow> (\<forall>\<sigma> e.  match e1 e = Some \<sigma> \<longrightarrow> (e \<ge> (\<sigma> $ e2))))"

*)




section \<open>Code Generation via Match Primitives\<close>

subsection \<open>Pattern Expressions\<close>
text \<open>
A pattern expression corresponds to an @{typ IRExpr} without nesting.
Nested expressions are replaced with a string placeholder.

This restricts match primitives to match just one node.
\<close>
type_synonym VarName = "String.literal"
type_synonym Vars = "VarName fset"

datatype PatternExpr =
    UnaryPattern IRUnaryOp VarName
  | BinaryPattern IRBinaryOp VarName VarName
  | ConditionalPattern VarName VarName VarName
  | VariablePattern VarName
  | ConstantPattern Value
  | ConstantVarPattern VarName


subsection \<open>Variable Generation\<close>
text \<open>
Variable scoping in match primitives is handled by the Scope type.
Scope is a pair of;
\begin{enumerate}
\item the set of used variable names, and
\item a mapping of the @{emph \<open>real\<close>} variable names to the most recent @{emph \<open>alias\<close>} for the real variable.
\end{enumerate}

A rewriting rule consists of @{emph \<open>real\<close>} variable names which can overlap.
A match primitive has @{emph \<open>alias\<close>} variable names to the real names.
Aliases must be unique.
\<close>
type_synonym Scope = "Vars \<times> (VarName \<rightharpoonup> VarName)"

fun remove_var :: "VarName \<Rightarrow> Scope \<Rightarrow> Scope" where
  "remove_var v (vs, m) = (vs - {|v|}, m)"
fun add_var :: "VarName \<Rightarrow> Scope \<Rightarrow> Scope" where
  "add_var v (vs, m) = (vs |\<union>| {|v|}, m)"


function fresh_var :: "VarName \<Rightarrow> Scope \<Rightarrow> VarName" where
  "fresh_var var s = 
    (if var |\<in>| (fst s) 
      then fresh_var (var + STR ''z'') (remove_var var s)
      else var)"
  by fastforce+
(*(* For some reason, by proving that this function terminates the definition of match_pattern
   no longer terminates. *)
termination
  apply (relation "measure (\<lambda>(v, s). (fcard (fst s)))")
  apply simp
  using fcard_fminus1_less by force*)

fun fresh :: "VarName \<Rightarrow> Scope \<Rightarrow> Scope \<times> VarName" where
  "fresh var s = (let v = fresh_var var s in (add_var v s, v))"


lemma fresh [code]:
  "fresh_var var s = 
    (if var |\<in>| (fst s) 
      then fresh_var (var + STR ''z'') (remove_var var s)
      else var)"
  sorry (* This will not be required when termination is proved *)


subsection \<open>Side-Conditions\<close>

datatype SideCondition =
  IsConstantExpr IRExpr |
  WellFormed IRExpr |
  IsStamp IRExpr Stamp |
  StampUnder IRExpr IRExpr |
  UpMaskEquals IRExpr "64 word" |
  DownMaskEquals IRExpr "64 word" |
  UpMaskCancels IRExpr IRExpr |
  Empty |
  And SideCondition SideCondition |
  Not SideCondition

definition wf_stamp :: "IRExpr \<Rightarrow> bool" where
  "wf_stamp e = (\<forall>m p v. ([m, p] \<turnstile> e \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr e))"
fun eval_condition :: "SideCondition \<Rightarrow> bool" where
  "eval_condition (IsConstantExpr e) = is_ConstantExpr e" |
  "eval_condition (WellFormed e) = wf_stamp e" |
  "eval_condition (IsStamp e s) = ((stamp_expr e) = s)" |
  "eval_condition (StampUnder e1 e2) = (stamp_under (stamp_expr e1) (stamp_expr e2))" |
  "eval_condition (UpMaskEquals e m) = (IRExpr_up e = m)" |
  "eval_condition (DownMaskEquals e m) = (IRExpr_down e = m)" |
  "eval_condition (UpMaskCancels e1 e2) = (((and (IRExpr_up e1) (IRExpr_up e2)) = 0))" |
  
  "eval_condition (Empty) = True" |

  "eval_condition (And sc1 sc2) = ((eval_condition sc1) \<and> (eval_condition sc2))" |
  "eval_condition (Not sc) = (\<not>(eval_condition sc))"


subsection \<open>Match Primitives\<close>
datatype MATCH =
  match VarName PatternExpr |
  equality VarName VarName (infixl "==" 52) |
  seq MATCH MATCH (infixl "&&" 50) |
  either MATCH MATCH (infixl "||" 49) |
  negate SideCondition |
  check SideCondition |
  noop

text \<open>The definitions of la and ra help to feed the scope through when generating a match pattern.\<close>
definition la :: "('b \<Rightarrow> 'a) \<Rightarrow> (Scope \<Rightarrow> Scope \<times> 'b) \<Rightarrow> (Scope \<Rightarrow> Scope \<times> 'a)"
  (infix "\<langle>" 65)
  where
  "la f f' s = (fst (f' s), f (snd (f' s)))"

definition ra :: "(Scope \<Rightarrow> Scope \<times> ('b \<Rightarrow> 'a)) \<Rightarrow> (Scope \<Rightarrow> Scope \<times> 'b) \<Rightarrow> (Scope \<Rightarrow> Scope \<times> 'a)"
  (infixl "\<rangle>" 54)
  where
  "ra f f' s = ((fst (f' (fst (f s)))), (snd (f s)) (snd (f' (fst (f s)))))"

text \<open>Join generates the lhs and feeds the scope through to then generate the rhs.
      The resulting match pattern is an sequential match of the lhs and rhs, @{term "lhs && rhs"}.
      The resulting scope is the result of generating the rhs after the lhs.\<close>
definition join :: "('b \<Rightarrow> 'c \<times> MATCH) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'a \<times> MATCH) \<Rightarrow> 'b \<Rightarrow> 'a \<times> MATCH" (infixl "|>" 53) where
  "join x y s = 
    (let (lhs_scope, lhs_match) = x s in
    (let (rhs_scope, rhs_match) = (y s lhs_scope) in
    (rhs_scope, (lhs_match && rhs_match))))"

abbreviation descend where
  "descend f e v \<equiv> (\<lambda>s s'. f e (snd (fresh v s)) s')"

fun register_name where
  "register_name (s, m) vn v = (s, m(vn\<mapsto>v))"

fun match_pattern :: "IRExpr \<Rightarrow> VarName \<Rightarrow> Scope \<Rightarrow> Scope \<times> MATCH" where
  "match_pattern (UnaryExpr op e) v =
    match v \<langle>
      (UnaryPattern op \<langle> fresh STR ''a'')
    |> descend match_pattern e STR ''a''" |
  "match_pattern (BinaryExpr op e1 e2) v =
    match v \<langle> 
      (BinaryPattern op \<langle> fresh STR ''a'' \<rangle> fresh STR ''b'')
    |> descend match_pattern e1 STR ''a''
    |> descend match_pattern e2 STR ''b''" |
  "match_pattern (ConditionalExpr b e1 e2) v =
    match v \<langle>
      (ConditionalPattern \<langle> fresh STR ''a'' \<rangle> fresh STR ''b'' \<rangle> fresh STR ''c'')
    |> descend match_pattern b STR ''a''
    |> descend match_pattern e1 STR ''b''
    |> descend match_pattern e2 STR ''c''" |
  \<comment> \<open>If a variable is reused, generate an equality check, else, generate a noop.\<close>
  "match_pattern (VariableExpr vn st) v = 
    (\<lambda>s. case (snd s) vn of 
      None \<Rightarrow> (register_name s vn v, noop) |
      Some v' \<Rightarrow> (register_name s vn v, equality v' v))" |
  "match_pattern (ConstantExpr c) v =
    (\<lambda>s. (s, match v (ConstantPattern c)))" |
  "match_pattern (ConstantVar c) v =
    (\<lambda>s. (s, match v (ConstantVarPattern c)))"


subsubsection \<open>Match Primitive Semantics\<close>
type_synonym Subst = "VarName \<Rightarrow> IRExpr option"

fun eval_match :: "MATCH \<Rightarrow> Subst \<Rightarrow> Subst option" where
  "eval_match (match v (UnaryPattern op1 x)) s =
    (case s v of 
      Some (UnaryExpr op2 xe) \<Rightarrow>
        (if op1 = op2 then Some (s(x\<mapsto>xe)) else None) |
      Some _ \<Rightarrow> None |
      None \<Rightarrow> None)" |
  "eval_match (match v (BinaryPattern op1 x y)) s =
    (case s v of
      Some (BinaryExpr op2 xe ye) \<Rightarrow>
        (if op1 = op2 
          then Some (s(x\<mapsto>xe) ++ s(y\<mapsto>ye))
          else None) |
      Some _ \<Rightarrow> None |
      None \<Rightarrow> None)" |
  "eval_match (match v (ConditionalPattern c tb fb)) s =
    (case s v of
      Some (ConditionalExpr ce te fe) \<Rightarrow>
        (Some (s(c\<mapsto>ce) ++ s(tb\<mapsto>te) ++ s(fb\<mapsto>fe))) |
      Some _ \<Rightarrow> None |
      None \<Rightarrow> None)" |
  "eval_match (match v (ConstantPattern c1)) s =
    (case s v of 
      Some (ConstantExpr c2) \<Rightarrow>
        (if c1 = c2 then Some s else None) |
      Some _ \<Rightarrow> None |
      None \<Rightarrow> None)" |
  "eval_match (equality v1 v2) s =
    (if s v1 = s v2 then Some s else None)" |
  "eval_match (seq m1 m2) s =
      (case eval_match m1 s of 
        None \<Rightarrow> None |
        Some s' \<Rightarrow> eval_match m2 s')" |
  "eval_match (either m1 m2) s =
      (case eval_match m1 s of
        None \<Rightarrow> eval_match m2 s |
        Some s' \<Rightarrow> Some s')" |
  "eval_match noop s = Some s" |
  "eval_match (check sc) s = Some s" | (* TODO: Check always passes *)
  "eval_match (negate sc) s = Some s" | (* TODO: Check always passes *)
  "eval_match _ s = None"


subsection \<open>Combining Rules\<close>

datatype Rules =
  base IRExpr |
  cond MATCH Rules (infixl "?" 52) |
  else Rules Rules (infixl "else" 50) |
  choice "Rules list"

text \<open>Use the scope of a generated match to replace real variable names with aliases in the rewrite result.\<close>
fun expr_result :: "IRExpr \<Rightarrow> Scope \<Rightarrow> IRExpr" where
  "expr_result (UnaryExpr op e) s = 
    UnaryExpr op (expr_result e s)" |
  "expr_result (BinaryExpr op e1 e2) s = 
    BinaryExpr op (expr_result e1 s) (expr_result e2 s)" |
  "expr_result (ConditionalExpr b e1 e2) s = 
    ConditionalExpr (expr_result b s) (expr_result e1 s) (expr_result e2 s)" |
  "expr_result (VariableExpr vn st) (s, m) = 
    (case m vn of None \<Rightarrow> VariableExpr vn st 
                | Some v' \<Rightarrow> VariableExpr v' st)" |
  "expr_result e v = e"

fun ground_condition :: "SideCondition \<Rightarrow> Scope \<Rightarrow> SideCondition" where
  "ground_condition (IsConstantExpr p) s = (IsConstantExpr (expr_result p s))" |
  "ground_condition (WellFormed st) s = (WellFormed st)" |
  "ground_condition (IsStamp e st) s = (IsStamp (expr_result e s) st)" |
  "ground_condition (StampUnder e1 e2) s = (StampUnder (expr_result e1 s) (expr_result e2 s))" |
  "ground_condition (UpMaskEquals e m) s = (UpMaskEquals (expr_result e s) m)" |
  "ground_condition (DownMaskEquals e m) s = (DownMaskEquals (expr_result e s) m)" |
  "ground_condition (UpMaskCancels e1 e2) s = (UpMaskCancels (expr_result e1 s) (expr_result e2 s))" |
  "ground_condition (And sc1 sc2) s = And (ground_condition sc1 s) (ground_condition sc2 s)" |
  "ground_condition (Not sc) s = Not (ground_condition sc s)" |
  "ground_condition (Empty) s = Empty"

fun generate :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> SideCondition \<Rightarrow> Rules" where
  "generate p r sc = 
    (let (s, m) = match_pattern p STR ''e'' ({||}, (\<lambda>x. None))
     in ((m && check (ground_condition sc s)) ? (base (expr_result r s))))"


subsubsection \<open>Rules Semantics\<close>
definition start_unification where
  "start_unification e = ((\<lambda>x. None)(STR ''e'' := Some e))"

text \<open>Replace any variable expressions with value in a substitution.\<close>
fun ground_expr :: "IRExpr \<Rightarrow> Subst \<Rightarrow> IRExpr option" where
  "ground_expr (VariableExpr v s) u = u v" |
  "ground_expr (UnaryExpr op e) u = (case (ground_expr e u)
    of None \<Rightarrow> None | Some e' \<Rightarrow> Some (UnaryExpr op e'))" |
  "ground_expr (BinaryExpr op e1 e2) u = (case (ground_expr e1 u)
    of None \<Rightarrow> None | Some e1' \<Rightarrow> 
    (case (ground_expr e2 u)
      of None \<Rightarrow> None | Some e2' \<Rightarrow> Some (BinaryExpr op e1' e2')))" |
  "ground_expr (ConditionalExpr e1 e2 e3) u = (case (ground_expr e1 u)
    of None \<Rightarrow> None | Some e1' \<Rightarrow>
    (case (ground_expr e2 u)
      of None \<Rightarrow> None | Some e2' \<Rightarrow>
        (case (ground_expr e2 u)
          of None \<Rightarrow> None | Some e3' \<Rightarrow> Some (ConditionalExpr e1' e2' e3'))))" |
  "ground_expr e u = Some e"

lemma remove1_size:
  "x \<in> set xs \<Longrightarrow> size (remove1 x xs) < size xs"
  by (metis diff_less length_pos_if_in_set length_remove1 zero_less_one)

inductive eval_rules :: "Rules \<Rightarrow> Subst \<Rightarrow> IRExpr option \<Rightarrow> bool" where
  "eval_rules (base e) u (ground_expr e u)" |
  "\<lbrakk>eval_match m u = Some u';
    eval_rules r u' e\<rbrakk>
   \<Longrightarrow> eval_rules (cond m r) u e" |
  "\<lbrakk>eval_match m u = None\<rbrakk>
   \<Longrightarrow> eval_rules (cond m r) u None" |
  "\<lbrakk>eval_rules r1 u (Some r)\<rbrakk>
   \<Longrightarrow> eval_rules (r1 else r2) u (Some r)" |
  "\<lbrakk>eval_rules r1 u None;
    eval_rules r2 u e\<rbrakk>
   \<Longrightarrow> eval_rules (r1 else r2) u e" |
  "\<lbrakk>rule \<in> set rules;
    eval_rules rule u (Some r)\<rbrakk>
   \<Longrightarrow> eval_rules (choice rules) u (Some r)" |
  "\<lbrakk>\<forall> rule \<in> set rules. eval_rules rule u None\<rbrakk>
   \<Longrightarrow> eval_rules (choice rules) u None" |
  "\<lbrakk>rules = []\<rbrakk>
   \<Longrightarrow> eval_rules (choice rules) u None"

inductive_cases baseE: "eval_rules (base e') u e"
inductive_cases condE: "eval_rules (cond m r) u e"
inductive_cases elseE: "eval_rules (r1 else r2) u e"
inductive_cases choiceE: "eval_rules (choice r) u e"

code_pred [show_modes] eval_rules .
(*
  apply (metis Rules.exhaust old.prod.exhaust) by simp+
termination
  apply (relation "measure (size o fst)") 
       apply auto[1] apply simp+
  subgoal for rules r' rs rule apply (induction rules) apply simp apply (rule someI2) apply auto[1]
    using size_list_estimation
    using not_less_eq by fastforce
  subgoal premises x for rules rs u x rule
  proof -
    have "rule \<in> set rules" using x(1) apply simp apply (rule someI_ex)
      by (metis list.set_intros(1) set_ConsD someI_ex x(2))
    then show ?thesis using remove1_size apply simp
      by (smt (verit) One_nat_def Suc_pred ab_semigroup_add_class.add_ac(1) add_Suc_right length_pos_if_in_set length_remove1 not_add_less2 not_less_eq size_list_conv_sum_list sum_list_map_remove1)
  qed
  done
*)


subsection \<open>Rule Optimization\<close>

fun elim_noop :: "MATCH \<Rightarrow> MATCH" where
  "elim_noop (lhs && noop) = elim_noop lhs" |
  "elim_noop (noop && rhs) = elim_noop rhs" |
  "elim_noop (lhs && rhs) = ((elim_noop lhs) && (elim_noop rhs))" |
  "elim_noop m = m"

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

lemma sound_optimize_noop:
  "eval_match m s = eval_match (elim_noop m) s"
  apply (induction m arbitrary: s rule: elim_noop.induct)
  using noop_semantics_rhs apply force+
  using seq_det_rhs apply force+
  using elim_noop.simps(23) elim_noop.simps(46) seq_det_rhs apply presburger
  by force+

(*lemma monotonic_choice:
  assumes "\<forall> r e. eval_rules r u e = eval_rules (f r) u e"
  shows "eval_rules (choice rs) u e = eval_rules (choice (map f rs)) u e"
  apply (induction rs) apply simp using choiceE assms sorry
  subgoal for a rs apply (induction "choice rs" u rule: eval_rules.induct)*)

fun optimize_match :: "(MATCH \<Rightarrow> MATCH) \<Rightarrow> Rules \<Rightarrow> Rules" where
  "optimize_match f (base e) = base e" |
  "optimize_match f (m ? r) = f m ? optimize_match f r" |
  "optimize_match f (r1 else r2) = (optimize_match f r1 else optimize_match f r2)" |
  "optimize_match f (choice rules) = choice (map (optimize_match f) rules)"

lemma choice_join:
  assumes "eval_rules (a) u e = eval_rules (f a) u e"
  assumes "eval_rules (choice rules) u e = eval_rules (choice (map f rules)) u e"
  shows "eval_rules (choice (a # rules)) u e = eval_rules (choice (map f (a # rules))) u e"
  using assms
  by (smt (verit, ccfv_threshold) choiceE eval_rules.intros(6) eval_rules.intros(7) list.map_disc_iff list.set_intros(1) list.set_intros(2) list.simps(9) option.distinct(1) set_ConsD)

(*lemma optimize_match_valid:
  fixes f :: "MATCH \<Rightarrow> MATCH"
  assumes "eval_match m s = eval_match (f m) s"
  shows "eval_rules r u e = eval_rules (optimize_match f r) u e"
  apply (induction r arbitrary: u e rule: optimize_match.induct)
  apply simp
  using optimize_match.simps(2) condE assms *)


fun eliminate_noop :: "Rules \<Rightarrow> Rules" where
  "eliminate_noop (base e) = base e" |
  "eliminate_noop (m ? r) = elim_noop m ? eliminate_noop r" |
  "eliminate_noop (r1 else r2) = (eliminate_noop r1 else eliminate_noop r2)" |
  "eliminate_noop (choice rules) = choice (map eliminate_noop rules)"


lemma eliminate_noop_valid:
  "eval_rules r u e = eval_rules (eliminate_noop r) u e"
  apply (induction r arbitrary: u e rule: eliminate_noop.induct)
  apply simp
  using eliminate_noop.simps(2) condE sound_optimize_noop
    apply (smt (verit) eval_rules.simps) 
  using eliminate_noop.simps(3) elseE
   apply (smt (verit, del_insts) eval_rules.intros(4) eval_rules.intros(5))
  unfolding eliminate_noop.simps(4)
  subgoal premises ind for rules u e 
    using ind apply (induction rules) apply simp
    (*using choice_join
    by (metis list.set_intros(1) list.set_intros(2))*)
    subgoal premises ind' for a rules'
    proof -
      have a: "eval_rules (a) u e = eval_rules (eliminate_noop a) u e"
        using ind' by simp
      have rules: "eval_rules (choice rules') u e = eval_rules (choice (map eliminate_noop rules')) u e"
        using ind' by auto
      have "eval_rules (choice (a # rules')) u e = eval_rules (choice (map eliminate_noop (a # rules'))) u e"
        using a rules using choice_join 
        by presburger
      then show ?thesis by simp
    qed
    done
  done

fun elim_empty :: "MATCH \<Rightarrow> MATCH" where
  "elim_empty (check Empty) = noop" |
  "elim_empty (m1 && m2) = (elim_empty m1 && elim_empty m2)" |
  "elim_empty m = m"

lemma empty_check_semantics:
  "eval_match (check Empty) s = eval_match noop s"
  by simp

lemma sound_optimize_empty:
  "eval_match m s = eval_match (elim_empty m) s"
  apply (induction m arbitrary: s rule: elim_empty.induct)
  apply simp using empty_check_semantics
  using elim_empty.simps(2) eval_match.simps(6) apply presburger
  by simp+

fun eliminate_empty :: "Rules \<Rightarrow> Rules" where
  "eliminate_empty (base e) = base e" |
  "eliminate_empty (m ? r) = elim_empty m ? eliminate_empty r" |
  "eliminate_empty (r1 else r2) = (eliminate_empty r1 else eliminate_empty r2)" |
  "eliminate_empty (choice rules) = choice (map eliminate_empty rules)"

lemma eliminate_empty_valid:
  "eval_rules r u e = eval_rules (eliminate_empty r) u e"
  apply (induction r arbitrary: u e rule: eliminate_empty.induct)
  apply simp
  using eliminate_empty.simps(2) sound_optimize_empty condE
    apply (smt (verit) eval_rules.simps)
  using eliminate_empty.simps(3) elseE
   apply (smt (verit, del_insts) eval_rules.intros(4) eval_rules.intros(5))
  unfolding eliminate_empty.simps(4)
  subgoal premises ind for rules u e 
    using ind apply (induction rules) apply simp
    using choice_join
    by (metis list.set_intros(1) list.set_intros(2))
  done

fun combined_size :: "Rules \<Rightarrow> nat" where
  "combined_size (m ? r) = (2 * size m) + combined_size r" |
  "combined_size (base e) = 0" |
  "combined_size (r1 else r2) = combined_size r1 + combined_size r2" |
  "combined_size (choice (rule # rules)) = 1 + combined_size rule + combined_size (choice rules)" |
  "combined_size (choice []) = 1"

value "size noop"

function (sequential) lift_match :: "Rules \<Rightarrow> Rules" where
  "lift_match (r1 else r2) = ((lift_match r1) else (lift_match r2))" |
  "lift_match (choice rules) = choice (map lift_match rules)" |
  "lift_match ((m1 && m2) ? r) = (lift_match (m1 ? (m2 ? r)))" |
  "lift_match (m ? r) = m ? (lift_match r)" |
  "lift_match (base e) = (base e)"
  by pat_completeness auto
termination lift_match
  apply (relation "measures [combined_size, size]") apply auto[1]
  apply auto[1] apply auto[1] apply simp
  subgoal for rules x apply (induction rules) apply simp by fastforce
  apply simp subgoal for m2 r apply (cases m2) by (simp add: lift_match.psimps(4))
  apply simp
  by simp+

lemma chain_equiv:
  "eval_rules (m1 ? (m2 ? r)) u e = eval_rules ((m1 && m2) ? r) u e"
  using condE apply auto[1]
   apply (smt (verit) eval_match.simps(6) eval_rules.simps option.simps(4) option.simps(5))
  by (metis (no_types, lifting) eval_match.simps(6) eval_rules.intros(2) eval_rules.intros(3) option.case_eq_if option.distinct(1) option.exhaust_sel)

lemma lift_match_valid:
  "eval_rules r u e = eval_rules (lift_match r) u e"
  apply (induction r arbitrary: u e rule: lift_match.induct) 
           apply simp 
  using lift_match.simps(1) elseE
           apply (smt (verit) eval_rules.simps)
  unfolding lift_match.simps(2)
  subgoal premises ind for rules u e 
    using ind apply (induction rules) apply simp
    using choice_join
    by (metis list.set_intros(1) list.set_intros(2))
         apply (simp add: chain_equiv)
  apply (metis (full_types) condE eval_rules.intros(2) eval_rules.intros(3) lift_match.simps(4))
  apply (metis (full_types) condE eval_rules.intros(2) eval_rules.intros(3) lift_match.simps(5))
      apply (metis (full_types) condE eval_rules.intros(2) eval_rules.intros(3) lift_match.simps(6))
     apply (metis (full_types) condE eval_rules.intros(2) eval_rules.intros(3) lift_match.simps(7))
    apply (metis (full_types) condE eval_rules.intros(2) eval_rules.intros(3) lift_match.simps(8))
   apply (metis (full_types) condE eval_rules.intros(2) eval_rules.intros(3) lift_match.simps(9))
  by simp

(*
fun lift_common :: "Rules \<Rightarrow> Rules" where
  "lift_common (m1 ? r1 else m2 ? r2) = 
    (if m1 = m2
      then m1 ? (lift_common (r1 else r2))
      else (lift_common (m1 ? r1) else lift_common (m2 ? r2)))" |
  "lift_common (r1 else r2) = ((lift_common r1) else (lift_common r2))" |
  "lift_common (m ? r) = (m ? (lift_common r))" |
  "lift_common (base e) = base e"*)

fun join_conditions :: "Rules \<Rightarrow> Rules option" where
  "join_conditions (m1 ? r1 else m2 ? r2) = 
    (if m1 = m2
      then Some (m1 ? (r1 else r2)) else None)" |
  "join_conditions (m1 ? (m2 ? r1)) = 
    (if m1 = m2
      then Some ((m1 ? r1)) else None)" |
  "join_conditions r = None"

lemma join_conditions_shrinks:
  "join_conditions r = Some r' \<Longrightarrow> size r' < size r"
  apply (induction r rule: join_conditions.induct)
  apply (metis One_nat_def Rules.size(6) Rules.size(7) Suc_eq_plus1 add_Suc_right add_Suc_shift join_conditions.simps(1) lessI option.distinct(1) option.sel)
   apply (metis One_nat_def Rules.size(6) join_conditions.simps(2) less_add_same_cancel1 option.discI option.inject zero_less_one)
  by simp+

(*
lemma join_conditions_shrinks_cond:
  "join_conditions (m ? r) = Some r' \<Longrightarrow> combined_size r' < combined_size (m ? r)"
  apply (induction "m ? r" rule: join_conditions.induct)
  apply auto subgoal for m2 r1 apply (cases "m = m2") apply auto sorry

lemma join_conditions_shrinks_combined:
  "join_conditions r = Some r' \<Longrightarrow> combined_size r' < combined_size r"
  apply (induction r rule: join_conditions.induct) apply auto
  subgoal for m1 r1 m2 r2
  apply (cases "m1 = m2") apply auto sledgehammer
  apply (metis One_nat_def Rules.size(6) Rules.size(7) Suc_eq_plus1 add_Suc_right add_Suc_shift join_conditions.simps(1) lessI option.distinct(1) option.sel)
   apply (metis One_nat_def Rules.size(6) join_conditions.simps(2) less_add_same_cancel1 option.discI option.inject zero_less_one)
  by simp+*)

function lift_common :: "Rules \<Rightarrow> Rules" where
  "lift_common (r1 else r2) = (
    case join_conditions (r1 else r2) 
    of Some r \<Rightarrow> lift_common r |
       None \<Rightarrow> (lift_common r1 else lift_common r2))" |
  "lift_common (m ? r) = (
    case join_conditions (m ? r) 
    of Some r' \<Rightarrow> lift_common r' |
       None \<Rightarrow> (m ? lift_common r))" |
  "lift_common (choice rules) = choice (map lift_common rules)" |
  "lift_common (base e) = base e"
  using combined_size.cases
  apply metis
  by simp+
termination
  apply (relation "measures [size]") apply auto[1]
    apply simp subgoal for r1 r2 apply (induction r1 rule: join_conditions.induct) by simp+
   apply auto[1] using join_conditions_shrinks apply fastforce+ 
  apply auto[1] using join_conditions_shrinks by (simp add: le_imp_less_Suc size_list_estimation')
  
lemma match_eq:
  "eval_match (m && m) u = eval_match m u"
  sorry

lemma redundant_conditions:
  "eval_rules (m ? (m ? r1)) u e = eval_rules (m ? r1) u e"
  using match_eq chain_equiv
  by (smt (verit, best) condE eval_rules.intros(2) eval_rules.intros(3))

lemma join_conditions_valid:
  "join_conditions r = Some r' \<Longrightarrow> eval_rules r u e = eval_rules r' u e"
  apply (induction r rule: join_conditions.induct)
  apply (smt (verit, ccfv_threshold) condE elseE eval_rules.intros(2) eval_rules.intros(3) eval_rules.intros(4) eval_rules.intros(5) join_conditions.simps(1) option.distinct(1) option.sel)
  apply (metis join_conditions.simps(2) option.discI option.inject redundant_conditions)
  by simp+

lemma lift_common_valid:
  "eval_rules r u e = eval_rules (lift_common r) u e"
  apply (induction r arbitrary: u e rule: lift_common.induct)
    subgoal for r1 r2 apply (cases "join_conditions (r1 else r2)")
    apply (smt (verit, del_insts) elseE eval_rules.intros(4) eval_rules.intros(5) lift_common.simps(1) option.simps(4))
      by (simp add: join_conditions_valid)
    subgoal for m r u apply (cases "join_conditions (m ? r)")
       apply simp apply (metis condE eval_rules.intros(2) eval_rules.intros(3))
      by (simp add: join_conditions_valid)
    subgoal for rules u apply (induction rules)
      apply simp
      by (metis choice_join lift_common.simps(3) list.set_intros(1) list.set_intros(2))
    by simp

fun find_common :: "MATCH \<Rightarrow> Rules \<Rightarrow> Rules option" where
  "find_common m (base e) = None" |
  "find_common m (r1 else r2) = None" |
  "find_common m (m' ? r) = (if m = m' then Some r else None)" |
  "find_common m (choice rules) = None"

fun find_uncommon :: "MATCH \<Rightarrow> Rules \<Rightarrow> Rules option" where
  "find_uncommon m (m' ? r) = (if m = m' then None else Some (m' ? r))" |
  "find_uncommon m r = Some r"

definition join_common :: "MATCH \<Rightarrow> Rules list \<Rightarrow> Rules list" where
  "join_common m rules = List.map_filter (find_common m) rules"

definition join_uncommon :: "MATCH \<Rightarrow> Rules list \<Rightarrow> Rules list" where
  "join_uncommon m rules = List.map_filter (find_uncommon m) rules"

lemma size_join_uncommon:
  "size (join_uncommon m rules) \<le> size rules"
  unfolding join_uncommon_def map_filter_def
  by (induction rule: find_uncommon.induct; auto)

function (sequential) combine_conditions :: "Rules \<Rightarrow> Rules" where
  "combine_conditions (base e) = base e" |
  "combine_conditions (r1 else r2) = (combine_conditions r1 else combine_conditions r2)" |
  "combine_conditions (m ? r) = (m ? combine_conditions r)" |
  "combine_conditions (choice ((m ? r) # rules)) = 
    choice ((m ? combine_conditions (choice (r # join_common m rules))) # map combine_conditions (join_uncommon m rules))" |
  "combine_conditions (choice rules) = 
    choice (map combine_conditions rules)"
  apply pat_completeness+
  by simp+

lemma find_common_size:
  assumes "(find_common m r) \<noteq> None"
  shows "size (the (find_common m r)) < size r"
  using assms apply (induction r rule: find_common.induct)
  apply simp+ apply fastforce by simp

lemma "size_list size (join_common m rules) \<le> (size_list size rules)"
  unfolding join_common_def map_filter_def
  (*apply (induction rules) apply auto[1]*)
  apply (induction rule: find_common.induct)
  apply (induction rules) 
  apply simp using find_common_size sledgehammer

lemma
  "combined_size (choice (join_common m rules))
       < combined_size (m ? (choice rules)) \<or>
       combined_size (choice (join_common m rules)) =
       combined_size (m ? (choice rules)) \<and>
       size_list size (join_common m rules) < Suc (size_list size rules)"

termination combine_conditions
  apply (relation "measures [combined_size, size]") apply auto[1] apply simp+
  apply blast+
  apply fastforce+ apply simp unfolding join_common_def sledgehammer

definition optimized_export where
  "optimized_export = lift_common o lift_match o eliminate_noop o eliminate_empty"

lemma optimized_export_valid:
  "eval_rules r u e = eval_rules (optimized_export r) u e"
  unfolding optimized_export_def comp_def
  using lift_common_valid lift_match_valid eliminate_noop_valid eliminate_empty_valid by simp


subsection \<open>Java Generation\<close>

fun unary_op_class :: "IRUnaryOp \<Rightarrow> string" where
  "unary_op_class UnaryAbs = ''AbsNode''" |
  "unary_op_class UnaryNeg = ''NegNode''" |
  "unary_op_class UnaryNot = ''NotNode''" |
  "unary_op_class UnaryLogicNegation = ''LogicNegationNode''" |
  "unary_op_class (UnaryNarrow _ _) = ''NarrowNode''" |
  "unary_op_class (UnarySignExtend _ _) = ''SignExtendNode''" |
  "unary_op_class (UnaryZeroExtend _ _) = ''ZeroExtendNode''"

fun binary_op_class :: "IRBinaryOp \<Rightarrow> string" where
  "binary_op_class BinAdd = ''AddNode''" |
  "binary_op_class BinMul = ''MulNode''" |
  "binary_op_class BinSub = ''SubNode''" |
  "binary_op_class BinAnd = ''AndNode''" |
  "binary_op_class BinOr = ''OrNode''" |
  "binary_op_class BinXor = ''XorNode''" |
  "binary_op_class BinShortCircuitOr = ''ShortCircuitOrNode''" |
  "binary_op_class BinLeftShift = ''LeftShiftNode''" |
  "binary_op_class BinRightShift = ''RightShiftNode''" |
  "binary_op_class BinURightShift = ''UnaryRightShiftNode''" |
  "binary_op_class BinIntegerEquals = ''IntegerEqualsNode''" |
  "binary_op_class BinIntegerLessThan = ''IntegerLessThanNode''" |
  "binary_op_class BinIntegerBelow = ''IntegerBelowNode''"

fun export_pattern :: "PatternExpr \<Rightarrow> string" where
  "export_pattern (UnaryPattern op v) = unary_op_class op" |
  "export_pattern (BinaryPattern op v1 v2) = binary_op_class op" |
  "export_pattern (ConditionalPattern v1 v2 v3) = ''ConditionalNode''" |
  "export_pattern (ConstantPattern v) = ''ConstantNode''" |
  "export_pattern (ConstantVarPattern v) = ''ConstantNode''" |
  "export_pattern (VariablePattern v) = ''ERROR: Variable should not occur on LHS''"

(* https://stackoverflow.com/questions/23864965/string-of-nat-in-isabelle *)
fun string_of_nat :: "nat \<Rightarrow> string" where
  "string_of_nat n = (if n < 10 then [char_of (48 + n)] else 
     string_of_nat (n div 10) @ [char_of (48 + (n mod 10))])"

definition string_of_int :: "int \<Rightarrow> string" where
  "string_of_int i = (if i < 0 then ''-'' @ string_of_nat (nat (- i)) else 
     string_of_nat (nat i))"

fun export_value :: "Value \<Rightarrow> string" where
  "export_value (IntVal s v) = string_of_int (sint v)" |
  "export_value _ = ''ERROR: unsupported Value''"

fun export_assignments :: "VarName \<Rightarrow> PatternExpr \<Rightarrow> string" where
  "export_assignments v (UnaryPattern op v1) = 
    ''var '' @ String.explode v1 @ '' = '' @ String.explode v @ ''.getX();
''" |
  "export_assignments v (BinaryPattern op v1 v2) = 
    ''var '' @ String.explode v1 @ '' = '' @ String.explode v @ ''.getX();
var '' @ String.explode v2 @ '' = '' @ String.explode v @ ''.getY();
''" |
  "export_assignments v (ConditionalPattern v1 v2 v3) =
    ''var '' @ String.explode v1 @ '' = '' @ String.explode v @ ''.condition();
var '' @ String.explode v2 @ '' = '' @ String.explode v @ ''.trueValue();
var '' @ String.explode v3 @ '' = '' @ String.explode v @ ''.falseValue();
''" |
  "export_assignments v (ConstantPattern val) =
    ''if ('' @ String.explode v @ ''.getValue() == '' @ export_value val @ '') {''" |
  "export_assignments v (ConstantVarPattern var) =
    ''if ('' @ String.explode v @ ''.getValue() == '' @ String.explode var @ '') {''"

fun export_irexpr :: "IRExpr \<Rightarrow> string" where
  "export_irexpr (UnaryExpr op e1) =
    ''new '' @ unary_op_class op @ ''('' @ export_irexpr e1 @ '')''" |
  "export_irexpr (BinaryExpr op e1 e2) =
    ''new '' @ binary_op_class op @ ''('' @ export_irexpr e1 @ '', '' @ export_irexpr e2 @ '')''" |
  "export_irexpr (ConditionalExpr e1 e2 e3) =
    ''new ConditionalNode('' @ export_irexpr e1 @ '', '' @ export_irexpr e2 @ '', '' @ export_irexpr e3 @ '')''" |
  "export_irexpr (ConstantExpr val) =
    ''new ConstantNode('' @ export_value val @ '')''" |
  "export_irexpr (ConstantVar var) =
    ''new ConstantNode('' @ String.explode var @ '')''" |
  "export_irexpr (VariableExpr v s) = String.explode v"

fun export_condition :: "SideCondition \<Rightarrow> string" where
  "export_condition (IsConstantExpr e) = export_irexpr e @ '' instanceof ConstantNode''" |
  "export_condition (WellFormed s) = ''true''" |
  "export_condition (IsStamp e s) = export_irexpr e @ ''.stamp() == v''" |
  "export_condition (StampUnder e1 e2) = ''stamp under''" |
  "export_condition (UpMaskEquals e m) = ''up mask equals''" |
  "export_condition (DownMaskEquals e m) = ''down mask equals''" |
  "export_condition (UpMaskCancels e1 e2) = ''('' @ export_irexpr e1 @ ''.stamp().upMask() && '' @ export_irexpr e2 @ ''.stamp().upMask()) == 0''" |
  "export_condition (Not sc) = ''!('' @ export_condition sc @ '')''" |
  "export_condition (And sc1 sc2) = ''('' @ export_condition sc1 @ '') && ('' @ export_condition sc2 @ '')''" |
  "export_condition (Empty) = ''true''"

fun export_match :: "MATCH \<Rightarrow> string" where
  "export_match (match v p) = ''if ('' @ String.explode v @ '' instanceof '' @ export_pattern p @ '') {
'' @ export_assignments v p" |
  "export_match (seq m1 m2) = export_match m1 @ '''' @ export_match m2" |
  "export_match (equality v1 v2) = ''if ('' @ String.explode v1 @ '' == '' @ String.explode v2 @ '') {
''" |
  "export_match (negate sc) = ''if (!('' @ export_condition sc @ '')) {
''" |
  "export_match (check sc) = ''if ('' @ export_condition sc @ '') {
''" |
  "export_match noop = ''''"



fun close :: "MATCH \<Rightarrow> string" where
  "close (match v (ConstantPattern val)) = ''
}
}''" |
  "close (match v p) = ''
}''" |
  "close (seq m1 m2) = close m1 @ close m2" |
  "close (equality v1 v2) = ''
}''" |
  "close (negate sc) = ''
}''" |
  "close (check sc) = ''
}''" |
  "close noop = ''''"

fun export_rules :: "Rules \<Rightarrow> string" where
  "export_rules (base e) = ''return '' @ export_irexpr e @ '';''" |
  "export_rules (cond m r) = export_match m @ export_rules r @ close m" |
  "export_rules (r1 else r2) = export_rules r1 @ ''
'' @ export_rules r2"

subsection \<open>Experiments\<close>

definition var :: "string \<Rightarrow> IRExpr" where
  "var v = (VariableExpr (String.implode v) VoidStamp)"

subsubsection \<open>Generated Rules\<close>

text \<open>@{text "\<not>(\<not>x) \<longrightarrow> x"}\<close>
definition NestedNot where
  "NestedNot = generate
    (UnaryExpr UnaryNot (UnaryExpr UnaryNot (var ''x'')))
    (var ''x'')
    (Empty)"

text \<open>@{text "(x - y) + y \<longrightarrow> x"}\<close>
definition RedundantSub where
  "RedundantSub = generate 
    (BinaryExpr BinAdd
      (BinaryExpr BinSub (var ''x'') (var ''y''))
      (var ''y''))
    (var ''x'')
    (Empty)"

text \<open>@{text "x + -e \<longmapsto> x - e"}\<close>
definition AddLeftNegateToSub where
  "AddLeftNegateToSub = generate 
    (BinaryExpr BinAdd
      (var ''x'')
      (UnaryExpr UnaryNeg (var ''e'')))
    (BinaryExpr BinSub (var ''x'') (var ''e''))
    (Empty)"

corollary
  "NestedNot =
   (MATCH.match STR ''e'' (UnaryPattern UnaryNot STR ''a'') &&
    (MATCH.match STR ''a'' (UnaryPattern UnaryNot STR ''az'') && noop) && check Empty) ?
      base (VariableExpr STR ''az'' VoidStamp)"
  by eval

corollary
  "RedundantSub =
   (MATCH.match STR ''e'' (BinaryPattern BinAdd STR ''a'' STR ''b'') &&
    (MATCH.match STR ''a'' (BinaryPattern BinSub STR ''az'' STR ''bz'') && noop && noop) &&
      STR ''bz'' == STR ''b'' && check Empty) ?
        base (VariableExpr STR ''az'' VoidStamp)"
  by eval

corollary
  "AddLeftNegateToSub =
   (MATCH.match STR ''e'' (BinaryPattern BinAdd STR ''a'' STR ''b'') && noop &&
    (MATCH.match STR ''b'' (UnaryPattern UnaryNeg STR ''az'') && noop) && check Empty) ?
      base (BinaryExpr BinSub 
            (VariableExpr STR ''a'' VoidStamp)
            (VariableExpr STR ''az'' VoidStamp))"
  by eval


subsubsection \<open>Rule Application\<close>
text \<open>@{text "\<not>(\<not>1)"}\<close>
definition NestedNot_ground where
  "NestedNot_ground = (UnaryExpr UnaryNot (UnaryExpr UnaryNot (ConstantExpr (IntVal 32 1))))"

text "1"
definition NestedNot_result where
  "NestedNot_result = (ConstantExpr (IntVal 32 1))"

text "(15 - 10) + 10"
definition RedundantSub_ground where
  "RedundantSub_ground = (BinaryExpr BinAdd 
          (BinaryExpr BinSub (ConstantExpr (IntVal 32 15)) (ConstantExpr (IntVal 32 10)))
          (ConstantExpr (IntVal 32 10)))"

text "15"
definition RedundantSub_result where
  "RedundantSub_result = (ConstantExpr (IntVal 32 15))"

text "10 - (-15)"
definition AddLeftNegateToSub_ground where
  "AddLeftNegateToSub_ground = (BinaryExpr BinAdd 
          (ConstantExpr (IntVal 32 10))
          (UnaryExpr UnaryNeg (ConstantExpr (IntVal 32 15))))"

text "10 + 15"
definition AddLeftNegateToSub_result where
  "AddLeftNegateToSub_result = (BinaryExpr BinSub
          (ConstantExpr (IntVal 32 10))
          (ConstantExpr (IntVal 32 15)))"


(*
value "eval_rules NestedNot (start_unification NestedNot_ground)"
corollary
  "eval_rules NestedNot (start_unification NestedNot_ground)
    = Some NestedNot_result"
  by eval

corollary
  "eval_rules RedundantSub (start_unification RedundantSub_ground)
    = Some RedundantSub_result"
  by eval

corollary
  "eval_rules AddLeftNegateToSub (start_unification RedundantSub_ground) = None"
  by eval

corollary
  "eval_rules AddLeftNegateToSub (start_unification AddLeftNegateToSub_ground)
    = Some AddLeftNegateToSub_result"
  by eval

subsubsection \<open>Rule Combinations\<close>

corollary
  "eval_rules (RedundantSub else AddLeftNegateToSub) (start_unification RedundantSub_ground)
    = Some RedundantSub_result"
  by eval

corollary
  "eval_rules (choice [RedundantSub, AddLeftNegateToSub]) (start_unification RedundantSub_ground)
    = Some RedundantSub_result"
  by eval

corollary
  "eval_rules (RedundantSub else AddLeftNegateToSub) (start_unification AddLeftNegateToSub_ground)
    = Some AddLeftNegateToSub_result"
  by eval

corollary
  "eval_rules (AddLeftNegateToSub else RedundantSub) (start_unification RedundantSub_ground)
    = Some RedundantSub_result"
  by eval

corollary
  "eval_rules (AddLeftNegateToSub else RedundantSub) (start_unification AddLeftNegateToSub_ground)
    = Some AddLeftNegateToSub_result"
  by eval
*)

subsubsection \<open>Rule Optimization\<close>

value "combine_conditions (lift_match (eliminate_noop (choice [NestedNot, RedundantSub, AddLeftNegateToSub])))"

corollary
  "lift_match (RedundantSub else AddLeftNegateToSub) =
  (MATCH.match STR ''e'' (BinaryPattern BinAdd STR ''a'' STR ''b'') ?
   (MATCH.match STR ''a'' (BinaryPattern BinSub STR ''az'' STR ''bz'') ?
    (noop ?
     (noop ?
      (STR ''bz'' == STR ''b'' ? (check Empty ? base (VariableExpr STR ''az'' VoidStamp)))))) else
   MATCH.match STR ''e'' (BinaryPattern BinAdd STR ''a'' STR ''b'') ?
   (noop ?
    (MATCH.match STR ''b'' (UnaryPattern UnaryNeg STR ''az'') ?
     (noop ?
      (check Empty ?
       base
        (BinaryExpr BinSub (VariableExpr STR ''a'' VoidStamp)
          (VariableExpr STR ''az'' VoidStamp)))))))"
  by eval

corollary
  "lift_common (lift_match (RedundantSub else AddLeftNegateToSub)) =
   (MATCH.match STR ''e'' (BinaryPattern BinAdd STR ''a'' STR ''b'') ?
   (MATCH.match STR ''a'' (BinaryPattern BinSub STR ''az'' STR ''bz'') ?
    (noop ?
     (STR ''bz'' == STR ''b'' ? (check Empty ? base (VariableExpr STR ''az'' VoidStamp)))) else
    noop ?
    (MATCH.match STR ''b'' (UnaryPattern UnaryNeg STR ''az'') ?
     (noop ?
      (check Empty ?
       base
        (BinaryExpr BinSub (VariableExpr STR ''a'' VoidStamp)
          (VariableExpr STR ''az'' VoidStamp)))))))"
  by eval

corollary
  "optimized_export (RedundantSub else AddLeftNegateToSub) =
   MATCH.match STR ''e'' (BinaryPattern BinAdd STR ''a'' STR ''b'') ?
    (MATCH.match STR ''a'' (BinaryPattern BinSub STR ''az'' STR ''bz'') ?
     (STR ''bz'' == STR ''b'' ?
      base (VariableExpr STR ''az'' VoidStamp))
    else
    MATCH.match STR ''b'' (UnaryPattern UnaryNeg STR ''az'') ?
     base (BinaryExpr BinSub (VariableExpr STR ''a'' VoidStamp) (VariableExpr STR ''az'' VoidStamp)))"
  by eval

subsubsection \<open>Java Generation\<close>

value "export_rules RedundantSub"
value "export_rules AddLeftNegateToSub"
value "export_rules (RedundantSub else AddLeftNegateToSub)"

value "export_rules (lift_common (lift_match (RedundantSub else AddLeftNegateToSub)))"
value "export_rules (optimized_export (RedundantSub else AddLeftNegateToSub))"

value "lift_match (eliminate_noop (NestedNot else RedundantSub else AddLeftNegateToSub))"
value "export_rules (optimized_export ((RedundantSub else AddLeftNegateToSub) else NestedNot))"
value "export_rules (optimized_export (NestedNot else RedundantSub else AddLeftNegateToSub))"

no_notation cond (infixl "?" 52)
no_notation seq (infixl "&&" 50)

notation And (infixl "&&" 50)

end
