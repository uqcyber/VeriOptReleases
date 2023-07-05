theory TermRewrites
  imports Semantics.IRTreeEvalThms Semantics.TreeToGraphThms Snippets.Snipping
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
snipbegin \<open>PatterExpr\<close>
type_synonym VarName = "String.literal"
type_synonym Vars = "VarName fset"

datatype PatternExpr =
    UnaryPattern IRUnaryOp VarName
  | BinaryPattern IRBinaryOp VarName VarName
  | ConditionalPattern VarName VarName VarName
  | VariablePattern VarName
  | ConstantPattern Value
  | ConstantVarPattern VarName
snipend -


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
  IsBool IRExpr |
  PowerOf2 IRExpr |
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
  "eval_condition (PowerOf2 e) = False" |
  "eval_condition (IsBool e) = ((e = ConstantExpr (IntVal 32 0)) | (e = ConstantExpr (IntVal 32 0)))" |
  
  "eval_condition (Empty) = True" |

  "eval_condition (And sc1 sc2) = ((eval_condition sc1) \<and> (eval_condition sc2))" |
  "eval_condition (Not sc) = (\<not>(eval_condition sc))"


subsection \<open>Match Primitives\<close>
snipbegin \<open>MATCH\<close>
datatype MATCH =
  match VarName PatternExpr |
  equality VarName VarName (infixl "==" 52) |
  andthen MATCH MATCH (infixl "&&" 50) |
  condition SideCondition |
  noop
snipend -

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

snipbegin "matchpattern"
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
snipend -

subsubsection \<open>Match Primitive Semantics\<close>
snipbegin \<open>Subst\<close>
type_synonym Subst = "VarName \<Rightarrow> IRExpr option"
snipend -

snipbegin \<open>evalmatch\<close>
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
          then Some (s(x\<mapsto>xe, y\<mapsto>ye))
          else None) |
      Some _ \<Rightarrow> None |
      None \<Rightarrow> None)" |
  "eval_match (match v (ConditionalPattern c tb fb)) s =
    (case s v of
      Some (ConditionalExpr ce te fe) \<Rightarrow>
        (Some (s(c\<mapsto>ce, tb\<mapsto>te, fb\<mapsto>fe))) |
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
  "eval_match (andthen m1 m2) s =
      (case eval_match m1 s of 
        None \<Rightarrow> None |
        Some s' \<Rightarrow> eval_match m2 s')" |
  "eval_match noop s = Some s" |
  "eval_match (condition sc) s = (if eval_condition sc then Some s else None)" |
  "eval_match _ s = None"
snipend -

subsection \<open>Combining Rules\<close>

snipbegin \<open>Rules\<close>
datatype Rules =
  base IRExpr |
  cond MATCH Rules (infixl "?" 52) |
  else Rules Rules (infixl "else" 50) |
  seq Rules Rules (infixl "\<then>" 49) |
  choice "Rules list"
snipend -

text \<open>Use the scope of a generated match to replace real variable names with aliases in the rewrite result.\<close>
snipbegin \<open>groundresult\<close>
fun ground_result :: "IRExpr \<Rightarrow> Scope \<Rightarrow> IRExpr" where
  "ground_result (UnaryExpr op e) s = 
    UnaryExpr op (ground_result e s)" |
  "ground_result (BinaryExpr op e1 e2) s = 
    BinaryExpr op (ground_result e1 s) (ground_result e2 s)" |
  "ground_result (ConditionalExpr b e1 e2) s = 
    ConditionalExpr (ground_result b s) (ground_result e1 s) (ground_result e2 s)" |
  "ground_result (VariableExpr vn st) (s, m) = 
    (case m vn of None \<Rightarrow> VariableExpr vn st 
                | Some v' \<Rightarrow> VariableExpr v' st)" |
  "ground_result e v = e"
snipend -

fun ground_condition :: "SideCondition \<Rightarrow> Scope \<Rightarrow> SideCondition" where
  "ground_condition (IsConstantExpr p) s = (IsConstantExpr (ground_result p s))" |
  "ground_condition (WellFormed st) s = (WellFormed st)" |
  "ground_condition (IsStamp e st) s = (IsStamp (ground_result e s) st)" |
  "ground_condition (StampUnder e1 e2) s = (StampUnder (ground_result e1 s) (ground_result e2 s))" |
  "ground_condition (UpMaskEquals e m) s = (UpMaskEquals (ground_result e s) m)" |
  "ground_condition (DownMaskEquals e m) s = (DownMaskEquals (ground_result e s) m)" |
  "ground_condition (UpMaskCancels e1 e2) s = (UpMaskCancels (ground_result e1 s) (ground_result e2 s))" |
  "ground_condition (PowerOf2 e) s = (PowerOf2 (ground_result e s))" |
  "ground_condition (IsBool e) s = (IsBool (ground_result e s))" |
  "ground_condition (And sc1 sc2) s = And (ground_condition sc1 s) (ground_condition sc2 s)" |
  "ground_condition (Not sc) s = Not (ground_condition sc s)" |
  "ground_condition (Empty) s = Empty"

snipbegin \<open>generate\<close>
fun generate :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> SideCondition \<Rightarrow> Rules" where
  "generate p r sc = 
    (let (s, m) = match_pattern p STR ''e'' ({||}, (\<lambda>x. None))
     in ((m && condition (ground_condition sc s)) ? (base (ground_result r s))))"
snipend -

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
  \<comment> \<open>Evaluate the result\<close>
  "eval_rules (base e) u (ground_expr e u)" |

  \<comment> \<open>Evaluate a condition\<close>
  "\<lbrakk>eval_match m u = Some u';
    eval_rules r u' e\<rbrakk>
   \<Longrightarrow> eval_rules (cond m r) u e" |
  "\<lbrakk>eval_match m u = None\<rbrakk>
   \<Longrightarrow> eval_rules (cond m r) u None" |

  \<comment> \<open>Evaluate else\<close>
  "\<lbrakk>eval_rules r1 u (Some r)\<rbrakk>
   \<Longrightarrow> eval_rules (r1 else r2) u (Some r)" |
  "\<lbrakk>eval_rules r1 u None;
    eval_rules r2 u e\<rbrakk>
   \<Longrightarrow> eval_rules (r1 else r2) u e" |

  \<comment> \<open>Evaluate choice\<close>
  "\<lbrakk>rule \<in> set rules;
    eval_rules rule u (Some r)\<rbrakk>
   \<Longrightarrow> eval_rules (choice rules) u (Some r)" |
  "\<lbrakk>\<forall> rule \<in> set rules. eval_rules rule u None\<rbrakk>
   \<Longrightarrow> eval_rules (choice rules) u None" |
  "\<lbrakk>rules = []\<rbrakk>
   \<Longrightarrow> eval_rules (choice rules) u None" |

  \<comment> \<open>Evaluate sequential\<close>
  "\<lbrakk>eval_rules r1 u (Some e');
    eval_rules r2 (u(STR ''e'' \<mapsto> e')) r\<rbrakk>
   \<Longrightarrow> eval_rules (r1 \<then> r2) u r" |
  "\<lbrakk>eval_rules r1 u None;
    eval_rules r2 u r\<rbrakk>
   \<Longrightarrow> eval_rules (r1 \<then> r2) u r"

declare [[show_types=false,show_sorts=false]]
snipbegin \<open>rules-semantics\<close>
text \<open>
\induct{@{thm[mode=Rule] eval_rules.intros(1) [no_vars]}}{evalrules:base}
\induct{@{thm[mode=Rule] eval_rules.intros(2) [no_vars]}}{evalrules:cond-some}
\induct{@{thm[mode=Rule] eval_rules.intros(3) [no_vars]}}{evalrules:cond-none}
\induct{@{thm[mode=Rule] eval_rules.intros(4) [no_vars]}}{evalrules:else-some}
\induct{@{thm[mode=Rule] eval_rules.intros(5) [no_vars]}}{evalrules:else-none}
\induct{@{thm[mode=Rule] eval_rules.intros(6) [no_vars]}}{evalrules:choice-some}
\induct{@{thm[mode=Rule] eval_rules.intros(7) [no_vars]}}{evalrules:choice-none}
\induct{@{thm[mode=Rule] eval_rules.intros(8) [no_vars]}}{evalrules:choice-empty}
\induct{@{thm[mode=Rule] eval_rules.intros(9) [no_vars]}}{evalrules:seq-some}
\induct{@{thm[mode=Rule] eval_rules.intros(10) [no_vars]}}{evalrules:seq-none}
\<close>
snipend -

inductive_cases baseE: "eval_rules (base e') u e"
inductive_cases condE: "eval_rules (cond m r) u e"
inductive_cases elseE: "eval_rules (r1 else r2) u e"
inductive_cases choiceE: "eval_rules (choice r) u e"
inductive_cases seqE: "eval_rules (r1 \<then> r2) u e"

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
  using seq_det_rhs by force+

(*lemma monotonic_choice:
  assumes "\<forall> r e. eval_rules r u e = eval_rules (f r) u e"
  shows "eval_rules (choice rs) u e = eval_rules (choice (map f rs)) u e"
  apply (induction rs) apply simp using choiceE assms sorry
  subgoal for a rs apply (induction "choice rs" u rule: eval_rules.induct)*)

fun optimize_match :: "(MATCH \<Rightarrow> MATCH) \<Rightarrow> Rules \<Rightarrow> Rules" where
  "optimize_match f (base e) = base e" |
  "optimize_match f (m ? r) = f m ? optimize_match f r" |
  "optimize_match f (r1 else r2) = (optimize_match f r1 else optimize_match f r2)" |
  "optimize_match f (choice rules) = choice (map (optimize_match f) rules)" |
  "optimize_match f (r1 \<then> r2) = (optimize_match f r1 \<then> optimize_match f r2)"

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
  "eliminate_noop (choice rules) = choice (map eliminate_noop rules)" |
  "eliminate_noop (r1 \<then> r2) = (eliminate_noop r1 \<then> eliminate_noop r2)"


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
  by (smt (verit) Rules.distinct(11) Rules.distinct(15) Rules.distinct(19) Rules.distinct(5) Rules.inject(4) eliminate_noop.simps(5) eval_rules.simps)

fun elim_empty :: "MATCH \<Rightarrow> MATCH" where
  "elim_empty (condition Empty) = noop" |
  "elim_empty (m1 && m2) = (elim_empty m1 && elim_empty m2)" |
  "elim_empty m = m"

lemma empty_check_semantics:
  "eval_match (condition Empty) s = eval_match noop s"
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
  "eliminate_empty (choice rules) = choice (map eliminate_empty rules)" |
  "eliminate_empty (r1 \<then> r2) = (eliminate_empty r1 \<then> eliminate_empty r2)"

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
  by (smt (verit) Rules.distinct(11) Rules.distinct(15) Rules.distinct(19) Rules.distinct(5) Rules.inject(4) eliminate_empty.simps(5) eval_rules.simps)

fun combined_size :: "Rules \<Rightarrow> nat" where
  "combined_size (m ? r) = (2 * size m) + combined_size r" |
  "combined_size (base e) = 0" |
  "combined_size (r1 else r2) = combined_size r1 + combined_size r2" |
  "combined_size (choice (rule # rules)) = 1 + combined_size rule + combined_size (choice rules)" |
  "combined_size (choice []) = 1" |
  "combined_size (r1 \<then> r2) = combined_size r1 + combined_size r2"

value "size (m ? r)"

function (sequential) lift_match :: "Rules \<Rightarrow> Rules" where
  "lift_match (r1 else r2) = ((lift_match r1) else (lift_match r2))" |
  "lift_match (choice rules) = choice (map lift_match rules)" |
  "lift_match ((m1 && m2) ? r) = (lift_match (m1 ? (m2 ? r)))" |
  "lift_match (m ? r) = m ? (lift_match r)" |
  "lift_match (base e) = (base e)" |
  "lift_match (r1 \<then> r2) = (lift_match r1 \<then> lift_match r2)"
  by pat_completeness auto
termination lift_match
  apply (relation "measures [combined_size, size]") apply auto[1]
  apply auto[1] apply auto[1] apply simp
  subgoal for rules x apply (induction rules) apply simp by fastforce
  apply simp subgoal for m2 r apply (cases m2) by (simp add: lift_match.psimps(4))
        apply simp+
  apply blast
  by auto

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
  apply (smt (verit, ccfv_threshold) eval_rules.intros(4) eval_rules.intros(5))
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
   apply simp+
  by (smt (verit) Rules.distinct(11) Rules.distinct(15) Rules.distinct(19) Rules.distinct(5) Rules.inject(4) eval_rules.simps)

(*
fun lift_common :: "Rules \<Rightarrow> Rules" where
  "lift_common (m1 ? r1 else m2 ? r2) = 
    (if m1 = m2
      then m1 ? (lift_common (r1 else r2))
      else (lift_common (m1 ? r1) else lift_common (m2 ? r2)))" |
  "lift_common (r1 else r2) = ((lift_common r1) else (lift_common r2))" |
  "lift_common (m ? r) = (m ? (lift_common r))" |
  "lift_common (base e) = base e"*)

fun   join_conditions :: "Rules \<Rightarrow> Rules option" where
  "join_conditions (m1 ? r1 else m2 ? r2) = 
    (if m1 = m2
      then Some (m1 ? (r1 else r2)) else None)" |
  (*"join_conditions (m1 ? (m2 ? r1)) = 
    (if m1 = m2
      then Some ((m1 ? r1)) else None)" |*)
  "join_conditions r = None"

lemma join_conditions_shrinks:
  "join_conditions r = Some r' \<Longrightarrow> size r' < size r"
  apply (induction r rule: join_conditions.induct) 
  apply (metis Rules.size(7) Rules.size(8) Suc_le_eq add.left_commute add.right_neutral antisym_conv1 join_conditions.simps(1) le_simps(1) option.distinct(1) option.sel plus_nat.simps(2))
   apply (metis One_nat_def Rules.size(7) join_conditions.simps(2) less_add_same_cancel1 less_numeral_extra(1) option.discI option.inject)
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
  "lift_common (m ? r) = (m ? lift_common r)" |
  (*"lift_common (m ? r) = (
    case join_conditions (m ? r) 
    of Some r' \<Rightarrow> lift_common r' |
       None \<Rightarrow> (m ? lift_common r))" |*)
  "lift_common (choice rules) = choice (map lift_common rules)" |
  "lift_common (base e) = base e" |
  "lift_common (r1 \<then> r2) = (lift_common r1 \<then> lift_common r2)"
  using combined_size.cases 
  apply (smt (verit, ccfv_threshold))
  by simp+
termination
  apply (relation "measures [size]") apply auto[1]
    apply simp subgoal for r1 r2 apply (induction r1 rule: join_conditions.induct) by simp+
   apply auto[1] using join_conditions_shrinks apply fastforce+ 
  apply auto[1] using join_conditions_shrinks apply (simp add: le_imp_less_Suc size_list_estimation')
  by simp+

fun pattern_variables :: "PatternExpr \<Rightarrow> String.literal set" where
  "pattern_variables (UnaryPattern op e) = {e}" |
  "pattern_variables (BinaryPattern op e1 e2) = {e1, e2}" |
  "pattern_variables (ConditionalPattern c t f) = {c, t, f}" |
  "pattern_variables (VariablePattern v) = {}" |
  "pattern_variables (ConstantPattern v) = {}" |
  "pattern_variables (ConstantVarPattern v) = {}"

fun def_vars :: "MATCH \<Rightarrow> String.literal set" where
  "def_vars (match v p) = pattern_variables p" |
  "def_vars (equality e1 e2) = {e1, e2}" |
  "def_vars (m1 && m2) = def_vars m1 \<union> def_vars m2" |
  "def_vars (condition c) = {}" |
  "def_vars noop = {}"

fun use_vars :: "MATCH \<Rightarrow> String.literal set" where
  "use_vars (match v p) = {v}" |
  "use_vars (equality e1 e2) = {}" |
  "use_vars (m1 && m2) = use_vars m1 \<union> (use_vars m2 - def_vars m1)" |
  "use_vars (condition c) = {}" |
  "use_vars noop = {}"

fun valid_match :: "MATCH \<Rightarrow> bool" where
  "valid_match (match v (UnaryPattern op e)) = (v \<noteq> e)" |
  "valid_match (match v (BinaryPattern op e1 e2)) = (v \<noteq> e1 \<and> v \<noteq> e2 \<and> e1 \<noteq> e2)" |
  "valid_match (match v (ConditionalPattern c t f)) = (v \<noteq> c \<and> v \<noteq> t \<and> v \<noteq> f \<and> c \<noteq> t \<and> c \<noteq> f \<and> t \<noteq> f)" |
  "valid_match (m1 && m2) = (valid_match m1 \<and> valid_match m2 \<and> use_vars m1 \<inter> def_vars m2 = {})" |
  "valid_match _ = True"

fun valid_rules :: "Rules \<Rightarrow> bool" where
  "valid_rules (m ? r) = (valid_match m \<and> valid_rules r)" |
  "valid_rules (r1 else r2) = (valid_rules r1 \<and> valid_rules r2)" |
  "valid_rules (r1 \<then> r2) = (valid_rules r1 \<and> valid_rules r2)" |
  "valid_rules (choice rules) = (\<forall>r \<in> set rules. valid_rules r)" |
  "valid_rules _ = True"

experiment begin
lemma match_def_affect:
  assumes "eval_match m u = Some a"
  shows "\<forall>v. v \<notin> def_vars m \<longrightarrow> u v = a v"
using assms proof (induction m u arbitrary: a rule: eval_match.induct)
  case (1 v op1 x s)
  have "\<exists>e. a = s(x\<mapsto>e)"
    by (smt (verit, ccfv_threshold) "1" IRExpr.case_eq_if eval_match.simps(1) option.case_eq_if option.distinct(1) option.inject)
  then show ?case
    unfolding def_vars.simps by auto
next
  case (2 v op1 x y s)
  have "\<exists>e1 e2. a = s(y\<mapsto>e1, x\<mapsto>e2)"
    by (smt (verit) "2" IRExpr.case_eq_if eval_match.simps(2) fun_upd_twist option.case_eq_if option.distinct(1) option.sel)
  then show ?case
    by fastforce
next
  case (3 v c tb fb s)
  have "\<exists>e1 e2 e3. a = s(c\<mapsto>e1, tb\<mapsto>e2, fb\<mapsto>e3)"
    by (smt (verit, best) "3" IRExpr.case_eq_if eval_match.simps(3) option.case_eq_if option.distinct(1) option.inject)  
  then show ?case
    by force
next
  case (4 v c1 s)
  then show ?case
    by (smt (verit, ccfv_SIG) IRExpr.case_eq_if eval_match.simps(4) option.case_eq_if option.distinct(1) option.sel)
next
  case (5 v1 v2 s)
  then show ?case
    by (metis eval_match.simps(5) option.distinct(1) option.sel)
next
  case (6 m1 m2 s)
  then show ?case
    by (metis (no_types, lifting) UnCI def_vars.simps(3) eval_match.simps(6) option.case_eq_if option.exhaust_sel)
    (*by (smt (verit) UnCI def_vars.simps(3) eval_match.simps(6) option.case_eq_if option.exhaust_sel)*)
next
  case (7 s)
  then show ?case
    by simp
next
  case (8 sc s)
  then show ?case
    by (metis eval_match.simps(8) option.distinct(1) option.sel)
next
  case ("9_1" v vb s)
  then show ?case
    by simp
next
  case ("9_2" v vb s)
  then show ?case
    by simp
qed

lemma use_def:
  assumes "valid_match m"
  shows "def_vars m \<inter> use_vars m = {}"
  using assms apply (induction m)
  subgoal for v p apply (cases p) by simp+
     apply simp
  apply auto[1]
  by simp+

lemma match_use_affect:
  assumes "eval_match m u = Some a"
  assumes "valid_match m"
  shows "\<forall>v \<in> use_vars m. u v = a v"
  using assms apply (induction m u arbitrary: u a rule: eval_match.induct)
  by (meson disjoint_iff_not_equal match_def_affect use_def)+
(*  case (1 v op1 x s)
  then show ?case
    by (meson disjoint_iff_not_equal match_def_affect use_def)
next
  case (2 v op1 x y s)
  then show ?case
    by (meson disjoint_iff_not_equal match_def_affect use_def)
next
  case (3 v c tb fb s)
  then show ?case
    by (meson disjoint_iff_not_equal match_def_affect use_def)
next
  case (4 v c1 s)
  then show ?case
    by (meson disjoint_iff_not_equal match_def_affect use_def)
next
  case (5 v1 v2 s)
  then show ?case
    by (meson disjoint_iff_not_equal match_def_affect use_def)
next
  case (6 m1 m2 s)
  then show ?case
    by (meson disjoint_iff_not_equal match_def_affect use_def)
  have drops: "\<exists>u a. (\<exists>s x2. eval_match m1 s = Some x2) \<longrightarrow>
    eval_match m2 u = Some a \<longrightarrow> valid_match m2 \<longrightarrow> (\<forall>v. v \<in> use_vars m2 \<longrightarrow> u v = a v)"
    by blast
  obtain a' where a': "eval_match m1 u = Some a'"
    using "6.prems"(1) by fastforce
  then have m1: "\<forall>v. v \<in> use_vars m1 \<longrightarrow> u v = a' v"
    using "6.IH"(1) "6.prems"(2) valid_match.simps(4) by blast
  have validm2: "valid_match m2"
    using "6.prems"(2) by auto
  obtain a'' where a'': "eval_match m2 a' = Some a''"
    using "6.prems"(1) \<open>eval_match m1 u = Some a'\<close> by fastforce
  then have "\<forall>v. v \<in> use_vars m2 \<longrightarrow> a' v = a'' v"
    using drops a' validm2
    by (meson disjoint_iff match_def_affect use_def)
  then show ?case unfolding use_vars.simps using m1 6(3) unfolding eval_match.simps
    using a' a''
    by (metis "6.prems"(2) disjoint_iff eval_match.simps(6) match_def_affect use_def use_vars.simps(3))
next
  case (7 s)
  then show ?case sorry
next
  case (8 sc s)
  then show ?case sorry
next
  case ("9_1" v vb s)
  then show ?case sorry
next
  case ("9_2" v vb s)
  then show ?case sorry
qed*)


lemma use_unchange:
  assumes "eval_match m u = Some a"
  assumes "eval_match m u' = Some a'"
  assumes "valid_match m"
  assumes "\<forall>v \<in> use_vars m. u v = u' v"
  shows "\<forall>v \<in> def_vars m. a v = a' v"
  using assms proof (induction m u arbitrary: u a u' a' rule: eval_match.induct)
  case (1 v op1 x s)
  then show ?case
    by (smt (verit) IRExpr.case_eq_if def_vars.simps(1) eval_match.simps(1) insertCI map_upd_Some_unfold option.case_eq_if option.sel pattern_variables.simps(1) singletonD use_vars.simps(1))
next
  case (2 v op1 x y s)
  then show ?case sorry
next
  case (3 v c tb fb s)
  then show ?case sorry
next
  case (4 v c1 s)
  then show ?case sorry
next
  case (5 v1 v2 s)
  then show ?case sorry
next
  case (6 m1 m2 s)
  obtain a'' where m1eval: "eval_match m1 u = Some a''"
    using "6.prems"(1)
    by fastforce
  obtain a''' where m1eval': "eval_match m1 u' = Some a'''"
    using "6.prems"(2)
    by fastforce
  have "valid_match m1"
    using "6.prems"(3) valid_match.simps(4) by blast
  then have "\<forall>v \<in> use_vars m1. u v = u' v"
    using m1eval match_use_affect
    by (simp add: "6.prems"(4))
  then have m1def: "\<forall>v\<in>def_vars m1. a'' v = a''' v"
    using "6.IH"(1) \<open>valid_match m1\<close> m1eval m1eval' by presburger
  have drops: "\<forall>u u' a a'. \<exists>s x2. (eval_match m1 s = Some x2 \<longrightarrow>
    eval_match m2 u = Some a \<longrightarrow>
    eval_match m2 u' = Some a' \<longrightarrow>
    valid_match m2 \<longrightarrow> (\<forall>v\<in>use_vars m2. u v = u' v) \<longrightarrow> (\<forall>v\<in>def_vars m2. a v = a' v))"
    by (meson "6.IH"(2))
  obtain b'' where m2eval: "eval_match m2 a'' = Some b''"
    using "6.prems"(1) m1eval by auto
  obtain b''' where m2eval': "eval_match m2 a''' = Some b'''"
    using "6.prems"(2) m1eval' by force
  have validm2: "valid_match m2"
    using "6.prems"(3) valid_match.simps(4) by blast
  then have m1use: "\<forall>v \<in> use_vars m2. a'' v = a''' v"
    by (metis "6.prems"(4) Diff_iff UnI2 m1def m1eval m1eval' match_def_affect use_vars.simps(3))
  then have m1def: "\<forall>v\<in>def_vars m2. b'' v = b''' v" 
    using 6 m1eval m2eval m2eval' validm2 apply simp sorry
  then show ?case unfolding valid_match.simps sorry
    (*by (smt (verit, best) "6.IH"(1) "6.prems"(1) "6.prems"(2) Un_iff \<open>\<forall>v\<in>use_vars m1. u v = u' v\<close> \<open>valid_match m1\<close> def_vars.simps(3) eval_match.simps(6) m1eval m1eval' m2eval m2eval' match_def_affect option.inject option.simps(5))
*)next
  case (7 s)
  then show ?case sorry
next
  case (8 sc s)
  then show ?case sorry
next
  case ("9_1" v vb s)
  then show ?case sorry
next
  case ("9_2" v vb s)
  then show ?case sorry
qed

lemma match_use_idemp:
  assumes "eval_match m u = Some a"
  assumes "valid_match m"
  shows "eval_match m a = Some a"
  using assms proof (induction m u arbitrary: u a rule: eval_match.induct)
  case (1 v op1 x s)
  then have "u v = a v"
    by (metis insertI1 match_use_affect use_vars.simps(1))
  then show ?case
    using 1(1) unfolding eval_match.simps
    by (smt (verit) IRExpr.case_eq_if fun_upd_idem_iff map_upd_Some_unfold option.case_eq_if option.sel)
next
  case (2 v op1 x y s)
  then show ?case sorry
next
  case (3 v c tb fb s)
  then show ?case sorry
next
  case (4 v c1 s)
  then show ?case sorry
next
  case (5 v1 v2 s)
  then show ?case sorry
next
  case (6 m1 m2 s)
  (*have "\<forall>v. v \<in> use_vars m1 \<longrightarrow> s v = a v"
    by (simp add: "6.prems"(1))
  have "\<forall>v. v \<in> use_vars m2 \<longrightarrow> s v = a v"
    by (simp add: "6.prems"(1))*)
  obtain a' where m1eval: "eval_match m1 u = Some a'"
    using "6.prems"(1)
    by fastforce
  have "valid_match m1"
    using "6.prems"(2) by auto
  then have "\<forall>v \<in> use_vars m1. u v = a' v"
    using m1eval match_use_affect by blast
  then have m1idem: "eval_match m1 a' = Some a'"
    using "6.IH"(1) \<open>valid_match m1\<close> m1eval by blast
  have drops: "\<forall>u a x2. (\<exists>s. (eval_match m1 s = Some x2 \<longrightarrow>
    eval_match m2 u = Some a \<longrightarrow>
    valid_match m2 \<longrightarrow> eval_match m2 a = Some a))"
    using "6"(2)
    by blast
  obtain a'' where m2eval: "eval_match m2 a' = Some a''"
    using "6.prems"(1) m1eval by auto
  have validm2: "valid_match m2"
    using "6.prems"(2) by auto
  then have m1use: "\<forall>v \<in> use_vars m2. a' v = a'' v"
    using m2eval
    by (simp add: match_use_affect)
  have existm1: "(\<exists>s x2. eval_match m1 s = Some x2)"
    using \<open>eval_match m1 a' = Some a'\<close> by auto
  have m2idem: "eval_match m2 a'' = Some a''"
    using drops existm1 m2eval validm2 m1eval sorry
    (*by blast
    by (simp add: "6.IH"(2) \<open>valid_match m2\<close> m1eval m2eval)*)
  have "a = a''"
    using "6.prems"(1) m1eval m2eval by auto
  (*have "eval_match m1 a'' = Some a''"
    using 6(4) unfolding valid_match.simps using use_unchange sledgehammer*)
  have "eval_match (m1 && m2) a'' = Some a''"
    unfolding eval_match.simps using m1eval m1idem m2eval m2idem using use_unchange sorry
    (*by (simp add: \<open>eval_match m1 a'' = Some a''\<close>)*)
  then show ?case using 6(3) m1eval m1idem m2idem
    unfolding eval_match.simps valid_match.simps sorry
next
  case (7 s)
  then show ?case sorry
next
  case (8 sc s)
  then show ?case sorry
next
  case ("9_1" v vb s)
  then show ?case sorry
next
  case ("9_2" v vb s)
  then show ?case sorry
qed

lemma disjoint_match_use:
  assumes "valid_match m"
  shows "use_vars m \<inter> def_vars m = {}"
  using assms apply (induction m)
  unfolding use_vars.simps def_vars.simps
  subgoal for x1 x2
    apply (cases x2) by simp+
     apply simp+
  sorry

lemma idempotent_match:
  assumes "valid_match m"
  assumes "eval_match m u = Some a"
  shows "eval_match m a = Some a"
  using assms match_def_affect match_use_idemp disjoint_match_use
  by (metis (no_types, opaque_lifting) disjoint_iff_not_equal) (*
  using assms proof (induction m u arbitrary: u a rule: eval_match.induct)
  case (1 v op1 x s)
  then obtain e where e: "u v = Some (UnaryExpr op1 e)"
    by (smt (verit) IRExpr.case_eq_if IRExpr.sel(1) eval_match.simps(1) is_UnaryExpr_def map_upd_Some_unfold option.case_eq_if option.distinct(1) option.exhaust_sel option.sel valid_match.simps(1))
    then have "a = u(x:=Some e)"
        using "1.prems"(2) by auto
    then show ?case
      using "1.prems"(1) e by auto
next
  case (2 v op1 x y s)
  then show ?case sorry
  (*then obtain e1 e2 where e: "u v = Some (BinaryExpr op1 e1 e2)"
    by (smt (verit, del_insts) IRExpr.case_eq_if IRExpr.simps(66) eval_match.simps(2) is_BinaryExpr_def option.case_eq_if option.distinct(1) option.exhaust_sel)
  then have "s = u(x:=Some e1, y:=Some e2)"
    using "2.prems"(2) by auto
  then show ?case
    using "2.prems"(1) e by auto*)
next
  case (3 v c tb fb s)
  then show ?case sorry
  (*then obtain cv t f where e: "u v = Some (ConditionalExpr cv t f)"
    unfolding eval_match.simps
    by (smt (verit, del_insts) IRExpr.split_sel_asm is_none_code(2) is_none_simps(1) option.case_eq_if option.exhaust_sel)
  then have "s = u(c:=Some cv, tb:=Some t, fb:=Some f)"
    using "3.prems"(2) by auto
  then show ?case
    using "3.prems"(1) e by auto*)
next
  case (4 v c1 s)
  then show ?case unfolding eval_match.simps
    by (smt (verit) IRExpr.case_eq_if option.case_eq_if option.sel)
next
  case (5 v1 v2 s)
  then show ?case unfolding eval_match.simps
    by (metis option.inject)
next
  case (6 m1 m2 s)
  (*obtain a' u where a': "eval_match m1 u = Some a'"
    using "6.prems"(2) by fastforce
  then have s1: "eval_match m1 u = Some a'"
    using "6.IH"(1) "6.prems"(1) valid_match.simps(4) by blast
  obtain a'' where a'': "eval_match m2 u = Some a''"
    using "6.prems"(2) \<open>eval_match m1 u = Some a'\<close> by auto
  then have s2: "eval_match m2 a'' = Some a''"
    using "6.IH"(2) "6.prems"(1) \<open>eval_match m1 s = Some a'\<close> valid_match.simps(4) by blast
  have "a = a''"
    using "6.prems"(2) a' a'' by auto
  have "eval_match m1 a = Some a"
    sorry*)
  then show ?case sorry (*using "6.prems"(2) unfolding eval_match.simps
    by (simp add: \<open>a = a''\<close> s2)*)
next
  case (7 s)
  then show ?case sorry
next
  case (8 sc s)
  then show ?case sorry
next
  case ("9_1" v vb s)
  then show ?case sorry
next
  case ("9_2" v vb s)
  then show ?case sorry
qed
*)

lemma match_eq:
  assumes "valid_match m"
  shows "eval_match (m && m) u = eval_match m u"
  using assms
  by (simp add: idempotent_match option.case_eq_if)
(*
proof (cases "eval_match m u")
  case None
  then show ?thesis by simp
next
  case (Some a)
  then have "eval_match m a = eval_match m u"
    using assms proof (induction m a arbitrary: a rule: eval_match.induct)
    case (1 v op1 x s)
      then show ?case
      proof (cases "\<exists>e. u v = Some (UnaryExpr op1 e)")
        case True
        obtain e where "a x = Some e"
          using "1" True by fastforce
        then have "x \<noteq> v"
          using assms
          using "1.prems"(2) by force
        then have "a = u(x:=Some e)"
          using "1.prems"(1) True \<open>a x = Some e\<close> by force
        then show ?thesis unfolding eval_match.simps
          using True \<open>x \<noteq> v\<close> by force
      next
        case False
        then have "eval_match (MATCH.match v (UnaryPattern op1 x)) u = None"
          unfolding eval_match.simps
          by (smt (verit, best) IRExpr.case_eq_if IRExpr.sel(1) is_UnaryExpr_def option.case_eq_if option.exhaust_sel)
        then show ?thesis
          using "1.prems"(1) by auto
      qed
    next
      case (2 v op1 x y s)
      then show ?case
      proof (cases "\<exists>e1 e2. u v = Some (BinaryExpr op1 e1 e2)")
        case True
        then obtain e1 e2 where e: "u v = Some (BinaryExpr op1 e1 e2)"
          by blast
        then have e2: "a y = Some e2"
          using "2"(1) unfolding eval_match.simps
          by auto
        have e1: "a x = Some e1"
          using "2.prems"(1) "2.prems"(2) e by auto
        then have "x \<noteq> v \<and> y \<noteq> v"
          using assms
          using "2.prems"(2) by auto
        then have "a = (u(y:=Some e2))(x:=Some e1)"
          using e1 e2 "2"(1) unfolding eval_match.simps using True
          by (smt (verit, ccfv_threshold) IRExpr.simps(66) e fun_upd_idem fun_upd_other fun_upd_twist map_add_subsumed1 map_add_upd map_le_refl option.inject option.simps(5))
        then show ?thesis unfolding eval_match.simps
          by (smt (z3) "2.prems"(1) IRExpr.simps(66) \<open>x \<noteq> v \<and> y \<noteq> v\<close> e e2 eval_match.simps(2) fun_upd_apply fun_upd_triv map_add_subsumed2 map_le_refl option.case_eq_if option.sel)
      next
        case False
        then have "eval_match (MATCH.match v (BinaryPattern op1 x y)) u = None"
          unfolding eval_match.simps
          using IRExpr.case_eq_if IRExpr.sel(2) is_BinaryExpr_def option.case_eq_if option.exhaust_sel
          by (smt (verit) IRExpr.simps(66))
        then show ?thesis
          using "2.prems"(1) by force
      qed
    next
      case (3 v c tb fb s)
      then show ?case
      proof (cases "\<exists>cv t f. u v = Some (ConditionalExpr cv t f)")
        case True
        then obtain cv t f where e: "u v = Some (ConditionalExpr cv t f)"
          by blast
        then have f: "a fb = Some f"
          using "3.prems"(1) unfolding eval_match.simps
          by force
        then have t: "a tb = Some t"
          using "3.prems"(1,2) unfolding eval_match.simps
          using e by auto
        then have c: "a c = Some cv"
          using "3.prems"(1,2) unfolding eval_match.simps
          using e by auto
        then have "c \<noteq> v \<and> tb \<noteq> v \<and> tb \<noteq> v"
          using assms
          using "3.prems"(2) by auto
        then have "a = ((u(c:=Some cv))(tb:=Some t))(fb:=Some f)"
          using c t f "3"(1) unfolding eval_match.simps using True
          using e by auto
        then show ?thesis unfolding eval_match.simps
          using "3.prems"(2) e by auto
      next
        case False
        then have "eval_match (MATCH.match v (ConditionalPattern c tb fb)) u = None"
          unfolding eval_match.simps
          using IRExpr.split_sels(2) is_none_code(2) is_none_simps(1) option.case_eq_if option.exhaust_sel
          by (smt (verit, del_insts))
        then show ?thesis
          using "3.prems"(1) by force
      qed
    next
      case (4 v c1 s)
      then show ?case unfolding eval_match.simps
        using IRExpr.case_eq_if option.case_eq_if option.sel
        by (smt (verit))
    next
      case (5 v1 v2 s)
      then show ?case
        by (metis eval_match.simps(5) option.sel)
    next
      case (6 m1 m2 s)
      then show ?case
      proof (cases "eval_match m1 u")
        case None
        then show ?thesis
          using "6.prems"(1) by force
      next
        case (Some a')
        then show ?thesis sorry
      qed
        (*
      proof (cases "eval_match (m1 && m2) u")
        case None
        then show ?thesis
          using "6.prems"(1) by auto
      next
        case (Some a)
        have "eval_match m1 u = Some s" sorry
        then show ?thesis sorry
      qed*)
    next
      case (7 s)
      then show ?case sorry
    next
      case (8 sc s)
      then show ?case sorry
    next
      case ("9_1" v vb s)
      then show ?case sorry
    next
      case ("9_2" v vb s)
      then show ?case sorry
    qed
  then show ?thesis
    by (simp add: Some)
qed*)
end
(*
      case (match x1 x2)
      then show ?case sorry
    next
      case (equality x1 x2)
      then have "a = u"
        using Some unfolding eval_match.simps
        by (metis option.distinct(1) option.inject)
      then show ?case by simp
    next
      case (andthen m1 m2)
      then show ?case 
      proof (cases "eval_match m1 u = None")
        case True
        then show ?thesis
          using andthen.prems by auto
      next
        case False
        then obtain u' where "eval_match m1 u = Some u'"
          by force
        then have "eval_match m2 u' = Some a"
          using andthen unfolding eval_match.simps
          by simp
        then show ?thesis sorry
      qed
        unfolding eval_match.simps
    next
      case (condition x)
      then have "a = u"
        using Some unfolding eval_match.simps
        by (metis option.distinct(1) option.inject)
      then show ?case by simp
    next
      case noop
      then show ?case by simp
    qed
  then show ?thesis
    by (simp add: Some)
qed
*)

lemma monotonic_cond:
  assumes "\<forall>e u. eval_rules r u e = eval_rules (f r) u e"
  shows "\<forall>e u. eval_rules (m ? r) u e = eval_rules (m ? f r) u e"
  using assms by (metis condE eval_rules.intros(2) eval_rules.intros(3))

lemma monotonic_else:
  assumes "\<forall>e u. eval_rules r1 u e = eval_rules (f r1) u e"
  assumes "\<forall>e u. eval_rules r2 u e = eval_rules (f r2) u e"
  shows "\<forall>e. eval_rules (r1 else r2) u e = eval_rules (f r1 else f r2) u e"
  using assms
  by (metis elseE eval_rules.intros(4) eval_rules.intros(5))

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

experiment begin
lemma redundant_conditions:
  assumes "valid_match m"
  shows "eval_rules (m ? (m ? r1)) u e = eval_rules (m ? r1) u e" (is "?lhs = ?rhs")
proof -
  have "?lhs = eval_rules ((m && m) ? r1) u e"
    using chain_equiv
    by simp
  moreover have "eval_rules ((m && m) ? r1) u e = ?rhs"
    sorry
    (*using match_eq
    by (smt (verit) Rules.distinct(1) Rules.distinct(11) Rules.distinct(13) Rules.distinct(9) Rules.inject(2) assms eval_rules.simps)
    *)
  ultimately show ?thesis by simp
qed

(*lemma join_conditions_valid:
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
  by simp+*)
end

lemma join_conditions_valid:
  "join_conditions r = Some r' \<Longrightarrow> eval_rules r u e = eval_rules r' u e"
  apply (induction r rule: join_conditions.induct)
  apply (smt (verit, ccfv_threshold) condE elseE eval_rules.intros(2) eval_rules.intros(3) eval_rules.intros(4) eval_rules.intros(5) join_conditions.simps(1) option.distinct(1) option.sel)
  by simp+

lemma lift_common_valid:
  "eval_rules r u e = eval_rules (lift_common r) u e"
  proof (induction r arbitrary: u e rule: lift_common.induct)
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
      by (smt (z3) join_conditions.elims option.distinct(1))
    then have "m1 = m2"
      by (metis Some join_conditions.simps(1) option.distinct(1))
    then show ?thesis using 1
      using ex join_conditions_valid by auto
  qed
next
  case (2 m r)
  then show ?case
    by (simp add: monotonic_cond)
(*
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
*)
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

  (*subgoal for r1 r2 apply (cases "join_conditions (r1 else r2)")
    apply (smt (verit, del_insts) elseE eval_rules.intros(4) eval_rules.intros(5) lift_common.simps(1) option.case_eq_if valid_rules.simps(2))
    unfolding lift_common.simps valid_rules.simps 
    using join_conditions_valid sledgehammer
    using join_conditions.elims join_conditions_valid lift_common.simps(1) option.distinct(1) option.simps(5) valid_rules.simps(1) valid_rules.simps(2)
    *)
(*
    subgoal for m r u apply (cases "join_conditions (m ? r)")
       apply simp apply (metis condE eval_rules.intros(2) eval_rules.intros(3))
      by (simp add: join_conditions_valid)
    subgoal for rules u apply (induction rules)
      apply simp
      by (metis choice_join lift_common.simps(3) list.set_intros(1) list.set_intros(2))
     apply simp
    by (smt (verit) Rules.distinct(11) Rules.distinct(15) Rules.distinct(19) Rules.distinct(5) Rules.inject(4) eval_rules.simps lift_common.simps(5))
*)

fun common_size :: "Rules \<Rightarrow> nat" where
  "common_size (m ? r) = 1 + common_size r" |
  "common_size (base e) = 0" |
  "common_size (r1 else r2) = 1 + common_size r1 + common_size r2" |
  "common_size (choice (rule # rules)) = 1 + common_size rule + common_size (choice rules)" |
  "common_size (choice []) = 0" |
  "common_size (r1 \<then> r2) = 1 + common_size r1 + common_size r2"

fun find_common :: "MATCH \<Rightarrow> Rules \<Rightarrow> Rules option" where
  "find_common m (m' ? r) = (if m = m' then Some r else None)" |
  "find_common m r = None"

fun find_uncommon :: "MATCH \<Rightarrow> Rules \<Rightarrow> Rules option" where
  "find_uncommon m (m' ? r) = (if m = m' then None else Some (m' ? r))" |
  "find_uncommon m r = Some r"

definition join_common :: "MATCH \<Rightarrow> Rules list \<Rightarrow> Rules list" where
  "join_common m rules = List.map_filter (find_common m) rules"

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

definition join_uncommon :: "MATCH \<Rightarrow> Rules list \<Rightarrow> Rules list" where
  "join_uncommon m rules = List.map_filter (find_uncommon m) rules"

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
     apply (metis common_size.simps(1) find_uncommon_preserve le_Suc_eq option.inject plus_1_eq_Suc)
    apply (metis Suc_eq_plus1_left add.assoc common_size.simps(3) find_uncommon_preserve option.inject verit_comp_simplify1(2))
   apply (metis Suc_eq_plus1_left add.assoc common_size.simps(6) find_uncommon_preserve option.inject order_refl)
  by (metis find_uncommon_preserve option.inject order_refl)

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
    by (simp add: add_le_mono dual_order.refl)
  done

function (sequential) combine_conditions :: "Rules \<Rightarrow> Rules" where
  "combine_conditions (base e) = base e" |
  "combine_conditions (r1 else r2) = (combine_conditions r1 else combine_conditions r2)" |
  "combine_conditions (m ? r) = (m ? combine_conditions r)" |
  "combine_conditions (choice ((m ? r) # rules)) = 
    choice ((m ? combine_conditions (choice (r # join_common m rules)))
      # [combine_conditions (choice (join_uncommon m rules))])" |
  "combine_conditions (choice rules) = 
    choice (map combine_conditions rules)" |
  "combine_conditions (r1 \<then> r2) = (combine_conditions r1 \<then> combine_conditions r2)"
  apply pat_completeness+
  by simp+

experiment begin
\<comment> \<open>Can we define a version of the optimization over a list?\<close>
\<comment> \<open>Not like this, still requires recursing on the subparts in combine\_conditions\_list\<close>
fun combine_conditions_list :: "Rules list \<Rightarrow> Rules list" where
  "combine_conditions_list ((m ? r) # rules) =
    ((m ? (choice (r # join_common m rules))) # (join_uncommon m rules))" |
  "combine_conditions_list r = r"

lemma "x \<in> set (combine_conditions_list rules) \<Longrightarrow> common_size x < common_size (choice rules)"
  apply (induction rules rule: combine_conditions_list.induct) 
  unfolding combine_conditions_list.simps
  unfolding join_common_def join_uncommon_def List.map_filter_def
  apply simp sorry

function (sequential) combine_conditions2 :: "Rules \<Rightarrow> Rules" where
  "combine_conditions2 (base e) = base e" |
  "combine_conditions2 (r1 else r2) = (combine_conditions2 r1 else combine_conditions2 r2)" |
  "combine_conditions2 (m ? r) = (m ? combine_conditions2 r)" |
  "combine_conditions2 (choice rules) =
    choice (map combine_conditions2 (combine_conditions_list rules))" |
  "combine_conditions2 (r1 \<then> r2) = (combine_conditions2 r1 \<then> combine_conditions2 r2)"
  apply pat_completeness+
  by simp+

termination combine_conditions2
  apply (relation "measures [common_size, size]") apply auto[1] apply simp+ using join_common_shrinks
  sorry
end

experiment begin
\<comment> \<open>Can we define combine conditions in a two step process: 1) group matches 2) pull out matching m's\<close>

fun find_common_unchanged :: "MATCH \<Rightarrow> Rules \<Rightarrow> Rules option" where
  "find_common_unchanged m (m' ? r) = (if m = m' then Some (m' ? r) else None)" |
  "find_common_unchanged m r = None"

definition group_common :: "MATCH \<Rightarrow> Rules list \<Rightarrow> Rules list" where
  "group_common m rules = List.map_filter (find_common_unchanged m) rules"

function (sequential) group_conditions :: "Rules \<Rightarrow> Rules" where
  "group_conditions (base e) = base e" |
  "group_conditions (r1 else r2) = (group_conditions r1 else group_conditions r2)" |
  "group_conditions (m ? r) = (m ? group_conditions r)" |
  "group_conditions (choice ((m ? r) # rules)) = 
    choice ((group_conditions (choice ((m ? r) # group_common m rules)))
      # [group_conditions (choice (join_uncommon m rules))])" |
  "group_conditions (choice rules) = 
    choice (map group_conditions rules)" |
  "group_conditions (r1 \<then> r2) = (group_conditions r1 \<then> group_conditions r2)"
  apply pat_completeness+
  by simp+

termination group_conditions
  apply (relation "measures [common_size, size]") apply auto[1] apply simp+ using join_common_shrinks
  sorry

function (sequential) merge_conditions :: "Rules \<Rightarrow> Rules" where
  "merge_conditions (base e) = base e" |
  "merge_conditions (r1 else r2) = (merge_conditions r1 else merge_conditions r2)" |
  "merge_conditions (m ? r) = (m ? merge_conditions r)" |
  "merge_conditions (choice ((m ? r) # (m' ? r') # rules)) = (if m = m' then
    m ? choice (map merge_conditions (r # r' # join_common m rules)) else
    choice (map merge_conditions ((m ? r) # (m' ? r') # rules)))" |
  "merge_conditions (choice rules) = 
    choice (map merge_conditions rules)" |
  "merge_conditions (r1 \<then> r2) = (merge_conditions r1 \<then> merge_conditions r2)"
  apply pat_completeness+
  by simp+

termination merge_conditions
  apply (relation "measures [common_size, size]") apply auto[1] apply simp+ using join_common_shrinks
  sorry

definition collapse_conditions :: "Rules \<Rightarrow> Rules" where
  "collapse_conditions = merge_conditions o group_conditions"

end

lemma find_common_size:
  assumes "(find_common m r) \<noteq> None"
  shows "size (the (find_common m r)) < size r"
  using assms apply (induction r rule: find_common.induct)
  apply simp+ apply fastforce by simp+

(*
lemma "size_list size (join_common m rules) \<le> (size_list size rules)"
  unfolding join_common_def map_filter_def
  (*apply (induction rules) apply auto[1]*)
  apply (induction rule: find_common.induct)
  apply (induction rules) 
  apply simp using find_common_size sorry

lemma
  "combined_size (choice (join_common m rules))
       < combined_size (m ? (choice rules)) \<or>
       combined_size (choice (join_common m rules)) =
       combined_size (m ? (choice rules)) \<and>
       size_list size (join_common m rules) < Suc (size_list size rules)"
*)

lemma common_size_choice_gt:
  "x \<in> set va \<Longrightarrow> common_size x \<le> common_size (choice va)"
  apply (induction va) apply simp
  by fastforce

termination combine_conditions
  apply (relation "measures [common_size]") apply auto[1] apply simp+ using join_common_shrinks
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

(*
lemma eval_choice: "eval_rules (choice rules) u e \<longrightarrow> (\<exists> r \<in> set rules . eval_rules r u e)"
  sorry
*)

lemma eval_choice: "{e. eval_rules (choice rules) u e \<and> e \<noteq> None} = {e | e r . r \<in> set rules \<and> eval_rules r u e \<and> e \<noteq> None}"
  using choiceE eval_rules.intros(6) by fastforce

lemma eval_choice_none: "eval_rules (choice rules) u None = (\<forall> r \<in> set rules . eval_rules r u None)"
  by (metis choiceE eval_rules.intros(7) length_pos_if_in_set list.size(3) nless_le option.distinct(1))

inductive_cases evalRulesE: "eval_rules r u e"

lemma eval_always_result:
  "\<exists> e. eval_rules r u e"
  apply (induction r arbitrary: u)
  using eval_rules.intros(1) apply auto[1]
  using eval_rules.intros(2,3) apply (meson opt_to_list.cases) 
  using eval_rules.intros(4,5) apply (metis split_option_ex) 
  using eval_rules.intros(9,10) apply (metis split_option_ex) 
  using eval_rules.intros(6,7,8) by (metis split_option_ex) 

experiment begin
lemma eval_choice_none_always:
  assumes "eval_rules (choice rules) u None"
  assumes "rules \<noteq> []"
  shows "(\<forall>r. eval_rules (choice rules) u r \<longrightarrow> r = None)"
  sorry
  (*using assms apply (subst (asm) eval_choice_none)
  apply (rule allI)
  subgoal for r
    using assms evalRulesE
  apply (induction rule: eval_rules.induct)
  using baseE apply blast
  apply (metis condE option.distinct(1) option.sel) 
  apply (metis condE option.distinct(1))
  apply (metis elseE option.distinct(1))
  apply (metis elseE option.distinct(1)) using eval_choice_none *)

lemma eval_choice_some_e:
  assumes "eval_rules (choice rules) u e"
  assumes "e \<noteq> None"
  shows "(\<exists>r \<in> set rules. eval_rules r u e)"
  by (metis assms(1) assms(2) choiceE)

lemma eval_single_choice: "{e. eval_rules (choice [r]) u e} = {e. eval_rules r u e}" (is "?lhs = ?rhs")
proof (cases "eval_rules r u None")
  case True
  then have "eval_rules (choice [r]) u None"
    by (simp add: eval_rules.intros(7))
  then show ?thesis
    by (metis True eval_choice_none_always eval_rules.intros(6) list.distinct(1) list.set_intros(1) option.exhaust)
next
  case False
  then have "\<forall>e. eval_rules r u (Some e) \<longrightarrow> eval_rules (choice [r]) u (Some e)"
    by (simp add: eval_rules.intros(6))
  also have "\<forall>e. eval_rules (choice [r]) u (Some e) \<longrightarrow> eval_rules r u (Some e)"
    using eval_choice_some_e by force
  then show ?thesis
    by (metis False calculation eval_always_result eval_choice_none_always not_Cons_self2 not_None_eq)
qed

lemma monotonic_choice:
  assumes "\<forall>r \<in> set rules. {e. eval_rules r u e} = {e. eval_rules (f r) u e}"
  shows "{e. eval_rules (choice rules) u e} = {e. eval_rules (choice (map f rules)) u e}"
proof (cases "eval_rules (choice rules) u None")
  case True
  then have "\<forall>r \<in> set rules. eval_rules r u None"
    by (simp add: eval_choice_none)
  then have "\<forall>r \<in> set rules. eval_rules (f r) u None"
    using assms by blast
  then have "eval_rules (choice (map f rules)) u None"
    using eval_choice_none sorry
  then show ?thesis
    by (metis Nil_is_map_conv True eval_choice_none_always)
next
  case False
  then have "\<forall>e. eval_rules (choice rules) u (Some e) \<longrightarrow> eval_rules (choice (map f rules)) u (Some e)"
    sorry
  also have "\<forall>e. eval_rules (choice (map f rules)) u (Some e) \<longrightarrow> eval_rules (choice rules) u (Some e)"
    sorry
  then show ?thesis
    by (metis Nil_is_map_conv calculation choiceE eval_always_result eval_choice_none_always)
qed
  

lemma combine_no_recurse:
  "{e. eval_rules (choice ((m ? r) # rules)) u e} = {e. eval_rules 
  (choice [(m ? (choice (r # join_common m rules))), choice (join_uncommon m rules)]) u e}"
  (is "{e. eval_rules ?lhs u e} = {e. eval_rules ?rhs u e}")
proof (induction rules)
  case Nil
  have "(choice ((m ? choice (r # join_common m [])) # join_uncommon m [])) = choice ([m ? choice [r]])"
    using join_common_empty join_uncommon_empty
    by simp
  also have "{e. eval_rules (choice ([m ? choice [r]])) u e} = {e. eval_rules (m ? r) u e}"
    using eval_single_choice
    by (smt (z3) Collect_cong condE eval_always_result eval_rules.simps option.inject option.simps(3))
  then show ?case sorry (*
    by (simp add: eval_single_choice join_common_empty join_uncommon_empty)*)
next
  case (Cons a rules)
  then show ?case sorry
qed
end


lemmas monotonic =
  monotonic_cond
  monotonic_else
  monotonic_choice
  monotonic_seq

lemma unordered_choice:
  assumes "set rules = set rules'"
  shows "\<forall>e. eval_rules (choice rules) u e = eval_rules (choice rules') u e"
  using assms by (metis choiceE eval_choice_none eval_rules.intros(6))

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

experiment begin
lemma pull_out_uncommon:
  assumes "join_common m rules = []"
  shows "eval_rules (choice (join_uncommon m rules)) u e = eval_rules (choice (rules)) u e"
proof -
  have "\<forall>r \<in> (set rules). find_common m r = None"
    using assms unfolding join_common_def List.map_filter_def
    by (simp add: filter_empty_conv)
  then have "\<forall>r \<in> set rules. \<exists>p. find_uncommon m r = Some p"
    using assms unfolding join_common_def join_uncommon_def List.map_filter_def
    using find_inverse_lhs by blast
  then have "rules = join_uncommon m rules"
    unfolding join_common_def join_uncommon_def List.map_filter_def
    by (smt (verit, ccfv_threshold) comp_eq_dest_lhs filter_id_conv find_uncommon_preserve map_idI option.sel option.simps(3))
  then show ?thesis
    by simp
qed

lemma pull_out_common:
  assumes "join_uncommon m rules = []"
  shows "eval_rules (m ? choice (r # join_common m rules)) u e = eval_rules (choice ((m ? r) # rules)) u e"
  using assms sorry

lemma pull_out:
  shows "
    eval_rules (choice ((m ? r) # rules)) u e =
    eval_rules (choice ((m ? (choice (r # join_common m rules))) # [(choice (join_uncommon m rules))])) u e"
  using pull_out_uncommon pull_out_common sorry

lemma combine_conditions:
  "eval_rules r u e = eval_rules (combine_conditions r) u e"
  apply (induction r arbitrary: u e rule: combine_conditions.induct) apply simp
  apply (simp add: monotonic)+
        defer
  apply simp+
  apply (metis choice_join combine_conditions.simps(1) list.simps(9) monotonic_choice)
  using monotonic_choice
  using combine_conditions.simps(7) monotonic_choice apply presburger
  using combine_conditions.simps(8) monotonic_choice apply presburger
  using combine_conditions.simps(9) monotonic_choice apply presburger
   apply (simp add: monotonic)+
  using pull_out sorry

end

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

experiment begin
lemma abstract_combine_condition:
  assumes "\<forall>u e. eval_rules (choice (r # ms)) u e \<longrightarrow> eval_rules (f (choice (r # ms))) u e"
  assumes "\<forall>u e. eval_rules (choice n) u e \<longrightarrow> eval_rules (f (choice n)) u e"
  assumes "(set (map (\<lambda>r. m ? r) ms) \<union> set n) = set rules"
  shows "eval_rules (choice ((m ? r) # rules)) u e \<longrightarrow>
       eval_rules
        (choice
          [m ? f (choice (r # ms)),
           f (choice (n))]) u e"
  using assms sorry

lemma combine_conditions_lhs:
  "eval_rules r u e = eval_rules (combine_conditions r) u e"
  apply (induction r arbitrary: u e rule: combine_conditions.induct) apply simp
  apply (simp add: monotonic)+
        defer
  apply simp+
  apply (metis choice_join combine_conditions.simps(1) list.simps(9) monotonic_choice)
  using monotonic_choice
  using combine_conditions.simps(7) monotonic_choice apply presburger
  using combine_conditions.simps(8) monotonic_choice apply presburger
  using combine_conditions.simps(9) monotonic_choice apply presburger
   apply (simp add: monotonic)+
  sorry

lemma
  assumes "\<forall>u e. eval_rules (choice (r # join_common m rules)) u e \<longrightarrow>
           eval_rules (combine_conditions (choice (r # join_common m rules))) u e"
  assumes "\<forall>u e. eval_rules (choice (join_uncommon m rules)) u e \<longrightarrow>
           eval_rules (combine_conditions (choice (join_uncommon m rules))) u e"
  shows "eval_rules (choice ((m ? r) # rules)) u e \<longrightarrow>
       eval_rules
        (choice
          [m ? combine_conditions (choice (r # join_common m rules)),
           combine_conditions (choice (join_uncommon m rules))])
        u e"
  sorry

lemma combine_nested:
  assumes "set rules = {choice r} \<union> set r'"
  assumes "set rules' = set r \<union> set r'"
  shows "\<forall>e. eval_rules (choice rules) u e = eval_rules (choice rules') u e"
  using assms
proof -
  obtain e' where "eval_rules (choice r) u e'"
    using eval_always_result by auto
  show ?thesis proof (cases e')
    case None
    have "\<forall>e. eval_rules (choice rules) u e = eval_rules (choice r') u e"
      using choiceE assms sorry
    then show ?thesis sorry
  next
    case (Some a)
    then show ?thesis sorry
  qed
qed
end

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

experiment begin
lemma idempotent_match:
  assumes "valid_match m"
  assumes "eval_match m u = Some r"
  shows "eval_match m r = Some r"
  using assms sorry (*
  by (metis eval_match.simps(6) match_eq option.simps(5))*)
end

lemma
  assumes "\<exists>r \<in> set rules. r \<in> set rules' \<and> eval_rules r u (Some e)"
  shows "eval_rules (choice rules) u (Some e) = eval_rules (choice rules') u (Some e)"
  using assms
  using eval_rules.intros(6) by blast

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
      then show ?thesis using pre apply auto
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

lemma combine_conditions_valid:
  "eval_rules r u e = eval_rules (combine_conditions r) u e"
  apply (induction r arbitrary: u e rule: combine_conditions.induct) apply simp
  apply (simp add: monotonic)+
        defer
  apply simp+
  apply (metis choice_join combine_conditions.simps(1) list.simps(9) monotonic_choice)
  using monotonic_choice
  using combine_conditions.simps(7) monotonic_choice apply presburger
  using combine_conditions.simps(8) monotonic_choice apply presburger
  using combine_conditions.simps(9) monotonic_choice apply presburger
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

(*
  proof (cases e)
    case None
    then have "eval_rules (m ? (choice (r # join_common m rules))) u None \<and>
  eval_rules ((choice (join_uncommon m rules))) u None"
      sorry
    then show ?thesis using p sorry
  next
    case (Some a)
    then show ?thesis sorry
  qed*)

(*
  proof (cases e)
    case None
    then show ?thesis 
      apply simp apply (rule choiceE) using None cases_None
      using eval_always_result apply auto
  next
    case (Some a)
    then show ?thesis sorry
  qed

  using join_combines unordered_choice monotonic_choice combine_nested
  
  done
*)

(*
lemma combine_conditions_valid:
  "{e. eval_rules r u e} = {e. eval_rules (combine_conditions r) u e}"
  apply (induction r arbitrary: u rule: combine_conditions.induct)
  apply simp unfolding combine_conditions.simps
  apply (smt (verit, del_insts) Collect_cong elseE eval_rules.intros(4) eval_rules.intros(5) mem_Collect_eq)
  unfolding combine_conditions.simps 
  apply (smt (z3) Collect_cong condE eval_rules.simps mem_Collect_eq)
  unfolding combine_conditions.simps 
  subgoal for m r rules u
    using combine_no_recurse sorry
  sorry*)
    (*apply (smt (verit, del_insts) elseE eval_rules.intros(4) eval_rules.intros(5) lift_common.simps(1) option.simps(4))
      by (simp add: join_conditions_valid)
    subgoal for m r u apply (cases "join_conditions (m ? r)")
       apply simp apply (metis condE eval_rules.intros(2) eval_rules.intros(3))
      by (simp add: join_conditions_valid)
    subgoal for rules u apply (induction rules)
      apply simp
      by (metis choice_join lift_common.simps(3) list.set_intros(1) list.set_intros(2))
     apply simp
    by (smt (verit) Rules.distinct(11) Rules.distinct(15) Rules.distinct(19) Rules.distinct(5) Rules.inject(4) eval_rules.simps lift_common.simps(5))
*)

fun eliminate_choice :: "Rules \<Rightarrow> Rules" where
  "eliminate_choice (base e) = base e" |
  "eliminate_choice (r1 else r2) = (eliminate_choice r1 else eliminate_choice r2)" |
  "eliminate_choice (m ? r) = (m ? eliminate_choice r)" |
  "eliminate_choice (choice (r # [])) = eliminate_choice r" |
  "eliminate_choice (choice rules) = 
    choice (map eliminate_choice rules)" |
  "eliminate_choice (r1 \<then> r2) = (eliminate_choice r1 \<then> eliminate_choice r2)"

lemma choice_Single:
  "eval_rules (choice [r]) u e = eval_rules r u e"
  apply (cases e)
  using eval_choice_none apply auto[1]
  using choiceE eval_rules.intros(6) by fastforce

lemma eliminate_choice_valid:
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
  by (smt (verit) Collect_cong eval_rules.intros(10) eval_rules.intros(9) mem_Collect_eq seqE)


definition optimized_export where
  "optimized_export = eliminate_choice \<circ> combine_conditions o lift_common o lift_match o eliminate_noop o eliminate_empty"


lemma optimized_export_valid:
  "{e. eval_rules r u e} = {e. eval_rules (optimized_export r) u e}"
  unfolding optimized_export_def comp_def
  using lift_common_valid lift_match_valid eliminate_noop_valid eliminate_empty_valid 
  using combine_conditions_valid eliminate_choice_valid by simp

thm_oracles optimized_export_valid


subsection \<open>Java AST\<close>

type_synonym ClassName = string
type_synonym VariableName = String.literal
type_synonym MethodName = string

datatype Expression =
  Ref VariableName |
  IntegerConstant int |
  TrueValue |
  FalseValue |
  MethodCall Expression MethodName "Expression list" |
  Constructor ClassName "Expression list" |
  InstanceOf Expression ClassName VariableName |
  Equal Expression Expression |
  Less Expression Expression |
  Negate Expression |
  And Expression Expression |
  BitAnd Expression Expression |
  Unsupported string

datatype Statement =
  Assignment VariableName Expression |
  Branch Expression Statement |
  Return Expression |
  Sequential "Statement list"

fun intersperse :: "string \<Rightarrow> string list \<Rightarrow> string list" where
  "intersperse i es = foldr (\<lambda>x ys . x # (if ys = [] then ys else i # ys)) es []"

fun param_list :: "string list \<Rightarrow> string" where
  "param_list es = (foldr (@) (intersperse '', '' es) '''')"

fun generate_expression :: "Expression \<Rightarrow> string" where
  "generate_expression (Ref v) = String.explode v" |
  "generate_expression (IntegerConstant n) = ''0''" | (*TODO FIX*)
  "generate_expression TrueValue = ''true''" |
  "generate_expression FalseValue = ''false''" |
  "generate_expression (MethodCall e mn ps) = 
    (generate_expression e) @ ''.'' @ mn @ ''('' @ param_list (map generate_expression ps) @ '')''" |
  "generate_expression (Constructor cn ps) =
    ''new '' @ cn @ ''('' @ param_list (map generate_expression ps) @ '')''" |
  "generate_expression (InstanceOf e cn var) =
    (generate_expression e) @ '' instanceof '' @ cn @ '' '' @ (String.explode var)" |
  "generate_expression (Equal e1 e2) =
    (generate_expression e1) @ '' == '' @ (generate_expression e2)" |
  "generate_expression (Less e1 e2) =
    (generate_expression e1) @ '' < '' @ (generate_expression e2)" |
  "generate_expression (Negate e) =
    ''!('' @ (generate_expression e) @ '')''" |
  "generate_expression (And e1 e2) =
    (generate_expression e1) @ '' && '' @ (generate_expression e2)" |
  "generate_expression (BitAnd e1 e2) =
    (generate_expression e1) @ '' & '' @ (generate_expression e2)"

fun indent :: "nat \<Rightarrow> string" where
  "indent 0 = ''''" |
  "indent (Suc n) = '' '' @ indent n"

fun generate_statement :: "nat \<Rightarrow> Statement \<Rightarrow> string" where
  "generate_statement i (Assignment v e) = indent i @
    ''var '' @ String.explode v @ '' = '' @ generate_expression e @ '';\<newline>''" |
  "generate_statement i (Branch c s) = indent i @
    ''if ('' @ generate_expression c @ '') {\<newline>'' @ generate_statement (i + 4) s @ 
    indent i @ ''}\<newline>''" |
  "generate_statement i (Return e) = indent i @
    ''return '' @ generate_expression e @ '';\<newline>''" |
  "generate_statement i (Sequential ss) = 
    foldr (@) (map (generate_statement i) ss) ''''"


subsection \<open>Java Generation\<close>

fun unary_op_class :: "IRUnaryOp \<Rightarrow> ClassName" where
  "unary_op_class UnaryAbs = ''AbsNode''" |
  "unary_op_class UnaryNeg = ''NegateNode''" |
  "unary_op_class UnaryNot = ''NotNode''" |
  "unary_op_class UnaryLogicNegation = ''LogicNegationNode''" |
  "unary_op_class (UnaryNarrow _ _) = ''NarrowNode''" |
  "unary_op_class (UnarySignExtend _ _) = ''SignExtendNode''" |
  "unary_op_class (UnaryZeroExtend _ _) = ''ZeroExtendNode''"

fun binary_op_class :: "IRBinaryOp \<Rightarrow> ClassName" where
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

fun export_pattern :: "PatternExpr \<Rightarrow> ClassName" where
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

fun export_value :: "Value \<Rightarrow> Expression" where
  "export_value (IntVal s v) = IntegerConstant (sint v)" |
  "export_value _ = Unsupported ''unsupported Value''"

fun export_irexpr :: "IRExpr \<Rightarrow> Expression" where
  "export_irexpr (UnaryExpr op e1) =
    Constructor (unary_op_class op) [export_irexpr e1]" |
  "export_irexpr (BinaryExpr op e1 e2) =
    Constructor (binary_op_class op) [export_irexpr e1, export_irexpr e2]" |
  "export_irexpr (ConditionalExpr e1 e2 e3) =
    Constructor ''ConditionalNode''  [export_irexpr e1, export_irexpr e2, export_irexpr e3]" |
  "export_irexpr (ConstantExpr val) =
    Constructor ''ConstantNode'' [export_value val]" |
  "export_irexpr (ConstantVar var) =
    Constructor ''ConstantNode'' [Ref var]" |
  "export_irexpr (VariableExpr v s) = Ref v"

fun export_stamp :: "Stamp \<Rightarrow> Expression" where
  "export_stamp (IntegerStamp bits lower higher) =
    Constructor ''IntegerStamp'' 
      [IntegerConstant bits, IntegerConstant lower,
       IntegerConstant higher]" |
  "export_stamp _ =
    Unsupported ''unsupported Stamp''"

definition stampOf :: "Expression \<Rightarrow> Expression" where
  "stampOf e = (MethodCall e ''stamp'' [Ref STR ''view''])"

definition upMask :: "Expression \<Rightarrow> Expression" where
  "upMask e = (MethodCall (stampOf e) ''upMask'' [])"

definition downMask :: "Expression \<Rightarrow> Expression" where
  "downMask e = (MethodCall (stampOf e) ''downMask'' [])"

fun export_condition :: "SideCondition \<Rightarrow> Expression" where
  "export_condition (IsConstantExpr e) = (InstanceOf (export_irexpr e) ''ConstantNode'' STR ''t'')" |
  "export_condition (WellFormed s) = TrueValue" |
  "export_condition (IsStamp e s) =
    (Equal (stampOf (export_irexpr e)) (export_stamp s))" |
  "export_condition (StampUnder e1 e2) =
    (Less 
      (MethodCall (stampOf (export_irexpr e1)) ''upperBound'' []) 
      (MethodCall (stampOf (export_irexpr e2)) ''lowerBound'' []))" |
  "export_condition (UpMaskEquals e m) =
    Equal (upMask (export_irexpr e)) (IntegerConstant (sint m))" |
  "export_condition (DownMaskEquals e m) =
    Equal (downMask (export_irexpr e)) (IntegerConstant (sint m))" |
  "export_condition (UpMaskCancels e1 e2) =
    Equal (BitAnd (upMask (export_irexpr e1)) (upMask (export_irexpr e2))) (IntegerConstant 0)" |
  "export_condition (PowerOf2 e) =
    MethodCall (Ref STR ''CodeUtil'') ''isPowerOf2'' [export_irexpr e]" |
  "export_condition (IsBool e) =
    Equal (MethodCall (export_irexpr e) ''upMask'' []) (IntegerConstant 1)" |
  "export_condition (Not sc) = Negate (export_condition sc)" |
  "export_condition (SideCondition.And sc1 sc2) = And (export_condition sc1) (export_condition sc2)" |
  "export_condition (Empty) = TrueValue"

fun export_assignments :: "VarName \<Rightarrow> PatternExpr \<Rightarrow> Statement \<Rightarrow> Statement" where
  "export_assignments v (UnaryPattern op v1) s = Sequential
    [Assignment v1 (MethodCall (Ref (v + STR ''c'')) ''getValue'' []), s]" |
  "export_assignments v (BinaryPattern op v1 v2) s = Sequential
    [Assignment v1 (MethodCall (Ref (v + STR ''c'')) ''getX'' []),
     Assignment v2 (MethodCall (Ref (v + STR ''c'')) ''getY'' []), s]" |
  "export_assignments v (ConditionalPattern v1 v2 v3) s = Sequential
    [Assignment v1 (MethodCall (Ref (v + STR ''c'')) ''condition'' []),
     Assignment v2 (MethodCall (Ref (v + STR ''c'')) ''trueValue'' []),
     Assignment v3 (MethodCall (Ref (v + STR ''c'')) ''falseValue'' []), s]" |
  "export_assignments v (ConstantPattern val) s =
    Branch (InstanceOf (MethodCall (Ref (v + STR ''c'')) ''getValue'' []) ''PrimitiveConstant'' (v + STR ''cd''))
    (Branch (Equal (MethodCall (Ref (v + STR ''cd'')) ''asLong'' []) (export_value val)) s)" |
  "export_assignments v (ConstantVarPattern var) s =
    Branch (Equal (MethodCall (Ref (v + STR ''c'')) ''getValue'' []) (Ref var)) s"

function (sequential) export_match :: "MATCH \<Rightarrow> Statement \<Rightarrow> Statement" where
  "export_match (match v p) r  = 
    Branch (InstanceOf (Ref v) (export_pattern p) (String.implode (String.explode v @ ''c'')))
      (export_assignments v p r)" |
  "export_match (andthen m1 m2) r = 
    export_match m1 (export_match m2 r)" |
  "export_match (equality v1 v2) r = 
    Branch (Equal (Ref v1) (Ref v2)) r" |
  "export_match (condition (SideCondition.And sc1 sc2)) r = 
    Branch (export_condition sc1) (Branch (export_condition sc2) r)" |
  "export_match (condition (WellFormed s)) r = r" |
  "export_match (condition (Empty)) r = r" |
  "export_match (condition sc) r = 
    Branch (export_condition sc) r" |
  "export_match noop r = r"
  apply pat_completeness+
  by simp+

fun size_condition :: "(MATCH \<times> Statement) \<Rightarrow> nat" where
  "size_condition ((condition c), s) = size (condition c) + size c" |
  "size_condition (m, s) = size m"

termination export_match
  apply (relation "measures [size_condition]") apply simp apply simp sorry

(*
fun close :: "MATCH \<Rightarrow> string" where
  "close (match v (ConstantPattern val)) = ''
}
}''" |
  "close (match v p) = ''
}''" |
  "close (andthen m1 m2) = close m1 @ close m2" |
  "close (equality v1 v2) = ''
}''" |
  "close (negate sc) = ''
}''" |
  "close (condition sc) = ''
}''" |
  "close noop = ''''"
*)

fun export_rules :: "Rules \<Rightarrow> Statement" where
  "export_rules (base e) = Return (export_irexpr e)" |
  "export_rules (cond m r) = export_match m (export_rules r)" |
  "export_rules (r1 else r2) = Sequential [export_rules r1, export_rules r2]" |
  "export_rules (choice rules) = Sequential (map export_rules rules)" |
  "export_rules (r1 \<then> r2) = Sequential [export_rules r1, export_rules r2]" (* TODO: should modify e *)


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
    (MATCH.match STR ''a'' (UnaryPattern UnaryNot STR ''az'') && noop) && condition Empty) ?
      base (VariableExpr STR ''az'' VoidStamp)"
  by eval

value "
generate 
    (BinaryExpr BinAdd
      (var ''x'')
      (var ''x''))
    (BinaryExpr BinSub (var ''x'') (var ''e''))
    (Empty)
"

corollary
  "RedundantSub =
   (MATCH.match STR ''e'' (BinaryPattern BinAdd STR ''a'' STR ''b'') &&
    (MATCH.match STR ''a'' (BinaryPattern BinSub STR ''az'' STR ''bz'') && noop && noop) &&
      STR ''bz'' == STR ''b'' && condition Empty) ?
        base (VariableExpr STR ''az'' VoidStamp)"
  by eval

corollary
  "AddLeftNegateToSub =
   (MATCH.match STR ''e'' (BinaryPattern BinAdd STR ''a'' STR ''b'') && noop &&
    (MATCH.match STR ''b'' (UnaryPattern UnaryNeg STR ''az'') && noop) && condition Empty) ?
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
      (STR ''bz'' == STR ''b'' ? (condition Empty ? base (VariableExpr STR ''az'' VoidStamp)))))) else
   MATCH.match STR ''e'' (BinaryPattern BinAdd STR ''a'' STR ''b'') ?
   (noop ?
    (MATCH.match STR ''b'' (UnaryPattern UnaryNeg STR ''az'') ?
     (noop ?
      (condition Empty ?
       base
        (BinaryExpr BinSub (VariableExpr STR ''a'' VoidStamp)
          (VariableExpr STR ''az'' VoidStamp)))))))"
  by eval

(*
corollary
  "lift_common (lift_match (RedundantSub else AddLeftNegateToSub)) =
   (MATCH.match STR ''e'' (BinaryPattern BinAdd STR ''a'' STR ''b'') ?
   (MATCH.match STR ''a'' (BinaryPattern BinSub STR ''az'' STR ''bz'') ?
    (noop ?
     (STR ''bz'' == STR ''b'' ? (condition Empty ? base (VariableExpr STR ''az'' VoidStamp)))) else
    noop ?
    (MATCH.match STR ''b'' (UnaryPattern UnaryNeg STR ''az'') ?
     (noop ?
      (condition Empty ?
       base
        (BinaryExpr BinSub (VariableExpr STR ''a'' VoidStamp)
          (VariableExpr STR ''az'' VoidStamp)))))))"
  by eval*)

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

value "RedundantSub"
value "(export_rules RedundantSub)"
value "generate_statement 0 (export_rules RedundantSub)"
value "export_rules AddLeftNegateToSub"
value "generate_statement 0 (export_rules (RedundantSub else AddLeftNegateToSub))"

value "export_rules (lift_common (lift_match (RedundantSub else AddLeftNegateToSub)))"
value "export_rules (optimized_export (RedundantSub else AddLeftNegateToSub))"

value "lift_match (eliminate_noop (NestedNot else RedundantSub else AddLeftNegateToSub))"
value "export_rules (optimized_export ((RedundantSub else AddLeftNegateToSub) else NestedNot))"
value "export_rules (optimized_export (NestedNot else RedundantSub else AddLeftNegateToSub))"

no_notation cond (infixl "?" 52)
no_notation seq (infixl "\<then>" 50)
no_notation andthen (infixl "&&" 50)

notation SideCondition.And (infixl "&&" 50)

value "NestedNot \<then> (RedundantSub else AddLeftNegateToSub)"


subsection \<open>Examples\<close>

text \<open>@{text "x * const 1 \<longrightarrow> x"}\<close>
definition Identity where
  "Identity = generate 
    (BinaryExpr BinMul
      (var ''x'')
      (ConstantExpr (IntVal 32 1)))
    (var ''x'')
    (Empty)"

value "Identity"
value "export_rules (optimized_export (Identity))"

text \<open>@{text "const x * const y \<longrightarrow> const (x * y)"}\<close>
definition Evaluate where
  "Evaluate = generate 
    (BinaryExpr BinMul
      (ConstantVar STR ''x'')
      (ConstantVar STR ''y''))
    (ConstantVar STR ''x'')
    (Empty)"
(* doesn't support constant evaluation *)
value "Evaluate"
value "export_rules (optimized_export (Evaluate))"

text \<open>@{text "x * const y \<longrightarrow> x << const (log2 y)"}\<close>
definition Shift where
  "Shift = generate 
    (BinaryExpr BinMul
      (var ''x'')
      (ConstantVar STR ''y''))
    (BinaryExpr BinLeftShift (var ''x'') (ConstantVar STR ''y''))
    (PowerOf2 (ConstantVar STR ''y''))"
(* doesn't support constant evaluation *)
value "Shift"


text \<open>@{text "const x * y \<longrightarrow> y * const x when NotConst y"}\<close>
definition LeftConst where
  "LeftConst = generate 
    (BinaryExpr BinMul
      (ConstantVar STR ''x'')
      (var ''y''))
    (BinaryExpr BinMul (var ''y'') (ConstantVar STR ''x''))
    (Not (IsConstantExpr (var ''y'')))"
(* doesn't support constant evaluation *)
value "LeftConst"


value "(optimized_export (optimized_export (LeftConst \<then> (Evaluate else (Identity else Shift)))))"

end
