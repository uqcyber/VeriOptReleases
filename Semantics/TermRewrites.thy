theory TermRewrites
  imports Semantics.IRTreeEvalThms Semantics.TreeToGraphThms Snippets.Snipping
begin

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

type_synonym Substitution = "String.literal \<rightharpoonup> SubValue"

fun substitute :: "Substitution \<Rightarrow> IRExpr \<Rightarrow> IRExpr" (infix "$" 60) where
  "substitute \<sigma> (UnaryExpr op e) = UnaryExpr op (\<sigma> $ e)" |
  "substitute \<sigma> (BinaryExpr op e1 e2) = BinaryExpr op (\<sigma> $ e1) (\<sigma> $ e2)" |
  "substitute \<sigma> (ConditionalExpr b e1 e2) = ConditionalExpr (\<sigma> $ b) (\<sigma> $ e1) (\<sigma> $ e2)" |
  "substitute \<sigma> (ParameterExpr i s) = ParameterExpr i s" |
  "substitute \<sigma> (LeafExpr n s) = LeafExpr n s" |
  "substitute \<sigma> (ConstantExpr v) = ConstantExpr v" |
  "substitute \<sigma> (ConstantVar x) = 
      (case \<sigma> x of Some (SubConst v) \<Rightarrow> ConstantExpr v | _ \<Rightarrow> ConstantVar x)" |
  "substitute \<sigma> (VariableExpr x s) = 
      (case \<sigma> x of None \<Rightarrow> (VariableExpr x s) | Some (SubExpr y) \<Rightarrow> y)"

lemma not_empty_has_member:
  assumes "xs \<noteq> []"
  shows "\<exists> k v. List.member xs (k, v)"
  using assms apply (cases xs; auto)
  by (meson member_rec(1))

value "map_of ([(x, xv1), (y, yv)] @ [(z, zv), (x, xv2)]) x"

lemma equal_mapping_implies_equal:
  assumes "\<forall>k. \<sigma>1 k = \<sigma>2 k"
  shows "\<sigma>1 = \<sigma>2"
  using assms
  by auto

fun compatible :: "Substitution \<Rightarrow> Substitution \<Rightarrow> bool" where
  "compatible \<sigma>1 \<sigma>2 = (\<forall>x \<in> dom \<sigma>1. \<sigma>2 x \<noteq> None \<longrightarrow> \<sigma>1 x = \<sigma>2 x)"

fun substitution_union :: "Substitution option \<Rightarrow> Substitution option \<Rightarrow> Substitution option" (infix "\<uplus>" 70) where
  "substitution_union s1 s2 = 
      (case s1 of
       None \<Rightarrow> None |
       Some \<sigma>1 \<Rightarrow> 
           (case s2 of
            None \<Rightarrow> None |
            Some \<sigma>2 \<Rightarrow> (if compatible \<sigma>1 \<sigma>2 then Some (\<sigma>1 ++ \<sigma>2) else None)
           )
      )"


definition EmptySubstitution :: "Substitution" where 
  "EmptySubstitution = map_of []"

fun match_tree :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> Substitution option" where
  "match_tree (UnaryExpr op e) (UnaryExpr op' e') = 
      (if op = op' then match_tree e e' else None)" |
  "match_tree (BinaryExpr op e1 e2) (BinaryExpr op' e1' e2') = 
      (if op = op' then (match_tree e1 e1') \<uplus> (match_tree e2 e2') else None)" |
  "match_tree (ConditionalExpr b e1 e2) (ConditionalExpr b' e1' e2') = 
      (match_tree b b') \<uplus> ((match_tree e1 e1') \<uplus> (match_tree e2 e2'))" |
  "match_tree (ParameterExpr i1 s1) (ParameterExpr i2 s2) = 
      (if i1 = i2 \<and> s1 = s2 then Some EmptySubstitution else None)" |
  "match_tree (LeafExpr n1 s1) (LeafExpr n2 s2) = 
      (if n1 = n2 \<and> s1 = s2 then Some EmptySubstitution else None)" |
  "match_tree (ConstantExpr v1) (ConstantExpr v2) = 
      (if v1 = v2 then Some EmptySubstitution else None)" |
  "match_tree (ConstantVar name) (ConstantExpr v) = 
      Some (map_of [(name, (SubConst v))])" |
  "match_tree (VariableExpr name s) e = 
      Some (map_of [(name, (SubExpr e))])" |
  "match_tree _ _ = None"

fun vars :: "IRExpr \<Rightarrow> String.literal fset" where
  "vars (UnaryExpr op e) = vars e" |
  "vars (BinaryExpr op e1 e2) = vars e1 |\<union>| vars e2" |
  "vars (ConditionalExpr b e1 e2) = vars b |\<union>| vars e1 |\<union>| vars e2" |
  "vars (ParameterExpr i s) = {||}" |
  "vars (LeafExpr n s) = {||}" |
  "vars (ConstantExpr v) = {||}" |
  "vars (ConstantVar x) = {|x|}" |
  "vars (VariableExpr x s) = {|x|}"


typedef Rewrite = "{ (e1,e2,cond) :: IRExpr \<times> IRExpr \<times> (Substitution \<Rightarrow> bool) | e1 e2 cond . vars e2 |\<subseteq>| vars e1 }" 
proof -
  have "\<exists>v. vars (ConstantExpr v) |\<subseteq>| vars (ConstantExpr v)" by simp
  then show ?thesis
    by auto
qed

setup_lifting type_definition_Rewrite

fun construct_rewrite :: "IRExpr \<times> IRExpr \<times> (Substitution \<Rightarrow> bool) \<Rightarrow> Rewrite option" where
  "construct_rewrite (e1, e2, cond) =
    (if vars e2 |\<subseteq>| vars e1 then Some (Abs_Rewrite (e1, e2, cond)) else None)"

code_datatype Abs_Rewrite

lemma "Abs_Rewrite (Rep_Rewrite r) = r"
  by (simp add: Rep_Rewrite_inverse)

(*lemma [code]: "Rep_Rewrite (Abs_Rewrite (e1, e2)) = (e1, e2)"*)

fun rewrite :: "Rewrite \<Rightarrow> IRExpr \<Rightarrow> IRExpr option" where
  "rewrite r e = (let (e1,e2,cond) = Rep_Rewrite r in 
                   (case match_tree e1 e of
                    Some \<sigma> \<Rightarrow> 
                      (if cond \<sigma> then Some (\<sigma> $ e2) else None) |
                    None \<Rightarrow> None))"

definition rewrite_valid :: "Rewrite \<Rightarrow> bool" where
  "rewrite_valid r = (let (e1,e2,cond) = Rep_Rewrite r in
    (\<forall>\<sigma> e. is_ground e \<longrightarrow> match_tree e1 e = Some \<sigma> \<longrightarrow> (e \<ge> (\<sigma> $ e2))))"

definition rewrite_valid_rep :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
  "rewrite_valid_rep e1 e2 = (vars e1 |\<subseteq>| vars e2 \<longrightarrow> (\<forall>\<sigma> e.  match_tree e1 e = Some \<sigma> \<longrightarrow> (e \<ge> (\<sigma> $ e2))))"



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
  IsIntegerStamp IRExpr |
  WellFormed IRExpr |
  IsStamp IRExpr Stamp |
  IsConstantValue IRExpr IRExpr "64 word" |
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
  "eval_condition (IsIntegerStamp e) = is_IntegerStamp (stamp_expr e)" |
  "eval_condition (WellFormed e) = wf_stamp e" |
  "eval_condition (IsStamp e s) = ((stamp_expr e) = s)" |
  "eval_condition (IsConstantValue e s v) = (e = ConstantExpr (IntVal (stp_bits (stamp_expr s)) v))" |
  "eval_condition (StampUnder e1 e2) = (stamp_under (stamp_expr e1) (stamp_expr e2))" |
  "eval_condition (UpMaskEquals e m) = (IRExpr_up e = m)" |
  "eval_condition (DownMaskEquals e m) = (IRExpr_down e = m)" |
  "eval_condition (UpMaskCancels e1 e2) = (((and (IRExpr_up e1) (IRExpr_up e2)) = 0))" |
  "eval_condition (PowerOf2 e) = False" |
  "eval_condition (IsBool e) = ((e = ConstantExpr (IntVal 32 0)) | (e = ConstantExpr (IntVal 32 0)))" |
  
  "eval_condition (Empty) = True" |

  "eval_condition (And sc1 sc2) = ((eval_condition sc1) \<and> (eval_condition sc2))" |
  "eval_condition (Not sc) = (\<not>(eval_condition sc))"


subsection \<open>Results\<close>

datatype Result =
  ExpressionResult IRExpr |
  forZero IRExpr

fun result_of :: "Result \<Rightarrow> IRExpr" where
  "result_of (ExpressionResult e) = e" |
  "result_of (forZero e) = ConstantExpr (IntVal (stp_bits (stamp_expr e)) 0)" 

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
definition join :: "('b \<Rightarrow> 'c \<times> MATCH) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'a \<times> MATCH) \<Rightarrow> 'b \<Rightarrow> 'a \<times> MATCH"
  (infixl "|>" 53) where
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
    (\<lambda>s. (s, match v (ConstantVarPattern c)))" |
  "match_pattern _ v = (\<lambda>s. (s, noop))"
snipend -

definition gen_pattern :: "IRExpr \<Rightarrow> VarName \<Rightarrow> MATCH" where
  "gen_pattern p v = snd (match_pattern p v ({|v|}, Map.empty))"

subsubsection \<open>Match Primitive Semantics\<close>
snipbegin \<open>Subst\<close>
type_synonym Subst = "VarName \<rightharpoonup> IRExpr"
snipend -

snipbegin \<open>evalmatch\<close>
fun eval_match :: "MATCH \<Rightarrow> Subst \<Rightarrow> Subst option" where
  "eval_match (match v (UnaryPattern op1 x)) s =
    (case s v of 
      Some (UnaryExpr op2 xe) \<Rightarrow>
        (if op1 = op2 then
          (if x \<in> dom s then
            (if s x = Some xe then Some s else None)
          else Some (s(x\<mapsto>xe)))
         else None) |
      Some _ \<Rightarrow> None |
      None \<Rightarrow> None)" |
  "eval_match (match v (BinaryPattern op1 x y)) s =
    (case s v of
      Some (BinaryExpr op2 xe ye) \<Rightarrow>
        (if op1 = op2 
          then 
          (if x \<in> dom s \<and> s x \<noteq> Some xe then None else 
          (if y \<in> dom s \<and> s y \<noteq> Some ye then None else 
          (if x \<in> dom s \<and> y \<in> dom s then Some s else
          (if x \<in> dom s then Some (s(y\<mapsto>ye)) else
          (if y \<in> dom s then Some (s(x\<mapsto>xe)) else
          Some (s(x\<mapsto>xe, y\<mapsto>ye)))))))
          else None) |
      Some _ \<Rightarrow> None |
      None \<Rightarrow> None)" |
  "eval_match (match v (ConditionalPattern c tb fb)) s =
    (case s v of
      Some (ConditionalExpr ce te fe) \<Rightarrow>
        (if c \<in> dom s \<and> s c \<noteq> Some ce then None else 
          (if tb \<in> dom s \<and> s tb \<noteq> Some te then None else
          (if fb \<in> dom s \<and> s fb \<noteq> Some fe then None else 
          (if c \<in> dom s \<and> tb \<in> dom s \<and> fb \<in> dom s then Some s else
          (if c \<in> dom s \<and> tb \<in> dom s then Some (s(fb\<mapsto>fe)) else
          (if c \<in> dom s \<and> fb \<in> dom s then Some (s(tb\<mapsto>te)) else
          (if tb \<in> dom s \<and> fb \<in> dom s then Some (s(c\<mapsto>ce)) else
          (if c \<in> dom s then Some (s(tb\<mapsto>te, fb\<mapsto>fe)) else
          (if tb \<in> dom s then Some (s(c\<mapsto>ce, fb\<mapsto>fe)) else
          (if fb \<in> dom s then Some (s(c\<mapsto>ce, tb\<mapsto>te)) else
          Some (s(c\<mapsto>ce, tb\<mapsto>te, fb\<mapsto>fe)))))))))))) |
      Some _ \<Rightarrow> None |
      None \<Rightarrow> None)" |
  "eval_match (match v (ConstantPattern c1)) s =
    (case s v of 
      Some (ConstantExpr c2) \<Rightarrow>
        (if c1 = c2 then Some s else None) |
      Some _ \<Rightarrow> None |
      None \<Rightarrow> None)" |
  "eval_match (equality v1 v2) s =
    (if v1 \<in> dom s \<and> v2 \<in> dom s \<and> s v1 = s v2 then Some s else None)" |
  "eval_match (andthen m1 m2) s =
      (case eval_match m1 s of 
        None \<Rightarrow> None |
        Some s' \<Rightarrow> eval_match m2 s')" |
  "eval_match noop s = Some s" |
  "eval_match (condition sc) s = (if eval_condition sc then Some s else None)" |
  "eval_match _ s = None"
snipend -

(*
fun IROnly :: "Substitution option \<Rightarrow> Subst option" where
  "IROnly (Some s) = Some (map_of (map (\<lambda>k. (k, (s_expr (the (s k))))) (sorted_list_of_set (dom s))))" |
  "IROnly None = None"

lemma "IROnly (match_tree p e) = eval_match (gen_pattern p v) [v\<mapsto>e]"*)


subsection \<open>Combining Rules\<close>

snipbegin \<open>Rules\<close>
datatype Rules =
  base Result |
  cond MATCH Rules (infixl "?" 52) |
  else Rules Rules (infixl "else" 50) |
  seq Rules Rules (infixl "\<then>" 49) |
  choice "Rules list"
snipend -

text \<open>Use the scope of a generated match to replace real variable names with aliases in the rewrite result.\<close>
snipbegin \<open>groundresult\<close>
fun ground_expr :: "IRExpr \<Rightarrow> Scope \<Rightarrow> IRExpr" where
  "ground_expr (UnaryExpr op e) s = 
    UnaryExpr op (ground_expr e s)" |
  "ground_expr (BinaryExpr op e1 e2) s = 
    BinaryExpr op (ground_expr e1 s) (ground_expr e2 s)" |
  "ground_expr (ConditionalExpr b e1 e2) s = 
    ConditionalExpr (ground_expr b s) (ground_expr e1 s) (ground_expr e2 s)" |
  "ground_expr (VariableExpr vn st) (s, m) = 
    (case m vn of None \<Rightarrow> VariableExpr vn st 
                | Some v' \<Rightarrow> VariableExpr v' st)" |
  "ground_expr e s = e"

fun ground_result :: "Result \<Rightarrow> Scope \<Rightarrow> Result" where
  "ground_result (ExpressionResult e) s = ExpressionResult (ground_expr e s)" |
  "ground_result (forZero e) s = forZero (ground_expr e s)"
snipend -

fun ground_condition :: "SideCondition \<Rightarrow> Scope \<Rightarrow> SideCondition" where
  "ground_condition (IsConstantExpr p) s = (IsConstantExpr (ground_expr p s))" |
  "ground_condition (IsIntegerStamp p) s = (IsIntegerStamp (ground_expr p s))" |
  "ground_condition (WellFormed st) s = (WellFormed st)" |
  "ground_condition (IsStamp e st) s = (IsStamp (ground_expr e s) st)" |
  "ground_condition (IsConstantValue e s' v) s = (IsConstantValue (ground_expr e s) (ground_expr s' s) v)" |
  "ground_condition (StampUnder e1 e2) s = (StampUnder (ground_expr e1 s) (ground_expr e2 s))" |
  "ground_condition (UpMaskEquals e m) s = (UpMaskEquals (ground_expr e s) m)" |
  "ground_condition (DownMaskEquals e m) s = (DownMaskEquals (ground_expr e s) m)" |
  "ground_condition (UpMaskCancels e1 e2) s = (UpMaskCancels (ground_expr e1 s) (ground_expr e2 s))" |
  "ground_condition (PowerOf2 e) s = (PowerOf2 (ground_expr e s))" |
  "ground_condition (IsBool e) s = (IsBool (ground_expr e s))" |
  "ground_condition (And sc1 sc2) s = And (ground_condition sc1 s) (ground_condition sc2 s)" |
  "ground_condition (Not sc) s = Not (ground_condition sc s)" |
  "ground_condition (Empty) s = Empty"

snipbegin \<open>generate\<close>
fun generate :: "IRExpr \<Rightarrow> Result \<Rightarrow> SideCondition \<Rightarrow> Rules" where
  "generate p r sc = 
    (let (s, m) = match_pattern p STR ''e'' ({||}, (\<lambda>x. None))
     in ((m && condition (ground_condition sc s)) ? (base (ground_result r s))))"
snipend -

subsubsection \<open>Rules Semantics\<close>
definition start_unification where
  "start_unification e = ((\<lambda>x. None)(STR ''e'' := Some e))"

text \<open>Replace any variable expressions with value in a substitution.\<close>
fun eval_expr :: "IRExpr \<Rightarrow> Subst \<Rightarrow> IRExpr option" where
  "eval_expr (VariableExpr v s) u = u v" |
  "eval_expr (UnaryExpr op e) u = (case (eval_expr e u)
    of None \<Rightarrow> None | Some e' \<Rightarrow> Some (UnaryExpr op e'))" |
  "eval_expr (BinaryExpr op e1 e2) u = (case (eval_expr e1 u)
    of None \<Rightarrow> None | Some e1' \<Rightarrow> 
    (case (eval_expr e2 u)
      of None \<Rightarrow> None | Some e2' \<Rightarrow> Some (BinaryExpr op e1' e2')))" |
  "eval_expr (ConditionalExpr e1 e2 e3) u = (case (eval_expr e1 u)
    of None \<Rightarrow> None | Some e1' \<Rightarrow>
    (case (eval_expr e2 u)
      of None \<Rightarrow> None | Some e2' \<Rightarrow>
        (case (eval_expr e2 u)
          of None \<Rightarrow> None | Some e3' \<Rightarrow> Some (ConditionalExpr e1' e2' e3'))))" |
  "eval_expr e u = Some e"

fun eval_result :: "Result \<Rightarrow> Subst \<Rightarrow> IRExpr option" where
  "eval_result (ExpressionResult e) s = (eval_expr e s)" |
  "eval_result (forZero e) s = (case eval_expr e s of
    None \<Rightarrow> None |
    Some r \<Rightarrow> Some (ConstantExpr (IntVal (stp_bits (stamp_expr r)) 0)))"

lemma remove1_size:
  "x \<in> set xs \<Longrightarrow> size (remove1 x xs) < size xs"
  by (metis diff_less length_pos_if_in_set length_remove1 zero_less_one)

inductive eval_rules :: "Rules \<Rightarrow> Subst \<Rightarrow> IRExpr option \<Rightarrow> bool" where
  \<comment> \<open>Evaluate the result\<close>
  "eval_rules (base e) u (eval_result e u)" |

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


lemma choice_join:
  assumes "eval_rules (a) u e = eval_rules (f a) u e"
  assumes "eval_rules (choice rules) u e = eval_rules (choice (map f rules)) u e"
  shows "eval_rules (choice (a # rules)) u e = eval_rules (choice (map f (a # rules))) u e"
  using assms
  by (smt (verit, ccfv_threshold) choiceE eval_rules.intros(6) eval_rules.intros(7) list.map_disc_iff list.set_intros(1) list.set_intros(2) list.simps(9) option.distinct(1) set_ConsD)


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
  apply fastforce
  by simp+


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


lemma match_def_affect:
  assumes "eval_match m u = Some a"
  shows "\<forall>v. v \<notin> def_vars m \<longrightarrow> u v = a v"
using assms proof (induction m u arbitrary: a rule: eval_match.induct)
  case (1 v op1 x s)
  have "\<exists>e. a = s(x\<mapsto>e)"
    by (smt (verit) "1" IRExpr.case_eq_if eval_match.simps(1) fun_upd_triv option.case_eq_if option.distinct(1) option.inject)
  then show ?case
    unfolding def_vars.simps by auto
next
  case (2 v op1 x y s)
  have "\<exists>e1 e2. a = s(y\<mapsto>e1, x\<mapsto>e2)"
    by (smt (verit) "2" IRExpr.case_eq_if eval_match.simps(2) fun_upd_idem_iff fun_upd_twist option.case_eq_if option.distinct(1) option.sel)
  then show ?case
    by fastforce
next
  case (3 v c tb fb s)
  have "\<exists>e1 e2 e3. a = s(c\<mapsto>e1, tb\<mapsto>e2, fb\<mapsto>e3)"
    by (smt (verit) "3" IRExpr.case_eq_if eval_match.simps(3) fun_upd_idem_iff fun_upd_twist option.case_eq_if option.distinct(1) option.sel)
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


lemma eval_match_subset:
  assumes "eval_match m u = Some a"
  assumes "valid_match m"
  shows "u \<subseteq>\<^sub>m a"
  using assms proof (induction m arbitrary: u a)
  case (match x1 x2)
  then show ?case proof (cases x2)
    case (UnaryPattern x11 x12)
    then show ?thesis using match apply simp
      by (smt (verit) IRExpr.case_eq_if fun_upd_other map_le_def option.case_eq_if option.distinct(1) option.inject)
  next
    case (BinaryPattern x21 x22 x23)
    then show ?thesis using match apply simp
      by (smt (verit) IRExpr.case_eq_if fun_upd_other map_le_def option.case_eq_if option.distinct(1) option.sel)
  next
    case (ConditionalPattern x31 x32 x33)
    then show ?thesis using match apply simp
      by (smt (verit) IRExpr.case_eq_if fun_upd_def map_le_def option.case_eq_if option.distinct(1) option.sel)
  next
    case (VariablePattern x4)
    then show ?thesis 
      using match.prems(1) by force
  next
    case (ConstantPattern x5)
    then show ?thesis 
      by (metis def_vars.simps(1) empty_iff map_le_def match.prems(1) match_def_affect pattern_variables.simps(5))
  next
    case (ConstantVarPattern x6)
    then show ?thesis 
      using match.prems(1) by auto
  qed
next
  case (equality x1 x2)
  then show ?case 
    by (metis eval_match.simps(5) map_le_refl option.distinct(1) option.sel)
next
  case (andthen m1 m2)
  then show ?case
    by (metis eval_match.simps(6) map_le_trans not_None_eq option.case_eq_if option.sel valid_match.simps(4))
next
  case (condition x)
  then show ?case
    using match_def_affect by fastforce
next
  case noop
  then show ?case by simp
qed

lemma lift_idempotence:
  assumes "eval_match m a' = Some a'"
  assumes "a' \<subseteq>\<^sub>m a"
  assumes "valid_match m"
  shows "eval_match m a = Some a"
  using assms proof (induction m arbitrary: a a')
  case (match x1 x2)
  then show ?case proof (cases x2)
    case (UnaryPattern x11 x12)
    then show ?thesis using match apply simp
      by (smt (verit) IRExpr.case_eq_if domI domIff fun_upd_idem_iff map_le_def option.case_eq_if option.sel)
  next
    case (BinaryPattern x21 x22 x23)
    then show ?thesis using match apply simp
      by (smt (verit) IRExpr.case_eq_if domIff map_le_def map_upd_Some_unfold option.case_eq_if option.distinct(1) option.sel)
  next
    case (ConditionalPattern x31 x32 x33)
    then show ?thesis using match apply simp
      by (smt (verit) IRExpr.case_eq_if domIff map_le_def map_upd_Some_unfold option.case_eq_if option.distinct(1) option.inject)
  next
    case (VariablePattern x4)
    then show ?thesis
      using match.prems(1) by fastforce
  next
    case (ConstantPattern x5)
    then show ?thesis using match apply simp
      by (smt (verit) IRExpr.case_eq_if domIff map_le_def option.case_eq_if option.distinct(1))
  next
    case (ConstantVarPattern x6)
    then show ?thesis
      using match.prems(1) by auto
  qed
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
    using andthen.prems(3) eval_match_subset valid_match.simps(4) by blast
  then show ?case
    by (metis m1eval m2eval andthen.IH(1) andthen.IH(2) andthen.prems(2) andthen.prems(3) eval_match.simps(6) eval_match_subset map_le_antisym option.simps(5) valid_match.simps(4))
next
  case (condition x)
  then show ?case
    by (metis eval_match.simps(8) option.distinct(1))
next
  case noop
  then show ?case by simp
qed

lemma idempotent_match:
  assumes "eval_match m u = Some a"
  assumes "valid_match m"
  shows "eval_match m a = Some a"
  using assms proof (induction m arbitrary: u a)
  case (match x1 x2)
  then show ?case proof (cases x2)
    case (UnaryPattern x11 x12)
    then show ?thesis using match apply simp
      by (smt (verit) IRExpr.case_eq_if fun_upd_other fun_upd_same map_upd_triv option.case_eq_if option.distinct(1) option.sel)
  next
    case (BinaryPattern x21 x22 x23)
    then show ?thesis using match apply simp
      by (smt (verit) IRExpr.case_eq_if fun_upd_other fun_upd_same map_upd_triv option.case_eq_if option.distinct(1) option.sel)
  next
    case (ConditionalPattern x31 x32 x33)
    then show ?thesis using match apply simp
      by (smt (verit) IRExpr.case_eq_if domI domIff fun_upd_def option.case_eq_if option.sel)
  next
    case (VariablePattern x4)
    then show ?thesis
      using match.prems(1) by auto
  next
    case (ConstantPattern x5)
    then show ?thesis using match apply simp
      by (smt (verit) IRExpr.case_eq_if option.case_eq_if option.sel)
  next
    case (ConstantVarPattern x6)
    then show ?thesis
      using match.prems(1) by auto
  qed
next
  case (equality x1 x2)
  then show ?case
    by (metis eval_match.simps(5) option.sel)
next
  case (andthen m1 m2)
  obtain a' where m1eval: "eval_match m1 u = Some a'"
    using andthen.prems(1) by fastforce
  have m1idem: "eval_match m1 a' = Some a'"
    using andthen.IH(1) andthen.prems(2) m1eval valid_match.simps(4) by blast
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
    using eval_match_subset m2eval validm2 by simp
  then have "eval_match m1 a = Some a"
    using m1idem lift_idempotence validm1 by simp
  then show ?case
    by (simp add: m2idem)
next
  case (condition x)
  then show ?case
    by (metis eval_match.simps(8))
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

lemma find_common_size:
  assumes "(find_common m r) \<noteq> None"
  shows "size (the (find_common m r)) < size r"
  using assms apply (induction r rule: find_common.induct)
  apply simp+ apply fastforce by simp+

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
    (generate_expression e1) @ '' & '' @ (generate_expression e2)" |
  "generate_expression (Unsupported x) = x"

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

fun export_result :: "Result \<Rightarrow> Expression" where
  "export_result (ExpressionResult e) = export_irexpr e" |
  "export_result (forZero e) = Constructor ''ConstantNode'' [IntegerConstant 0]"

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
  "export_condition (IsIntegerStamp e) = (InstanceOf (stampOf (export_irexpr e)) ''IntegerStamp'' STR ''t'')" |
  "export_condition (WellFormed s) = TrueValue" |
  "export_condition (IsStamp e s) =
    (Equal (stampOf (export_irexpr e)) (export_stamp s))" |
  "export_condition (IsConstantValue e s v) =
    (And
      (InstanceOf (export_irexpr e) ''ConstantNode'' STR ''t'')
      (Equal (MethodCall (export_irexpr e) ''getConstantValue'' []) (IntegerConstant (sint v))))" |
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
    Branch (Equal (MethodCall (Ref (v + STR ''c'')) ''getValue'' []) (Ref var)) s" |
  "export_assignments v (VariablePattern var) s =
    Return (Unsupported ''export_assignments for VariablePattern'')" 

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


fun export_rules :: "Rules \<Rightarrow> Statement" where
  "export_rules (base e) = Return (export_result e)" |
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
    (ExpressionResult (var ''x''))
    (Empty)"

text \<open>@{text "(x - y) + y \<longrightarrow> x"}\<close>
definition RedundantSub where
  "RedundantSub = generate 
    (BinaryExpr BinAdd
      (BinaryExpr BinSub (var ''x'') (var ''y''))
      (var ''y''))
    (ExpressionResult (var ''x''))
    (Empty)"

text \<open>@{text "x + -e \<longmapsto> x - e"}\<close>
definition AddLeftNegateToSub where
  "AddLeftNegateToSub = generate 
    (BinaryExpr BinAdd
      (var ''x'')
      (UnaryExpr UnaryNeg (var ''e'')))
    (ExpressionResult (BinaryExpr BinSub (var ''x'') (var ''e'')))
    (Empty)"

corollary
  "NestedNot =
   (MATCH.match STR ''e'' (UnaryPattern UnaryNot STR ''a'') &&
    (MATCH.match STR ''a'' (UnaryPattern UnaryNot STR ''az'') && noop) && condition Empty) ?
      base (ExpressionResult (VariableExpr STR ''az'' VoidStamp))"
  by eval

value "
generate 
    (BinaryExpr BinAdd
      (var ''x'')
      (var ''x''))
    (ExpressionResult (BinaryExpr BinSub (var ''x'') (var ''e'')))
    (Empty)
"

corollary
  "RedundantSub =
   (MATCH.match STR ''e'' (BinaryPattern BinAdd STR ''a'' STR ''b'') &&
    (MATCH.match STR ''a'' (BinaryPattern BinSub STR ''az'' STR ''bz'') && noop && noop) &&
      STR ''bz'' == STR ''b'' && condition Empty) ?
        base (ExpressionResult (VariableExpr STR ''az'' VoidStamp))"
  by eval

corollary
  "AddLeftNegateToSub =
   (MATCH.match STR ''e'' (BinaryPattern BinAdd STR ''a'' STR ''b'') && noop &&
    (MATCH.match STR ''b'' (UnaryPattern UnaryNeg STR ''az'') && noop) && condition Empty) ?
      base (ExpressionResult (BinaryExpr BinSub 
            (VariableExpr STR ''a'' VoidStamp)
            (VariableExpr STR ''az'' VoidStamp)))"
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
      (STR ''bz'' == STR ''b'' ? (condition Empty ? base (ExpressionResult (VariableExpr STR ''az'' VoidStamp))))))) else
   MATCH.match STR ''e'' (BinaryPattern BinAdd STR ''a'' STR ''b'') ?
   (noop ?
    (MATCH.match STR ''b'' (UnaryPattern UnaryNeg STR ''az'') ?
     (noop ?
      (condition Empty ?
       base
        (ExpressionResult (BinaryExpr BinSub (VariableExpr STR ''a'' VoidStamp)
          (VariableExpr STR ''az'' VoidStamp))))))))"
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
      base (ExpressionResult (VariableExpr STR ''az'' VoidStamp)))
    else
    MATCH.match STR ''b'' (UnaryPattern UnaryNeg STR ''az'') ?
     base (ExpressionResult (BinaryExpr BinSub (VariableExpr STR ''a'' VoidStamp) (VariableExpr STR ''az'' VoidStamp))))"
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
    (ExpressionResult (var ''x''))
    (Empty)"

value "Identity"
value "export_rules (optimized_export (Identity))"

text \<open>@{text "const x * const y \<longrightarrow> const (x * y)"}\<close>
definition Evaluate where
  "Evaluate = generate 
    (BinaryExpr BinMul
      (ConstantVar STR ''x'')
      (ConstantVar STR ''y''))
    (ExpressionResult (ConstantVar STR ''x''))
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
    (ExpressionResult (BinaryExpr BinLeftShift (var ''x'') (ConstantVar STR ''y'')))
    (PowerOf2 (ConstantVar STR ''y''))"
(* doesn't support constant evaluation *)
value "Shift"


text \<open>@{text "const x * y \<longrightarrow> y * const x when NotConst y"}\<close>
definition LeftConst where
  "LeftConst = generate 
    (BinaryExpr BinMul
      (ConstantVar STR ''x'')
      (var ''y''))
    (ExpressionResult (BinaryExpr BinMul (var ''y'') (ConstantVar STR ''x'')))
    (Not (IsConstantExpr (var ''y'')))"
(* doesn't support constant evaluation *)
value "LeftConst"


value "(optimized_export (optimized_export (LeftConst \<then> (Evaluate else (Identity else Shift)))))"

end
