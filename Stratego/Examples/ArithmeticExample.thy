theory ArithmeticExample
  imports Arithmetic "../JavaExport"
begin

context Rewritable begin
termination match_pattern sorry
end

setup \<open>Locale_Code.open_block\<close>
interpretation Arithmetic: Rewritable
  size_Arithmetic
  
  eval_condition ground_condition is_ground_condition
  eval_transformer ground_transformer is_ground_transformer

  subexprs_Arithmetic chain_Arithmetic rewrite_Arithmetic
  match_Arithmetic

  varof_Arithmetic var_Arithmetic
proof
  fix c :: ArithmeticCondition
  fix a' a :: "(string \<rightharpoonup> Arithmetic)"
  assume sub: "a' \<subseteq>\<^sub>m a"
  assume ground: "is_ground_condition (ground_condition c a')"
  show "ground_condition c a' = ground_condition c a"
    using sub ground 
    apply (induction c a rule: ground_condition.induct)
    defer defer apply simp+
    subgoal premises prem for e f
    proof (cases "a' e")
      case None
      then have "\<not>(is_ground_condition (case a' e of None \<Rightarrow> IsSub (Variable e) | Some x \<Rightarrow> IsSub x))"
        by simp
      then show ?thesis using prem by blast
    next
      case (Some a)
      then have "a' e = f e" using prem(1)
        by (metis domIff map_le_def option.distinct(1))
      then show ?thesis by simp
    qed
    apply simp
    subgoal premises prem for e f
    proof (cases "a' e")
      case None
      then have "\<not>(is_ground_condition (case a' e of None \<Rightarrow> IsNumber (Variable e) | Some x \<Rightarrow> IsNumber x))"
        by simp
      then show ?thesis using prem by blast
    next
      case (Some a)
      then have "a' e = f e" using prem(1)
        by (metis domIff map_le_def option.distinct(1))
      then show ?thesis by simp
    qed
    done
next
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
next
  fix c :: "ArithmeticCondition"
  have lhs: "eval_condition c = None \<Longrightarrow> (\<not> is_ground_condition c)"
  subgoal premises e
  proof (cases c)
    case (IsSub x1)
    then show ?thesis using e by (cases x1; auto) 
  next
    case (IsNumber x2)
    then show ?thesis using e by (cases x2; auto)
  qed
  done
  have rhs: "(\<not> is_ground_condition c) \<Longrightarrow> eval_condition c = None"
  subgoal premises e
  proof (cases c)
    case (IsSub x1)
    then show ?thesis using e by (cases x1; auto) 
  next
    case (IsNumber x2)
    then show ?thesis using e by (cases x2; auto)
  qed
  done
  from lhs rhs show "eval_condition c = None \<equiv> (\<not> is_ground_condition c)"
    by linarith
qed
setup \<open>Locale_Code.close_block\<close>



subsubsection \<open>Example: Match Pattern\<close>

definition "join = Arithmetic.join"
definition "generate = Arithmetic.generate"
definition "match_pattern = Arithmetic.match_pattern"
definition "optimized_export = Arithmetic.optimized_export"
definition "var = var_Arithmetic"

export_code "optimized_export" checking SML


export_code "match_pattern" checking SML

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
    (Result (var ''x''))"

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
    (Plus (var ''x'') (var ''y''))"
(* doesn't support constant evaluation *)
value "Evaluate"
value "(optimized_export (Evaluate))"

text \<open>@{text "const x + y \<longrightarrow> y + const x when NotConst y"}\<close>
definition LeftConst where
  "LeftConst = generate 
    (Add
      (var ''x'')
      (var ''y''))
    (Plus (var ''y'') (var ''x''))"
value "LeftConst"

value "(choice [LeftConst, Evaluate, Identity])"
text "@{value[display] \<open>choice [LeftConst, Evaluate, Identity]\<close>}"
value "(optimized_export (choice [LeftConst, Evaluate, Identity]))"
text "@{value[display] \<open>(optimized_export (choice [LeftConst, Evaluate, Identity]))\<close>}"
value "(optimized_export (optimized_export (choice [LeftConst, Evaluate, Identity])))"
text "@{value[display] \<open>(optimized_export (optimized_export (choice [LeftConst, Evaluate, Identity])))\<close>}"



fun class_of_term_Arithmetic :: "Arithmetic \<Rightarrow> string" where
  "class_of_term_Arithmetic (Add x y) = ''AddNode''" |
  "class_of_term_Arithmetic (Sub x y) = ''SubNode''" |
  "class_of_term_Arithmetic (UMinus x) = ''UnaryMinusNode''" |
  "class_of_term_Arithmetic (Number v) = ''ConstantNode''" |
  "class_of_term_Arithmetic (Variable s) = ''VariableNode''"

datatype JavaCheck =
  CallMethod1 |
  CallMethod2 |
  MethodCall string string |
  Construct string "JavaCheck list" |
  VariableExpr string

instantiation "JavaCheck" :: JavaExpression
begin
fun expToJava_JavaCheck where
  "expToJava_JavaCheck CallMethod1 = ''I'm asserting you're a number''" |
  "expToJava_JavaCheck CallMethod2 = ''I'm asserting you're a subnode''" |
  "expToJava_JavaCheck (MethodCall ob m) = ob @ ''.'' @ m @ ''()''" |
  "expToJava_JavaCheck (Construct class args) = ''new '' @ class @ ''('' @ param_list (map expToJava_JavaCheck args) @ '')''" |
  "expToJava_JavaCheck (VariableExpr v) = v"
instance ..
end

fun generate_condition_Arithmetic :: "ArithmeticCondition \<Rightarrow> JavaCheck" where
  "generate_condition_Arithmetic (IsSub e) = CallMethod2" |
  "generate_condition_Arithmetic (IsNumber e) = CallMethod1"

fun generate_Arithmetic :: "Arithmetic \<Rightarrow> JavaCheck" where
  "generate_Arithmetic (Add x y) = Construct ''AddNode'' (map generate_Arithmetic [x, y])" |
  "generate_Arithmetic (Sub x y) = Construct ''SubNode'' (map generate_Arithmetic [x, y])" |
  "generate_Arithmetic (UMinus x) = Construct ''UnaryMinusNode'' (map generate_Arithmetic [x])" |
  "generate_Arithmetic (Number v) = Construct ''ConstantNode'' []" |
  "generate_Arithmetic (Variable s) = VariableExpr s"

fun generate_result_Arithmetic :: "Transformer \<Rightarrow> JavaCheck" where
  "generate_result_Arithmetic (UnaryMinus e) = CallMethod1" |
  "generate_result_Arithmetic (Plus e1 e2) = CallMethod2" |
  "generate_result_Arithmetic (Result e) = generate_Arithmetic e"

fun generate_access_Arithmetic :: "VarName \<Rightarrow> Arithmetic \<Rightarrow> JavaCheck list" where
  "generate_access_Arithmetic v (Add x y) = 
    [(MethodCall v ''getX''),
     (MethodCall v ''getY'')]" |
  "generate_access_Arithmetic v (Sub x y) = 
    [(MethodCall v ''getX''),
     (MethodCall v ''getY'')]" |
  "generate_access_Arithmetic v (UMinus x) = [(MethodCall v ''getValue'')]" |
  "generate_access_Arithmetic v (Number val) = []" |
  "generate_access_Arithmetic v (Variable s) = []"

setup \<open>Locale_Code.open_block\<close>
interpretation Arithmetic: JavaTarget
  size_Arithmetic
  "eval_condition"
  "ground_condition"
  "is_ground_condition"
  "eval_transformer"
  "ground_transformer"
  "is_ground_transformer"
  subexprs_Arithmetic
  chain_Arithmetic
  rewrite_Arithmetic
  match_Arithmetic
  varof_Arithmetic
  var_Arithmetic
  
  class_of_term_Arithmetic
  generate_condition_Arithmetic
  generate_result_Arithmetic
  generate_access_Arithmetic
  by standard
setup \<open>Locale_Code.close_block\<close>

definition "export_rules = Arithmetic.export_rules"
value "export_rules"

value "export_rules (optimized_export (choice [Identity, Evaluate]))"
value "export_rules (optimized_export (Identity \<then> Evaluate))"

value "statementToJava 0 (export_rules (optimized_export (choice [Identity, Evaluate])))"


end