theory JavaExport
  imports CompileRewrite
begin

class JavaStatement =
  fixes statementToJava :: "nat \<Rightarrow> 'a \<Rightarrow> string"

class JavaExpression =
  fixes expToJava :: "'a \<Rightarrow> string"

type_synonym ClassName = string
type_synonym VariableName = string
type_synonym MethodName = string

datatype 'a BaseExpressions =
  Ref VariableName |
  IntegerConstant int |
  TrueValue |
  FalseValue |
  MethodCall "'a::JavaExpression" MethodName "'a::JavaExpression list" |
  Constructor ClassName "'a::JavaExpression list" |
  InstanceOf "'a BaseExpressions" ClassName VariableName |
  Equal "'a BaseExpressions" "'a BaseExpressions" |
  ConditionExpression 'a (* |
  Less Expression Expression |
  Negate Expression |
  And Expression Expression |
  BitAnd Expression Expression |
  Unsupported string*)

datatype ('a) Statement =
  Assignment VariableName "'a::JavaExpression" |
  Branch "'a::JavaExpression" "('a) Statement" |
  Return "'a::JavaExpression" |
  Sequential "('a) Statement list"

fun intersperse :: "string \<Rightarrow> string list \<Rightarrow> string list" where
  "intersperse i es = foldr (\<lambda>x ys . x # (if ys = [] then ys else i # ys)) es []"

fun param_list :: "string list \<Rightarrow> string" where
  "param_list es = (foldr (@) (intersperse '', '' es) '''')"

fun generate_expression :: "('a::JavaExpression) BaseExpressions \<Rightarrow> string" where
  "generate_expression (Ref v) = v" |
  "generate_expression (IntegerConstant n) = ''0''" | (*TODO FIX*)
  "generate_expression TrueValue = ''true''" |
  "generate_expression FalseValue = ''false''" |
  "generate_expression (MethodCall e mn ps) = 
    (expToJava e) @ ''.'' @ mn @ ''('' @ param_list (map expToJava ps) @ '')''" |
  "generate_expression (Constructor cn ps) =
    ''new '' @ cn @ ''('' @ param_list (map expToJava ps) @ '')''" |
  "generate_expression (InstanceOf e cn v) =
    (generate_expression e) @ '' instanceof '' @ cn @ '' '' @ v" |
  "generate_expression (Equal e1 e2) =
    (generate_expression e1) @ '' == '' @ (generate_expression e2)" |
  "generate_expression (ConditionExpression e) =
    (expToJava e)"

fun indent :: "nat \<Rightarrow> string" where
  "indent 0 = ''''" |
  "indent (Suc n) = '' '' @ indent n"

fun generate_statement :: "nat \<Rightarrow> ('a::JavaExpression) Statement \<Rightarrow> string" where
  "generate_statement i (Assignment v e) = indent i @
    ''var '' @ v @ '' = '' @ expToJava e @ '';\<newline>''" |
  "generate_statement i (Branch c s) = indent i @
    ''if ('' @ expToJava c @ '') {\<newline>'' @ generate_statement (i + 4) s @ 
    indent i @ ''}\<newline>''" |
  "generate_statement i (Return e) = indent i @
    ''return '' @ expToJava e @ '';\<newline>''" |
  "generate_statement i (Sequential ss) = 
    foldr (@) (map (generate_statement i) ss) ''''"


instantiation "BaseExpressions" :: (type) JavaExpression
begin
definition "expToJava_BaseExpressions = generate_expression" 
instance ..
end

instantiation "Statement" :: (type) JavaStatement
begin
definition "statementToJava_Statement = generate_statement" 
instance ..
end
 

locale JavaTarget = CompiledRewrites +
  fixes class_of_term :: "'a \<Rightarrow> string"
  and generate_condition :: "'b \<Rightarrow> 'e::JavaExpression"
  and generate_result :: "'c \<Rightarrow> 'e::JavaExpression"
  and generate_access :: "VarName \<Rightarrow> 'a \<Rightarrow> 'e::JavaExpression list"
  (*and generate_assignment :: "VarName \<Rightarrow> 'a \<Rightarrow> ('e BaseExpressions) Statement \<Rightarrow> ('e BaseExpressions) Statement"*)
begin

fun generate_assignment :: 
  "VarName \<Rightarrow> 'a \<Rightarrow> ('e BaseExpressions) Statement \<Rightarrow> ('e BaseExpressions) Statement" where
  "generate_assignment v e s =
    Sequential (
      [Assignment e' (ConditionExpression ((generate_access (v @ ''c'') e)!i)).
        (i, e') <- (enumerate 0 (pattern_variables e))] @ [s])"

function (sequential) export_match :: "('a, 'b) MATCH \<Rightarrow> ('e BaseExpressions) Statement 
  \<Rightarrow> ('e BaseExpressions) Statement" where
  "export_match (match v p) r  = 
    Branch (InstanceOf (Ref v) (class_of_term p) (v @ ''c''))
      (Sequential [(generate_assignment v p r)])" |
  "export_match (andthen m1 m2) r = 
    export_match m1 (export_match m2 r)" |
  "export_match (equality v1 v2) r = 
    Branch (Equal (Ref v1) (Ref v2)) r" |
  "export_match (cond sc) r = 
    Branch (ConditionExpression (generate_condition sc)) r" |
  "export_match noop r = r"
  apply pat_completeness+
  by simp+

fun size_conditional :: "(('a, 'b) MATCH \<times> ('e BaseExpressions) Statement) \<Rightarrow> nat" where
  "size_conditional ((cond c), s) = size_match (cond c) + size_condition c" |
  "size_conditional (m, s) = size_match m"

termination export_match
  apply (relation "measures [size_conditional]") apply simp apply simp sorry


fun export_rules :: "('a, 'b, 'c) Rules \<Rightarrow> ('e BaseExpressions) Statement" where
  "export_rules (base e) = Return (ConditionExpression (generate_result e))" |
  "export_rules (cond' m r) = export_match m (export_rules r)" |
  "export_rules (r1 else r2) = Sequential [export_rules r1, export_rules r2]" |
  "export_rules (choice rules) = Sequential (map export_rules rules)" |
  "export_rules (r1 \<then> r2) = Sequential [export_rules r1, export_rules r2]" (* TODO: should modify e *)
end




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

(*
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
*)

setup \<open>Locale_Code.open_block\<close>
interpretation Arithmetic: JavaTarget
  size_Arithmetic
  "eval_condition"
  "ground_condition"
  "is_ground_condition"
  "eval_transformer"
  "ground_transformer"
  "is_ground_transformer"
  rewrite_Arithmetic
  match_Arithmetic
  varof_Arithmetic
  var_Arithmetic
  subexprs_Arithmetic
  chain_Arithmetic
  class_of_term_Arithmetic
  generate_condition_Arithmetic
  generate_result_Arithmetic
  generate_access_Arithmetic
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

definition "export_rules = Arithmetic.export_rules"


value "export_rules"

definition "join = Arithmetic.join"
(*definition "compile' = ArithmeticCompiled.compile'"*)
definition "generate = Arithmetic.generate"
definition "match_pattern = Arithmetic.match_pattern"
definition "optimized_export = Arithmetic.optimized_export"

export_code "optimized_export" checking SML

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


value "export_rules (optimized_export (choice [Identity, Evaluate]))"

value "statementToJava 0 (export_rules (optimized_export (choice [Identity, Evaluate])))"

end