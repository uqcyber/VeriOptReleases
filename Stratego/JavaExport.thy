theory JavaExport
  imports MatchPattern
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
  MethodCall "'a::JavaExpression" MethodName "'a::JavaExpression list"
    ("_._(_)") |
  Constructor ClassName "'a::JavaExpression list"
    ("new _(_)") |
  InstanceOf "'a BaseExpressions" ClassName VariableName
    ("_ instanceof _ _")|
  Equal "'a BaseExpressions" "'a BaseExpressions" 
    (infix "==" 58)|
  ConditionExpression 'a

datatype ('a) Statement =
  Assignment VariableName "'a::JavaExpression" (infix ":=" 56) |
  Branch "'a::JavaExpression" "('a) Statement" ("if _ {(2//_)//}") |
  Return "'a::JavaExpression" |
  Sequential "('a) Statement list"

syntax
  "_seq" :: "'a Statement \<Rightarrow> 'a Statement => 'a Statement" (infixr ";//" 55)

translations
  "_seq x y" == "CONST Sequential [x, y]"

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
 

locale JavaTarget = Rewritable +
  fixes class_of_term :: "'a \<Rightarrow> string"
  and generate_condition :: "'b \<Rightarrow> 'e::JavaExpression"
  and generate_result :: "'c \<Rightarrow> 'e::JavaExpression"
  and generate_access :: "VarName \<Rightarrow> 'a \<Rightarrow> 'e::JavaExpression list"
begin

fun generate_assignment :: 
  "VarName \<Rightarrow> 'a \<Rightarrow> ('e BaseExpressions) Statement \<Rightarrow> ('e BaseExpressions) Statement" where
  "generate_assignment v e s =
    Sequential (
      [(e' := (ConditionExpression ((generate_access (v @ ''c'') e)!i))).
        (i, e') <- (enumerate 0 (pattern_variables e))] @ [s])"

fun export_match :: "('a, 'b) MATCH \<Rightarrow> ('e BaseExpressions) Statement 
  \<Rightarrow> ('e BaseExpressions) Statement" where
  "export_match (match v p) r  = 
    if ((Ref v) instanceof (class_of_term p) (v @ ''c'')) {
      (Sequential [(generate_assignment v p r)])
    }" |
  "export_match (andthen m1 m2) r = 
    export_match m1 (export_match m2 r)" |
  "export_match (equality v1 v2) r = 
    if (Equal (Ref v1) (Ref v2)) {
      r
    }" |
  "export_match (cond sc) r = 
    if (ConditionExpression (generate_condition sc)) {
      r
    }" |
  "export_match noop r = r"

fun generate_rules :: "VarName option \<Rightarrow> ('a, 'b, 'c) Rules \<Rightarrow> ('e BaseExpressions) Statement" where
  "generate_rules None (base e) = Return (ConditionExpression (generate_result e))" |
  "generate_rules (Some v) (base e) = (v := (ConditionExpression (generate_result e)))" |
  "generate_rules v (cond' m r) = export_match m (generate_rules v r)" |
  "generate_rules v (r1 else r2) = generate_rules v r1; generate_rules v r2" |
  "generate_rules v (choice rules) = Sequential (map (generate_rules v) rules)" |
  "generate_rules v (r1 \<then> r2) = 
    generate_rules (entry_var r2) r1;
    generate_rules v r2"

definition "export_rules = generate_rules None"

end

end