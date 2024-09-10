theory JavaAST
  imports Main Semantics.IRTreeEval
begin

declare [[show_types=false]]

subsection \<open>Java AST\<close>

type_synonym ClassName = String.literal
type_synonym VariableName = String.literal
type_synonym MethodName = String.literal

datatype Expression =
  JavaUnary IRUnaryOp Expression |
  JavaBinary IRBinaryOp Expression Expression |
  JavaVariable VariableName |
  JavaConstant int |
  JavaTrue |
  JavaFalse |
  JavaMethodCall Expression MethodName "Expression list" |
  JavaConstructor ClassName "Expression list" |
  JavaInstanceOf Expression ClassName VariableName |
  JavaCast ClassName Expression |
  
  Unsupported string

datatype Statement =
  JavaAssignment VariableName Expression |
  JavaBranch Expression Statement |
  JavaReturn Expression |
  JavaSequential "Statement list"

bundle java_ast_syntax
begin

notation
  JavaConstant  (\<open>const _\<close>)
    and JavaVariable  (\<open>ref _\<close>)
    and JavaTrue (\<open>true\<close>)
    and JavaFalse (\<open>false\<close>)
    and JavaConstructor ("new _'(_')")
    and JavaInstanceOf ("_ instanceof _ _")

notation
  JavaAssignment (infixr ":=" 56)
    and JavaBranch  ("if '(_') {(2//_)//}")
    and JavaReturn ("return _")

(*syntax
  "_method" :: "Expression \<Rightarrow> ClassName \<Rightarrow> args => Expression" ("_.._'(_')" 45)
  "_method_empty" :: "Expression \<Rightarrow> ClassName => Expression" ("_.._'(')" 45)
  "_method_syntax" :: "Expression \<Rightarrow> ClassName \<Rightarrow> args => Expression"

translations
  "i..m(x, xs)" \<rightharpoonup> "_method_syntax i m (x#[xs])"
  "i..m(x)" \<rightharpoonup> "_method_syntax i m (x#[])"
  "i..m()" \<rightharpoonup> "_method_syntax i m ([])"*)

end

syntax
  "_seq" :: "Statement \<Rightarrow> Statement => Statement" (infixr ";//" 55)

translations
  "_seq x y" == "CONST JavaSequential [x, y]"


context includes java_ast_syntax begin
value "v1 := (ref v2); v2 := (ref v3); v3 := (ref v4)"
end

fun intersperse :: "string \<Rightarrow> string list \<Rightarrow> string list" where
  "intersperse i es = foldr (\<lambda>x ys . x # (if ys = [] then ys else i # ys)) es []"

fun param_list :: "string list \<Rightarrow> string" where
  "param_list es = (foldr (@) (intersperse '', '' es) '''')"

(* https://stackoverflow.com/questions/23864965/string-of-nat-in-isabelle *)
fun string_of_nat :: "nat \<Rightarrow> string" where
  "string_of_nat n = (if n < 10 then [char_of (48 + n)] else 
     string_of_nat (n div 10) @ [char_of (48 + (n mod 10))])"

definition string_of_int :: "int \<Rightarrow> string" where
  "string_of_int i = (if i < 0 then ''-'' @ string_of_nat (nat (- i)) else 
     string_of_nat (nat i))"

fun unary_op_expr :: "IRUnaryOp \<Rightarrow> string \<Rightarrow> string" where
  "unary_op_expr UnaryAbs e = ''Math.abs('' @ e @ '')''" |
  "unary_op_expr UnaryNeg e = ''-('' @ e @ '')''" |
  "unary_op_expr UnaryNot e = ''~('' @ e @ '')''" |
  "unary_op_expr UnaryLogicNegation e = ''!('' @ e @ '')''"

fun binary_op_expr :: "IRBinaryOp \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string" where
  "binary_op_expr BinAdd x y = ''('' @ x @ '' + '' @ y @ '')''" |
  "binary_op_expr BinMul x y = ''('' @ x @ '' * '' @ y @ '')''" |
  "binary_op_expr BinSub x y = ''('' @ x @ '' - '' @ y @ '')''" |
  "binary_op_expr BinAnd x y = ''('' @ x @ '' & '' @ y @ '')''" |
  "binary_op_expr BinOr x y = ''('' @ x @ '' | '' @ y @ '')''" |
  "binary_op_expr BinXor x y = ''('' @ x @ '' ^ '' @ y @ '')''" |
  "binary_op_expr BinShortCircuitOr x y = ''('' @ x @ '' || '' @ y @ '')''" |
  "binary_op_expr BinLeftShift x y = ''('' @ x @ '' << '' @ y @ '')''" |
  "binary_op_expr BinRightShift x y = ''('' @ x @ '' >> '' @ y @ '')''" |
  "binary_op_expr BinURightShift x y = ''('' @ x @ '' >>> '' @ y @ '')''" |
  "binary_op_expr BinIntegerEquals x y = ''('' @ x @ '' == '' @ y @ '')''" |
  "binary_op_expr BinIntegerLessThan x y = ''('' @ x @ '' < '' @ y @ '')''"
  

fun generate_expression :: "Expression \<Rightarrow> string" where
  "generate_expression (JavaUnary op e) = unary_op_expr op (generate_expression e)" |
  "generate_expression (JavaBinary op x y) = binary_op_expr op (generate_expression x) (generate_expression y)" |
  "generate_expression (JavaVariable v) = String.explode v" |
  "generate_expression (JavaConstant n) = string_of_int n" |
  "generate_expression (JavaTrue) = ''true''" |
  "generate_expression (JavaFalse) = ''false''" |
  "generate_expression (JavaMethodCall e mn ps) =
    (generate_expression e) @ ''.'' @ String.explode mn @ ''('' @ param_list (map generate_expression ps) @ '')''" |
  "generate_expression (JavaConstructor cn ps) =
    ''new '' @ String.explode cn @ ''('' @ param_list (map generate_expression ps) @ '')''" |
  "generate_expression (JavaInstanceOf e cn var) =
    (generate_expression e) @ '' instanceof '' @ String.explode cn @ '' '' @ (String.explode var)" |
  "generate_expression (JavaCast c e) =
    ''(('' @ String.explode c @ '') '' @ (generate_expression e) @ '')''" |
  "generate_expression (Unsupported x) = x"

fun indent :: "nat \<Rightarrow> string" where
  "indent 0 = ''''" |
  "indent (Suc n) = '' '' @ indent n"

fun generate_statement :: "nat \<Rightarrow> Statement \<Rightarrow> string" where
  "generate_statement i (JavaAssignment v e) = indent i @
    ''var '' @ String.explode v @ '' = '' @ generate_expression e @ '';\<newline>''" |
  "generate_statement i (JavaBranch c s) = indent i @
    ''if ('' @ generate_expression c @ '') {\<newline>'' @ generate_statement (i + 4) s @ 
    indent i @ ''}\<newline>''" |
  "generate_statement i (JavaReturn e) = indent i @
    ''return '' @ generate_expression e @ '';\<newline>''" |
  "generate_statement i (JavaSequential ss) = 
    foldr (@) (map (generate_statement i) ss) ''''"


context includes java_ast_syntax begin
value "generate_statement 0 (
  if (JavaBinary BinIntegerEquals (ref STR ''x'') (const 12)) {
    if (((ref STR ''e'') instanceof STR ''IntegerLessThanNode'' STR ''ex'')) {
      STR ''res'' := (const 12);
      return (ref STR ''res'')
    }
  }
)"
end

end