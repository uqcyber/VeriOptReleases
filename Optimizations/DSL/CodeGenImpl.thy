theory CodeGenImpl
  imports 
    Semantics.IRTreeEval
    CodeGen.JavaExport
    "HOL-Library.Monad_Syntax"
begin

fun compatible :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> bool" where
  "compatible s1 s2 = (\<forall>x \<in> fset (fmdom s1) . fmlookup s2 x \<noteq> None \<longrightarrow> fmlookup s1 x = fmlookup s2 x)"

fun union :: "(('a, 'b) fmap) option \<Rightarrow> (('a, 'b) fmap) option \<Rightarrow> (('a, 'b) fmap) option" where
  "union s1 s2 = do {
    s1' <- s1;
    s2' <- s2;
    if compatible s1' s2' then Some (s1' ++\<^sub>f s2') else None
  }"

fun rewrite_IRExpr :: "(IRExpr \<Rightarrow> IRExpr) \<Rightarrow> IRExpr \<Rightarrow> IRExpr" where
  "rewrite_IRExpr f (UnaryExpr op x) = f (UnaryExpr op (rewrite_IRExpr f x))" |
  "rewrite_IRExpr f (BinaryExpr op x y) = f (BinaryExpr op (rewrite_IRExpr f x) (rewrite_IRExpr f y))" |
  "rewrite_IRExpr f (ConditionalExpr c b1 b2) = f (ConditionalExpr (rewrite_IRExpr f c) (rewrite_IRExpr f b1) (rewrite_IRExpr f b2))" |
  "rewrite_IRExpr f (ParameterExpr i s) = f (ParameterExpr i s)" |
  "rewrite_IRExpr f (LeafExpr i s) = f (LeafExpr i s)" |
  "rewrite_IRExpr f (ConstantExpr v) = f (ConstantExpr v)" |
  "rewrite_IRExpr f (ConstantVar v) = f (ConstantVar v)" |
  "rewrite_IRExpr f (VariableExpr v s) = f (VariableExpr v s)"

fun match_IRExpr :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> ((string, IRExpr) fmap) option" where
  "match_IRExpr (UnaryExpr op x) (UnaryExpr op' x') =
    (if op = op' then (match_IRExpr x x') else None)" |
  "match_IRExpr (BinaryExpr op x y) (BinaryExpr op' x' y') =
    (if op = op' then
      union (match_IRExpr x x') (match_IRExpr y y') else None)" |
  "match_IRExpr (ConditionalExpr c t f) (ConditionalExpr c' t' f') =
    (union (match_IRExpr c c') (union (match_IRExpr t t') (match_IRExpr f f')))" |
  "match_IRExpr (ParameterExpr i s) (ParameterExpr i' s') =
    (if i = i' \<and> s = s' then Some (fmempty) else None)" |
  "match_IRExpr (LeafExpr i s) (LeafExpr i' s') =
    (if i = i' \<and> s = s' then Some (fmempty) else None)" |
  "match_IRExpr (ConstantExpr v) (ConstantExpr v') =
    (if v = v' then Some (fmempty) else None)" |
  "match_IRExpr (ConstantVar v) (ConstantVar v') =
    (if v = v' then Some (fmempty) else None)" |
  "match_IRExpr (VariableExpr v s) e = Some (fmupd (String.explode v) e fmempty)" |
  "match_IRExpr _ _ = None"

fun varof_IRExpr :: "IRExpr \<Rightarrow> string option" where
  "varof_IRExpr (VariableExpr v s) = Some (String.explode v)" |
  "varof_IRExpr _ = None"

fun var_IRExpr :: "string \<Rightarrow> IRExpr" where
  "var_IRExpr v = VariableExpr (String.implode v) (VoidStamp)"

fun subexprs_IRExpr :: "IRExpr \<Rightarrow> IRExpr list" where
  "subexprs_IRExpr (UnaryExpr op x) = [x]" |
  "subexprs_IRExpr (BinaryExpr op x y) = [x, y]" |
  "subexprs_IRExpr (ConditionalExpr c t f) = [c, t, f]" |
  "subexprs_IRExpr _ = []"

fun chain_IRExpr :: "(IRExpr \<Rightarrow> nat \<Rightarrow> (nat \<times> IRExpr)) \<Rightarrow> IRExpr \<Rightarrow> nat \<Rightarrow> (nat \<times> IRExpr)" where
  "chain_IRExpr f (UnaryExpr op x) n =
    (let (n', x') = f x n in
      (n', UnaryExpr op x'))" |
  "chain_IRExpr f (BinaryExpr op x y) n =
    (let (n', x') = f x n in
    (let (n'', y') = f y n' in
      (n'', BinaryExpr op x' y')))" |
  "chain_IRExpr f (ConditionalExpr c b1 b2) n =
    (let (n', c') = f c n in
    (let (n'', b1') = f b1 n' in
    (let (n''', b2') = f b2 n'' in
      (n''', ConditionalExpr c' b1' b2'))))" |
  "chain_IRExpr f e n = (n, e)"


datatype SideCondition =
  IsConstantExpr IRExpr |
  IsIntegerStamp IRExpr |
  IsBoolStamp IRExpr |
  WellFormed IRExpr |
  IsStamp IRExpr Stamp |
  IsConstantValue IRExpr IRExpr "64 word" |
  AlwaysDistinct IRExpr IRExpr |
  NeverDistinct IRExpr IRExpr |
  StampUnder IRExpr IRExpr |
  UpMaskEquals IRExpr "64 word" |
  DownMaskEquals IRExpr "64 word" |
  UpMaskCancels IRExpr IRExpr |
  IsBool IRExpr |
  PowerOf2 IRExpr |
  Empty |
  And SideCondition SideCondition |
  Not SideCondition

(* No code generation for for all
definition wf_stamp :: "IRExpr \<Rightarrow> bool" where
  "wf_stamp e = (\<forall>m p v. ([m, p] \<turnstile> e \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr e))"
*)
definition wf_stamp :: "IRExpr \<Rightarrow> bool" where
  "wf_stamp e = False"
fun eval_condition :: "SideCondition \<Rightarrow> bool" where
  "eval_condition (IsConstantExpr e) = is_ConstantExpr e" |
  "eval_condition (IsIntegerStamp e) = is_IntegerStamp (stamp_expr e)" |
  "eval_condition (IsBoolStamp e) = (stamp_expr e = IntegerStamp 32 0 1)" |
  "eval_condition (WellFormed e) = wf_stamp e" |
  "eval_condition (IsStamp e s) = ((stamp_expr e) = s)" |
  "eval_condition (IsConstantValue e s v) = (e = ConstantExpr (IntVal (stp_bits (stamp_expr s)) v))" |
  "eval_condition (AlwaysDistinct e1 e2) = alwaysDistinct (stamp_expr e1) (stamp_expr e2)" |
  "eval_condition (NeverDistinct e1 e2) = neverDistinct (stamp_expr e1) (stamp_expr e2)" |
  "eval_condition (StampUnder e1 e2) = (stamp_under (stamp_expr e1) (stamp_expr e2))" |
  "eval_condition (UpMaskEquals e m) = (IRExpr_up e = m)" |
  "eval_condition (DownMaskEquals e m) = (IRExpr_down e = m)" |
  "eval_condition (UpMaskCancels e1 e2) = (((and (IRExpr_up e1) (IRExpr_up e2)) = 0))" |
  "eval_condition (PowerOf2 e) = False" |
  "eval_condition (IsBool e) = ((e = ConstantExpr (IntVal 32 0)) | (e = ConstantExpr (IntVal 32 0)))" |
  
  "eval_condition (Empty) = True" |

  "eval_condition (And sc1 sc2) = ((eval_condition sc1) \<and> (eval_condition sc2))" |
  "eval_condition (Not sc) = (\<not>(eval_condition sc))"

fun eval_condition_opt :: "SideCondition \<Rightarrow> bool option" where
  "eval_condition_opt c = Some (eval_condition c)"

fun ground_expr :: "IRExpr \<Rightarrow> (string \<rightharpoonup> IRExpr) \<Rightarrow> IRExpr" where
  "ground_expr (UnaryExpr op e) s = (UnaryExpr op (ground_expr e s))" |
  "ground_expr (BinaryExpr op e1 e2) s = 
    (BinaryExpr op (ground_expr e1 s) (ground_expr e1 s))" |
  "ground_expr (ConditionalExpr b e1 e2) s =
    (ConditionalExpr (ground_expr b s) (ground_expr e1 s) (ground_expr e2 s))" |
  "ground_expr (VariableExpr vn st) s = 
    (case s (String.explode vn) of None \<Rightarrow> (VariableExpr vn st)
                | Some v' \<Rightarrow> v')" |
  "ground_expr e s = e"


fun ground_condition :: "SideCondition \<Rightarrow> (string \<rightharpoonup> IRExpr) \<Rightarrow> SideCondition" where
  "ground_condition (IsConstantExpr p) s = (IsConstantExpr (ground_expr p s))" |
  "ground_condition (IsIntegerStamp p) s = (IsIntegerStamp (ground_expr p s))" |
  "ground_condition (IsBoolStamp p) s = (IsBoolStamp (ground_expr p s))" |
  "ground_condition (WellFormed st) s = (WellFormed st)" |
  "ground_condition (IsStamp e st) s = (IsStamp (ground_expr e s) st)" |
  "ground_condition (IsConstantValue e s' v) s = (IsConstantValue (ground_expr e s) (ground_expr s' s) v)" |
  "ground_condition (AlwaysDistinct e1 e2) s = (AlwaysDistinct (ground_expr e1 s) (ground_expr e2 s))" |
  "ground_condition (NeverDistinct e1 e2) s = (NeverDistinct (ground_expr e1 s) (ground_expr e2 s))" |  
  "ground_condition (StampUnder e1 e2) s = (StampUnder (ground_expr e1 s) (ground_expr e2 s))" |
  "ground_condition (UpMaskEquals e m) s = (UpMaskEquals (ground_expr e s) m)" |
  "ground_condition (DownMaskEquals e m) s = (DownMaskEquals (ground_expr e s) m)" |
  "ground_condition (UpMaskCancels e1 e2) s = (UpMaskCancels (ground_expr e1 s) (ground_expr e2 s))" |
  "ground_condition (PowerOf2 e) s = (PowerOf2 (ground_expr e s))" |
  "ground_condition (IsBool e) s = (IsBool (ground_expr e s))" |
  "ground_condition (And sc1 sc2) s = And (ground_condition sc1 s) (ground_condition sc2 s)" |
  "ground_condition (Not sc) s = Not (ground_condition sc s)" |
  "ground_condition (Empty) s = Empty"

fun is_ground_condition :: "SideCondition \<Rightarrow> bool" where
  "is_ground_condition (IsConstantExpr e) = is_VariableExpr e" |
  "is_ground_condition (IsIntegerStamp e) = is_VariableExpr e" |
  "is_ground_condition (IsBoolStamp e) = is_VariableExpr e" |
  "is_ground_condition (WellFormed s) = True" |
  "is_ground_condition (IsStamp e s) = is_VariableExpr e" |
  "is_ground_condition (IsConstantValue e s v) = is_VariableExpr e" |
  "is_ground_condition (AlwaysDistinct e1 e2) = (is_VariableExpr e1 \<and> is_VariableExpr e2)" |
  "is_ground_condition (NeverDistinct e1 e2) = (is_VariableExpr e1 \<and> is_VariableExpr e2)" |
  "is_ground_condition (StampUnder e1 e2) = (is_VariableExpr e1 \<and> is_VariableExpr e2)" |
  "is_ground_condition (UpMaskEquals e m) = is_VariableExpr e" |
  "is_ground_condition (DownMaskEquals e m) = is_VariableExpr e" |
  "is_ground_condition (UpMaskCancels e1 e2) = (is_VariableExpr e1 \<and> is_VariableExpr e2)" |
  "is_ground_condition (PowerOf2 e) = is_VariableExpr e" |
  "is_ground_condition (IsBool e) = is_VariableExpr e" |
  "is_ground_condition (And sc1 sc2) = (is_ground_condition sc1 \<and> is_ground_condition sc2)" |
  "is_ground_condition (Not sc) = is_ground_condition sc" |
  "is_ground_condition (Empty) = True"

datatype Result =
  ExpressionResult IRExpr |
  forZero IRExpr |
  Negate IRExpr |
  Add IRExpr IRExpr

fun result_of :: "Result \<Rightarrow> IRExpr option" where
  "result_of (ExpressionResult e) = Some e" |
  "result_of (forZero e) = Some (ConstantExpr (IntVal (stp_bits (stamp_expr e)) 0))" |
  "result_of (Negate (ConstantExpr (IntVal b v))) = Some (ConstantExpr (intval_negate (IntVal b v)))" |
  "result_of (Add (ConstantExpr (IntVal b1 v1)) (ConstantExpr (IntVal b2 v2))) = Some (ConstantExpr (intval_add (IntVal b1 v1) (IntVal b2 v2)))" |
  "result_of _ = None"

fun ground_result :: "Result \<Rightarrow> (string \<rightharpoonup> IRExpr) \<Rightarrow> Result" where
  "ground_result (ExpressionResult e) s = ExpressionResult (ground_expr e s)" |
  "ground_result (forZero e) s = forZero (ground_expr e s)" |
  "ground_result (Negate e) s = Negate (ground_expr e s)" |
  "ground_result (Add e1 e2) s = Add (ground_expr e1 s) (ground_expr e2 s)"

fun is_ground_result :: "Result \<Rightarrow> bool" where
  "is_ground_result (ExpressionResult e) = is_VariableExpr e" |
  "is_ground_result (forZero e) = is_VariableExpr e" |
  "is_ground_result (Negate e) = is_VariableExpr e" |
  "is_ground_result (Add e1 e2) = (is_VariableExpr e1 \<and> is_VariableExpr e2)"


subsection \<open>Java Generation\<close>

fun unary_op_class :: "IRUnaryOp \<Rightarrow> ClassName" where
  "unary_op_class UnaryAbs = ''AbsNode''" |
  "unary_op_class UnaryNeg = ''NegateNode''" |
  "unary_op_class UnaryNot = ''NotNode''" |
  "unary_op_class UnaryLogicNegation = ''LogicNegationNode''" |
  "unary_op_class (UnaryNarrow _ _) = ''NarrowNode''" |
  "unary_op_class (UnarySignExtend _ _) = ''SignExtendNode''" |
  "unary_op_class (UnaryZeroExtend _ _) = ''ZeroExtendNode''" |
  "unary_op_class UnaryIsNull = ''IsNullNode''" |
  "unary_op_class UnaryReverseBytes = ''ReverseBytesNode''" |
  "unary_op_class UnaryBitCount = ''BitCountNode''"

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
  "binary_op_class BinIntegerBelow = ''IntegerBelowNode''" |
  "binary_op_class BinIntegerTest = ''IntegerTestNode''" |
  "binary_op_class BinIntegerNormalizeCompare = ''IntegerNormalizeCompareNode''" |
  "binary_op_class BinIntegerMulHigh = ''IntegerMulHighNode''"

fun class_of_irexpr :: "IRExpr \<Rightarrow> ClassName" where
  "class_of_irexpr (UnaryExpr op v) = unary_op_class op" |
  "class_of_irexpr (BinaryExpr op v1 v2) = binary_op_class op" |
  "class_of_irexpr (ConditionalExpr v1 v2 v3) = ''ConditionalNode''" |
  "class_of_irexpr (ConstantExpr v) = ''ConstantNode''" |
  "class_of_irexpr (ConstantVar v) = ''ConstantNode''" |
  "class_of_irexpr (VariableExpr v s) = ''ERROR: Variable should not occur on LHS''"

datatype Expression =
  Ref VariableName |
  IntegerConstant int |
  TrueValue |
  FalseValue |
  MethodCall Expression MethodName "Expression list"
    ("_._(_)") |
  Constructor ClassName "Expression list"
    ("new _(_)") |
  InstanceOf Expression ClassName VariableName
    ("_ instanceof _ _")|
  Equal Expression Expression
    (infix "==" 58) |
  Less Expression Expression |
  Negate Expression |
  Add Expression Expression |
  And Expression Expression |
  BitAnd Expression Expression |
  Unsupported string

fun generate_expression :: "Expression \<Rightarrow> string" where
  "generate_expression (Ref v) = v" |
  "generate_expression (IntegerConstant n) = ''0''" | (*TODO FIX*)
  "generate_expression TrueValue = ''true''" |
  "generate_expression FalseValue = ''false''" |
  "generate_expression (MethodCall e mn ps) = 
    (generate_expression e) @ ''.'' @ mn @ ''('' @ param_list (map generate_expression ps) @ '')''" |
  "generate_expression (Constructor cn ps) =
    ''new '' @ cn @ ''('' @ param_list (map generate_expression ps) @ '')''" |
  "generate_expression (InstanceOf e cn var) =
    (generate_expression e) @ '' instanceof '' @ cn @ '' '' @ var" |
  "generate_expression (Equal e1 e2) =
    (generate_expression e1) @ '' == '' @ (generate_expression e2)" |
  "generate_expression (Less e1 e2) =
    (generate_expression e1) @ '' < '' @ (generate_expression e2)" |
  "generate_expression (Negate e) =
    ''!('' @ (generate_expression e) @ '')''" |
  "generate_expression (Add e1 e2) =
    ''('' @ (generate_expression e1) @ '' + '' @ (generate_expression e2) @ '')''" |
  "generate_expression (And e1 e2) =
    (generate_expression e1) @ '' && '' @ (generate_expression e2)" |
  "generate_expression (BitAnd e1 e2) =
    (generate_expression e1) @ '' & '' @ (generate_expression e2)" |
  "generate_expression (Unsupported x) = x"

fun export_value :: "Value \<Rightarrow> Expression" where
  "export_value (IntVal s v) = IntegerConstant (sint v)" |
  "export_value _ = Unsupported ''unsupported Value''"

fun construct_node :: "IRExpr \<Rightarrow> Expression" where
  "construct_node (UnaryExpr op e1) =
    Constructor (unary_op_class op) [construct_node e1]" |
  "construct_node (BinaryExpr op e1 e2) =
    Constructor (binary_op_class op) [construct_node e1, construct_node e2]" |
  "construct_node (ConditionalExpr e1 e2 e3) =
    Constructor ''ConditionalNode''  [construct_node e1, construct_node e2, construct_node e3]" |
  "construct_node (ConstantExpr val) =
    Constructor ''ConstantNode'' [export_value val]" |
  "construct_node (ConstantVar v) =
    Constructor ''ConstantNode'' [Ref (String.explode v)]" |
  "construct_node (VariableExpr v s) = Ref (String.explode v)"

fun export_result :: "Result \<Rightarrow> Expression" where
  "export_result (ExpressionResult e) = construct_node e" |
  "export_result (forZero e) = Constructor ''ConstantNode'' [IntegerConstant 0]" |
  "export_result (Result.Negate e) = Negate (construct_node e)" |
  "export_result (Result.Add e1 e2) = Add (construct_node e1) (construct_node e2)"

fun export_stamp :: "Stamp \<Rightarrow> Expression" where
  "export_stamp (IntegerStamp bits lower higher) =
    Constructor ''IntegerStamp'' 
      [IntegerConstant bits, IntegerConstant lower,
       IntegerConstant higher]" |
  "export_stamp _ =
    Unsupported ''unsupported Stamp''"

definition stampOf :: "Expression \<Rightarrow> Expression" where
  "stampOf e = (MethodCall e ''stamp'' [Ref ''view''])"

definition upMask :: "Expression \<Rightarrow> Expression" where
  "upMask e = (MethodCall (stampOf e) ''upMask'' [])"

definition downMask :: "Expression \<Rightarrow> Expression" where
  "downMask e = (MethodCall (stampOf e) ''downMask'' [])"

fun export_condition :: "SideCondition \<Rightarrow> Expression" where
  "export_condition (IsConstantExpr e) = (InstanceOf (construct_node e) ''ConstantNode'' ''t'')" |
  "export_condition (IsIntegerStamp e) = (InstanceOf (stampOf (construct_node e)) ''IntegerStamp'' ''t'')" |
  "export_condition (WellFormed s) = TrueValue" |
  "export_condition (IsStamp e s) =
    (Equal (stampOf (construct_node e)) (export_stamp s))" |
  "export_condition (IsConstantValue e s v) =
    (And
      (InstanceOf (construct_node e) ''ConstantNode'' ''t'')
      (Equal (MethodCall (construct_node e) ''getConstantValue'' []) (IntegerConstant (sint v))))" |
  "export_condition (StampUnder e1 e2) =
    (Less 
      (MethodCall (stampOf (construct_node e1)) ''upperBound'' []) 
      (MethodCall (stampOf (construct_node e2)) ''lowerBound'' []))" |
  "export_condition (UpMaskEquals e m) =
    Equal (upMask (construct_node e)) (IntegerConstant (sint m))" |
  "export_condition (DownMaskEquals e m) =
    Equal (downMask (construct_node e)) (IntegerConstant (sint m))" |
  "export_condition (UpMaskCancels e1 e2) =
    Equal (BitAnd (upMask (construct_node e1)) (upMask (construct_node e2))) (IntegerConstant 0)" |
  "export_condition (PowerOf2 e) =
    MethodCall (Ref ''CodeUtil'') ''isPowerOf2'' [construct_node e]" |
  "export_condition (IsBool e) =
    Equal (MethodCall (construct_node e) ''upMask'' []) (IntegerConstant 1)" |
  "export_condition (Not sc) = Negate (export_condition sc)" |
  "export_condition (SideCondition.And sc1 sc2) = And (export_condition sc1) (export_condition sc2)" |
  "export_condition (Empty) = TrueValue"


instantiation Expression :: JavaExpression
begin
definition "expToJava_Expression = generate_expression" 
instance ..
end

fun export_assignments :: "VarName \<Rightarrow> IRExpr \<Rightarrow> Expression list" where
  "export_assignments v (UnaryExpr op (VariableExpr v1 st)) =
    [(MethodCall (Ref (v @ ''c'')) ''getValue'' [])]" |
  "export_assignments v (BinaryExpr op (VariableExpr v1 st) (VariableExpr v2 st')) =
    [(MethodCall (Ref (v @ ''c'')) ''getX'' []),
     (MethodCall (Ref (v @ ''c'')) ''getY'' [])]" |
  "export_assignments v (ConditionalExpr (VariableExpr v1 st) (VariableExpr v2 st') (VariableExpr v3 st'')) =
    [(MethodCall (Ref (v @ ''c'')) ''condition'' []),
     (MethodCall (Ref (v @ ''c'')) ''trueValue'' []),
     (MethodCall (Ref (v @ ''c'')) ''falseValue'' [])]" |
  "export_assignments v (ConstantExpr val) = []" | (* TODO: conditionals *)
  "export_assignments v (ConstantVar v') = []" | (* TODO: conditionals *)
  "export_assignments v (VariableExpr v' st) = []" 


context Rewritable begin
termination match_pattern sorry
end

setup \<open>Locale_Code.open_block\<close>
interpretation IRExprRewrites : Rewritable
  size_IRExpr
  "eval_condition_opt"
  "ground_condition"
  is_ground_condition
  result_of
  ground_result
  is_ground_result
  subexprs_IRExpr
  chain_IRExpr
  rewrite_IRExpr
  match_IRExpr
  varof_IRExpr
  var_IRExpr
proof
  fix a' a :: "(string \<rightharpoonup> IRExpr)"
  fix e e' :: SideCondition
  assume sub: "a' \<subseteq>\<^sub>m a"
  assume e': "is_ground_condition (ground_condition e a')"
  show "ground_condition e a' = ground_condition e a"
    using sub e'
    apply (induction e a' arbitrary: a a' rule: ground_condition.induct; auto)
    sorry
next
  fix e :: IRExpr
  show "\<forall>e' \<in> set (subexprs_IRExpr e). size_IRExpr e > size_IRExpr e'"
    by (cases e; simp)
next
  fix f :: "IRExpr \<Rightarrow> IRExpr"
  fix e :: IRExpr
  show "map f (subexprs_IRExpr e) = subexprs_IRExpr (snd (chain_IRExpr (\<lambda>e a. (plus a 1, f e)) e 0))"
    by (cases e; simp)
next
  fix f :: "IRExpr \<Rightarrow> IRExpr"
  fix e :: IRExpr
  show "length (subexprs_IRExpr e) = fst (chain_IRExpr (\<lambda>e a. (plus a 1, f e)) e 0)"
    by (cases e; simp)
next
  fix c :: SideCondition
  show "eval_condition_opt c = None \<equiv> \<not> is_ground_condition c"
    sorry
qed
setup \<open>Locale_Code.close_block\<close>

setup \<open>Locale_Code.open_block\<close>
interpretation IRExprRewrites: JavaTarget
  size_IRExpr
  "eval_condition_opt"
  "ground_condition"
  is_ground_condition
  result_of
  ground_result
  is_ground_result
  subexprs_IRExpr
  chain_IRExpr
  rewrite_IRExpr
  match_IRExpr
  varof_IRExpr
  var_IRExpr
  class_of_irexpr
  export_condition
  export_result
  export_assignments
  by standard
setup \<open>Locale_Code.close_block\<close>

definition var where "var = var_IRExpr"
definition join where "join = IRExprRewrites.join"
definition generate where "generate = IRExprRewrites.generate"
definition generate_with_condition where "generate_with_condition = IRExprRewrites.generate_with_condition"

definition match_pattern where "match_pattern = IRExprRewrites.match_pattern"
definition optimized_export where "optimized_export = IRExprRewrites.optimized_export"

export_code "generate_with_condition" checking SML

instantiation IRExpr :: full_exhaustive
begin
instance ..
end

instantiation SideCondition :: full_exhaustive
begin
instance ..
end

instantiation Result :: full_exhaustive
begin
instance ..
end

lemma exhaust_SideCondition[code]:
"full_exhaustive_SideCondition_inst.full_exhaustive_SideCondition f d = None"
  sorry
lemma exhaust_Result[code]:
"full_exhaustive_Result_inst.full_exhaustive_Result f d = None"
  sorry
lemma exhaust_IRExpr[code]:
"full_exhaustive_IRExpr_inst.full_exhaustive_IRExpr f d = None"
  sorry


text \<open>@{text "x * const 1 \<longrightarrow> x"}\<close>
definition Identity where
  "Identity = generate 
    (BinaryExpr BinMul
      (var ''x'')
      (ConstantExpr (IntVal 32 1)))
    (ExpressionResult (var ''x''))"

value "Identity"
value "(optimized_export (Identity))"

text \<open>@{text "const x * const y \<longrightarrow> const (x * y)"}\<close>
definition Evaluate where
  "Evaluate = generate 
    (BinaryExpr BinMul
      (ConstantVar STR ''x'')
      (ConstantVar STR ''y''))
    (Result.Add (ConstantVar STR ''x'') (ConstantVar STR ''y''))"
(* doesn't support constant evaluation *)
value "Evaluate"
value "(optimized_export (Evaluate))"

text \<open>@{text "x * const y \<longrightarrow> x << const (log2 y)"}\<close>
definition Shift where
  "Shift = generate_with_condition 
    (BinaryExpr BinMul
      (var ''x'')
      (ConstantVar STR ''y''))
    (ExpressionResult (BinaryExpr BinLeftShift (var ''x'') (ConstantVar STR ''y'')))
    (PowerOf2 (ConstantVar STR ''y''))"

value "Shift"
value "(optimized_export (Shift))"

text \<open>@{text "const x * y \<longrightarrow> y * const x when NotConst y"}\<close>
definition LeftConst where
  "LeftConst = generate_with_condition 
    (BinaryExpr BinMul
      (ConstantVar STR ''x'')
      (var ''y''))
    (ExpressionResult (BinaryExpr BinMul (var ''y'') (ConstantVar STR ''x'')))
    (Not (IsConstantExpr (var ''y'')))"

value "LeftConst"

value "optimized_export (optimized_export (LeftConst else (Evaluate else (Identity else Shift))))"

value " (optimized_export (choice [LeftConst, Shift, Evaluate]))"

definition "export_rules = IRExprRewrites.export_rules"
definition generate_statement where "generate_statement = statementToJava"


value "export_rules"

value "export_rules (choice [LeftConst, Shift, Evaluate])"
value "export_rules (optimized_export (choice [LeftConst, Shift, Evaluate]))"


value "generate_statement 0 (export_rules (choice [LeftConst, Shift, Evaluate]))"


end