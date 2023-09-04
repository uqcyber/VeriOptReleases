theory RewriteTerms
imports IRTreeEval Stratego.CompileRewrite "HOL-Library.Monad_Syntax"
begin

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

(*
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


fun ground_expr :: "IRExpr \<Rightarrow> (string \<rightharpoonup> IRExpr) \<Rightarrow> IRExpr option" where
  "ground_expr (UnaryExpr op e) s = do {
    e <- ground_expr e s;
    Some (UnaryExpr op e)
  }" |
  "ground_expr (BinaryExpr op e1 e2) s = do {
    e1 <- ground_expr e1 s;
    e2 <- ground_expr e2 s;
    Some (BinaryExpr op e1 e2)
  }" |
  "ground_expr (ConditionalExpr b e1 e2) s = do {
    b <- ground_expr b s;
    e1 <- ground_expr e1 s;
    e2 <- ground_expr e2 s;
    Some (ConditionalExpr b e1 e2)
  }" |
  "ground_expr (VariableExpr vn st) s = 
    (case s (String.explode vn) of None \<Rightarrow> None
                | Some v' \<Rightarrow> Some v')" |
  "ground_expr e s = Some e"

lemma
  assumes sub: "a' \<subseteq>\<^sub>m a"
  assumes e': "ground_expr e a' = Some e'"
  shows "ground_expr e a' = ground_expr e a"
  using assms apply (induction e a' arbitrary: a a' rule: ground_expr.induct; auto)
  sorry
  

fun ground_condition :: "SideCondition \<Rightarrow> (string \<rightharpoonup> IRExpr) \<Rightarrow> SideCondition option" where
  "ground_condition (IsConstantExpr e) f = do {e <- ground_expr e f; Some (IsConstantExpr e)}" |
  "ground_condition (IsIntegerStamp e) f = do {e <- ground_expr e f; Some (IsIntegerStamp e)}" |
  "ground_condition (IsBoolStamp e) f = do {e <- ground_expr e f; Some (IsBoolStamp e)}" |
  "ground_condition (WellFormed e) f = do {e <- ground_expr e f; Some (WellFormed e)}" |
  "ground_condition (IsStamp e s) f = do {e <- ground_expr e f; Some (IsStamp e s)}" |
  "ground_condition (IsConstantValue e s v) f = do {e <- ground_expr e f; Some (IsConstantValue e s v)}" |
  "ground_condition (AlwaysDistinct e1 e2) f = do {
    e1 <- ground_expr e1 f;
    e2 <- ground_expr e2 f;
    Some (AlwaysDistinct e1 e2)
  }" |
  "ground_condition (NeverDistinct e1 e2) f = do {
    e1 <- ground_expr e1 f;
    e2 <- ground_expr e2 f;
    Some (NeverDistinct e1 e2)
  }" |
  "ground_condition (StampUnder e1 e2) f = do {
    e1 <- ground_expr e1 f;
    e2 <- ground_expr e2 f;
    Some (StampUnder e1 e2)
  }" |
  "ground_condition (UpMaskEquals e m) f = 
    do {e <- ground_expr e f; Some (UpMaskEquals e m)}" |
  "ground_condition (DownMaskEquals e m) f = 
    do {e <- ground_expr e f; Some (DownMaskEquals e m)}" |
  "ground_condition (UpMaskCancels e1 e2) f = do {
    e1 <- ground_expr e1 f;
    e2 <- ground_expr e2 f;
    Some (UpMaskCancels e1 e2)
  }" |
  "ground_condition (PowerOf2 e) f = do {e <- ground_expr e f; Some (PowerOf2 e)}" |
  "ground_condition (IsBool e) f = do {e <- ground_expr e f; Some (IsBool e)}" |
  
  "ground_condition (Empty) f = Some (Empty)" |

  "ground_condition (And sc1 sc2) f = do {
    sc1 <- ground_condition sc1 f;
    sc2 <- ground_condition sc2 f;
    Some (And sc1 sc2)
  }" |
  "ground_condition (Not sc) f = do {
    sc <- ground_condition sc f;
    Some (Not sc)
  }"

datatype Result =
  ExpressionResult IRExpr |
  forZero IRExpr |
  Negate IRExpr |
  Add IRExpr IRExpr

fun result_of :: "Result \<Rightarrow> IRExpr" where
  "result_of (ExpressionResult e) = e" |
  "result_of (forZero e) = ConstantExpr (IntVal (stp_bits (stamp_expr e)) 0)" |
  "result_of (Negate (ConstantExpr (IntVal b v))) = ConstantExpr (intval_negate (IntVal b v))" |
  "result_of (Add (ConstantExpr (IntVal b1 v1)) (ConstantExpr (IntVal b2 v2))) = ConstantExpr (intval_add (IntVal b1 v1) (IntVal b2 v2))" 

fun ground_result :: "Result \<Rightarrow> (string \<rightharpoonup> IRExpr) \<Rightarrow> Result option" where
  "ground_result (ExpressionResult e) s = do {e <- ground_expr e s; Some (ExpressionResult e)}" |
  "ground_result (forZero e) s = do {e <- ground_expr e s; Some (forZero e)}" |
  "ground_result (Negate e) s = do {e <- ground_expr e s; Some (Negate e)}" |
  "ground_result (Add e1 e2) s = do {
    e1 <- ground_expr e1 s;
    e2 <- ground_expr e2 s;
    Some (Add e1 e2)
  }"

setup \<open>Locale_Code.open_block\<close>
interpretation IRExprRewrites : Rewritable
  size_IRExpr
  "eval_condition"
  "ground_condition"
  result_of
  ground_result
  rewrite_IRExpr
  match_IRExpr
  varof_IRExpr
  var_IRExpr
proof
  fix a' a :: "(string \<rightharpoonup> IRExpr)"
  fix e e' :: SideCondition
  assume sub: "a' \<subseteq>\<^sub>m a"
  assume e': "ground_condition e a' = Some e'"
  show "ground_condition e a' = ground_condition e a"
    using sub e' apply (induction e a' arbitrary: a a' rule: ground_condition.induct; auto)
    sorry
qed
setup \<open>Locale_Code.close_block\<close>

setup \<open>Locale_Code.open_block\<close>
interpretation IRExprRewrites: CompiledRewrites
  size_IRExpr
  "eval_condition"
  "ground_condition"
  result_of
  ground_result
  rewrite_IRExpr
  match_IRExpr
  varof_IRExpr
  var_IRExpr
  subexprs_IRExpr
  chain_IRExpr
proof
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
qed
setup \<open>Locale_Code.close_block\<close>

definition eval where "eval = IRExprRewrites.eval"
definition var where "var = var_IRExpr"

no_notation Arithmetic.func ("func _")
no_notation Arithmetic.else ("_ else _")
notation IRExprRewrites.conditional_rewrite_to ("_ \<rightarrow> _ where _")
notation IRExprRewrites.not ("not _")
notation IRExprRewrites.condition ("condition _")
notation IRExprRewrites.func ("func _")

type_synonym StrategyRule = "(IRExpr, SideCondition, Result) IRExprRewrites.Strategy"

code_datatype fmap_of_list
lemma fmlookup_of_list[code]: "fmlookup (fmap_of_list m) = map_of m"
  by (simp add: fmlookup_of_list)

export_code "eval" checking SML

definition join where "join = IRExprRewrites.join"
definition compile' where "compile' = IRExprRewrites.compile'"
definition generate where "generate = IRExprRewrites.generate"
definition generate_with_condition where "generate_with_condition = IRExprRewrites.generate_with_condition"

definition match_pattern where "match_pattern = IRExprRewrites.match_pattern"
definition optimized_export where "optimized_export = IRExprRewrites.optimized_export"
notation IRExprRewrites.choice ("choice _")
notation IRExprRewrites.else ("_ else _")

export_code "compile'" checking SML

definition RedundantAdd :: "StrategyRule" where
  "RedundantAdd = 
    ((BinaryExpr BinAdd (var ''b'') (ConstantExpr (IntVal 32 0))) 
      \<rightarrow> (var ''b''))"

definition RedundantSub :: "StrategyRule" where
  "RedundantSub = 
    ((BinaryExpr BinSub (var ''a'') (ConstantExpr (IntVal 32 0)))
      \<rightarrow> (var ''a''))"

definition ShiftConstRight :: "StrategyRule" where
  "ShiftConstRight = 
    ((BinaryExpr BinAdd (var ''a'') (var ''b'')) \<rightarrow> (BinaryExpr BinAdd (var ''b'') (var ''a''))
      where ((var ''a'')!; not (ConstantExpr (IntVal 32 0)?)))"

definition EvalMinus :: "StrategyRule" where
  "EvalMinus = 
    ((UnaryExpr UnaryNeg (var ''a'')) \<rightarrow> ((var ''b''))
      where (condition (IsConstantExpr (var ''a'')); (func (Negate (var ''a''))); (var ''b'')?))"

definition EvalMinus1 :: "StrategyRule" where
  "EvalMinus1 =
    (UnaryExpr UnaryNeg (var ''a'')) \<rightarrow> var ''b''
      where (condition (IsConstantExpr (var ''a'')); (var ''b'') := (func Negate (var ''a'')))"

definition EvalAdd :: "StrategyRule" where
  "EvalAdd =
    (BinaryExpr BinAdd (var ''a'') (var ''b'')) \<rightarrow> ((var ''c''))
      where (
        condition (IsConstantExpr (var ''a''));
        condition (IsConstantExpr (var ''b''));
        (var ''c'') := func (Add (var ''a'') (var ''b''))
      )"

value "eval (RedundantAdd <+ RedundantSub)
        ((BinaryExpr BinAdd (ConstantExpr (IntVal 32 10)) (ConstantExpr (IntVal 32 10))), fmempty)"

\<comment> \<open>Successful application\<close>
value "eval (RedundantAdd <+ RedundantSub)
        ((BinaryExpr BinAdd (ConstantExpr (IntVal 32 10)) (ConstantExpr (IntVal 32 0))), fmempty)"

\<comment> \<open>Successful application in the second rule\<close>
value "eval (RedundantSub <+ RedundantAdd)
        ((BinaryExpr BinAdd (ConstantExpr (IntVal 32 10)) (ConstantExpr (IntVal 32 0))), fmempty)"

(*value "ShiftConstRight"*)
value "eval ShiftConstRight 
      ((BinaryExpr BinAdd (ConstantExpr (IntVal 32 10)) (ConstantExpr (IntVal 32 0))), fmempty)"
value "eval ShiftConstRight
      ((BinaryExpr BinAdd (ConstantExpr (IntVal 32 10))
                          (BinaryExpr BinAdd (ConstantExpr (IntVal 32 10)) (ConstantExpr (IntVal 32 20)))), fmempty)"

value "eval EvalMinus ((UnaryExpr UnaryNeg (ConstantExpr (IntVal 32 10))), fmempty)"
value "eval EvalMinus ((UnaryExpr UnaryNeg (BinaryExpr BinAdd (ConstantExpr (IntVal 32 10)) (ConstantExpr (IntVal 32 10)))), fmempty)"

value "eval EvalAdd ((UnaryExpr UnaryNeg (ConstantExpr (IntVal 32 10))), fmempty)"
value "eval EvalAdd ((BinaryExpr BinAdd (ConstantExpr (IntVal 32 10)) (ConstantExpr (IntVal 32 10))), fmempty)"


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

value "RedundantAdd"
value "(choice [the (compile' RedundantAdd), the (compile' RedundantSub)])"
value "(optimized_export (choice [the (compile' RedundantAdd), the (compile' RedundantSub)]))"




text \<open>@{text "x * const 1 \<longrightarrow> x"}\<close>
definition Identity where
  "Identity = generate 
    (BinaryExpr BinMul
      (var ''x'')
      (ConstantExpr (IntVal 32 1)))
    (var ''x'')"

value "Identity"
value "(optimized_export (Identity))"

text \<open>@{text "const x * const y \<longrightarrow> const (x * y)"}\<close>
definition Evaluate where
  "Evaluate = generate 
    (BinaryExpr BinMul
      (ConstantVar STR ''x'')
      (ConstantVar STR ''y''))
    ((ConstantVar STR ''x''))"
(* doesn't support constant evaluation *)
value "Evaluate"
value "(optimized_export (Evaluate))"

text \<open>@{text "x * const y \<longrightarrow> x << const (log2 y)"}\<close>
definition Shift where
  "Shift = generate_with_condition 
    (BinaryExpr BinMul
      (var ''x'')
      (ConstantVar STR ''y''))
    ((BinaryExpr BinLeftShift (var ''x'') (ConstantVar STR ''y'')))
    (PowerOf2 (ConstantVar STR ''y''))"
(* doesn't support constant evaluation *)
value "Shift"


text \<open>@{text "const x * y \<longrightarrow> y * const x when NotConst y"}\<close>
definition LeftConst where
  "LeftConst = generate_with_condition 
    (BinaryExpr BinMul
      (ConstantVar STR ''x'')
      (var ''y''))
    ((BinaryExpr BinMul (var ''y'') (ConstantVar STR ''x'')))
    (Not (IsConstantExpr (var ''y'')))"
(* doesn't support constant evaluation *)
value "LeftConst"

(*no_notation "\<^syntax_const>\<open>_thenM\<close>" (infixl "\<then>" 54)*)

value "LeftConst else Evaluate else Identity else Shift"


end