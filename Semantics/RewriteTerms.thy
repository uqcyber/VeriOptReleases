theory RewriteTerms
imports IRTreeEval Stratego.CompileRewrite
begin
                              
instantiation IRExpr :: Rewritable
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

fun chain_IRExpr :: "nat \<Rightarrow> (IRExpr \<Rightarrow> nat \<Rightarrow> (nat \<times> IRExpr)) \<Rightarrow> IRExpr \<Rightarrow> (nat \<times> IRExpr)" where
  "chain_IRExpr n f (UnaryExpr op x) =
    (let (n', x') = f x n in
      (n', UnaryExpr op x'))" |
  "chain_IRExpr n f (BinaryExpr op x y) =
    (let (n', x') = f x n in
    (let (n'', y') = f y n' in
      (n'', BinaryExpr op x' y')))" |
  "chain_IRExpr n f (ConditionalExpr c b1 b2) =
    (let (n', c') = f c n in
    (let (n'', b1') = f b1 n' in
    (let (n''', b2') = f b2 n'' in
      (n''', ConditionalExpr c' b1' b2'))))" |
  "chain_IRExpr n f e = (n, e)"

(*instance proof qed*)
instance proof
  fix e :: IRExpr
  show "\<forall>e' \<in> set (subexprs e). size e > size e'"
    by (cases e; simp)
next
  fix f :: "IRExpr \<Rightarrow> IRExpr"
  fix e :: IRExpr
  show "map f (subexprs e) = subexprs (snd (chain 0 (\<lambda>e a. (plus a 1, f e)) e))"
    by (cases e; simp)
next
  fix f :: "IRExpr \<Rightarrow> IRExpr"
  fix e :: IRExpr
  show "length (subexprs e) = fst (chain 0 (\<lambda>e a. (plus a 1, f e)) e)"
    by (cases e; simp)
qed
end

definition RedundantAdd :: "IRExpr Strategy" where
  "RedundantAdd = 
    ((BinaryExpr BinAdd (var ''b'') (ConstantExpr (IntVal 32 0))) 
      \<rightarrow> (var ''b''))"

definition RedundantSub :: "IRExpr Strategy" where
  "RedundantSub = 
    ((BinaryExpr BinSub (var ''a'') (ConstantExpr (IntVal 32 0)))
      \<rightarrow> (var ''a''))"

definition ShiftConstRight :: "IRExpr Strategy" where
  "ShiftConstRight = 
    ((BinaryExpr BinAdd (var ''a'') (var ''b'')) \<rightarrow> (BinaryExpr BinAdd (var ''b'') (var ''a''))
      where ((var ''a'')!; not (ConstantExpr (IntVal 32 0)?)))"

fun negate :: "IRExpr \<Rightarrow> IRExpr" where
  "negate (ConstantExpr v) = (ConstantExpr (intval_negate v))" |
  "negate x = x"

definition EvalMinus :: "IRExpr Strategy" where
  "EvalMinus = 
    ((UnaryExpr UnaryNeg (var ''a'')) \<rightarrow> ((var ''b''))
      where (<is_ConstantExpr>?(var ''a''); ((var ''a'')!; func negate); (var ''b'')?))"

definition EvalMinus1 :: "IRExpr Strategy" where
  "EvalMinus1 =
    (UnaryExpr UnaryNeg (var ''a'')) \<rightarrow> var ''b''
      where (<is_ConstantExpr>?(var ''a''); (var ''b'') := (<negate>(var ''a'')))"

fun add :: "IRExpr \<Rightarrow> IRExpr" where
  "add (BinaryExpr BinAdd (ConstantExpr v1) (ConstantExpr v2)) = (ConstantExpr (intval_add v1 v2))" |
  "add x = x"

definition EvalAdd :: "IRExpr Strategy" where
  "EvalAdd =
    (BinaryExpr BinAdd (var ''a'') (var ''b'')) \<rightarrow> ((var ''c''))
      where (
        <is_ConstantExpr>?(var ''a'');
        <is_ConstantExpr>?(var ''b'');
        (var ''c'') := <add>(BinaryExpr BinAdd (var ''a'') (var ''b''))
      )"

value "eval (RedundantAdd <+ RedundantSub)
        ((BinaryExpr BinAdd (ConstantExpr (IntVal 32 10)) (ConstantExpr (IntVal 32 10))), fmempty)"

\<comment> \<open>Successful application\<close>
value "eval (RedundantAdd <+ RedundantSub)
        ((BinaryExpr BinAdd (ConstantExpr (IntVal 32 10)) (ConstantExpr (IntVal 32 0))), fmempty)"

\<comment> \<open>Successful application in the second rule\<close>
value "eval (RedundantSub <+ RedundantAdd)
        ((BinaryExpr BinAdd (ConstantExpr (IntVal 32 10)) (ConstantExpr (IntVal 32 0))), fmempty)"

value "ShiftConstRight"
value "eval ShiftConstRight 
      ((BinaryExpr BinAdd (ConstantExpr (IntVal 32 10)) (ConstantExpr (IntVal 32 0))), fmempty)"
value "eval ShiftConstRight
      ((BinaryExpr BinAdd (ConstantExpr (IntVal 32 10))
                          (BinaryExpr BinAdd (ConstantExpr (IntVal 32 10)) (ConstantExpr (IntVal 32 20)))), fmempty)"

value "eval EvalMinus ((UnaryExpr UnaryNeg (ConstantExpr (IntVal 32 10))), fmempty)"
value "eval EvalMinus ((UnaryExpr UnaryNeg (BinaryExpr BinAdd (ConstantExpr (IntVal 32 10)) (ConstantExpr (IntVal 32 10)))), fmempty)"

value "eval EvalAdd ((UnaryExpr UnaryNeg (ConstantExpr (IntVal 32 10))), fmempty)"
value "eval EvalAdd ((BinaryExpr BinAdd (ConstantExpr (IntVal 32 10)) (ConstantExpr (IntVal 32 10))), fmempty)"

value "(choice [compile' RedundantAdd, compile' RedundantSub])"
value "(optimized_export (choice [compile' RedundantAdd, compile' RedundantSub]))"




text \<open>@{text "x * const 1 \<longrightarrow> x"}\<close>
fun alwaysTrue :: "IRExpr \<Rightarrow> bool" where
  "alwaysTrue e = True"

definition Identity where
  "Identity = generate 
    (BinaryExpr BinMul
      (var ''x'')
      (ConstantExpr (IntVal 32 1)))
    (var ''x'')
    (var ''x'', alwaysTrue)"

value "Identity"
value "(optimized_export (Identity))"

text \<open>@{text "const x * const y \<longrightarrow> const (x * y)"}\<close>
definition Evaluate where
  "Evaluate = generate 
    (BinaryExpr BinMul
      (ConstantVar STR ''x'')
      (ConstantVar STR ''y''))
    ((ConstantVar STR ''x''))
    (var ''x'', alwaysTrue)"
(* doesn't support constant evaluation *)
value "Evaluate"
value "(optimized_export (Evaluate))"

text \<open>@{text "x * const y \<longrightarrow> x << const (log2 y)"}\<close>
definition Shift where
  "Shift = generate 
    (BinaryExpr BinMul
      (var ''x'')
      (ConstantVar STR ''y''))
    ((BinaryExpr BinLeftShift (var ''x'') (ConstantVar STR ''y'')))
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