theory ArithmeticExample
  imports JavaExport
begin


subsection "Example: Simple Arithmetic Rewrites"

datatype (discs_sels) Arithmetic =
  Add Arithmetic Arithmetic |
  Sub Arithmetic Arithmetic |
  UMinus Arithmetic |
  Number int |
  Variable string

fun compatible :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> bool" where
  "compatible s1 s2 = (\<forall>x \<in> fset (fmdom s1) . fmlookup s2 x \<noteq> None \<longrightarrow> fmlookup s1 x = fmlookup s2 x)"

fun union :: "(('a, 'b) fmap) option \<Rightarrow> (('a, 'b) fmap) option \<Rightarrow> (('a, 'b) fmap) option" where
  "union s1 s2 = do {
    s1' <- s1;
    s2' <- s2;
    if compatible s1' s2' then Some (s1' ++\<^sub>f s2') else None
  }"

fun match_Arithmetic :: "Arithmetic \<Rightarrow> Arithmetic \<Rightarrow> ((string, Arithmetic) fmap) option" where
  "match_Arithmetic (Add x y) (Add x' y') = 
    union (match_Arithmetic x x') (match_Arithmetic y y')" |
  "match_Arithmetic (Sub x y) (Sub x' y') =
    union (match_Arithmetic x x') (match_Arithmetic y y')" |
  "match_Arithmetic (UMinus x) (UMinus x') =
    (match_Arithmetic x x')" |
  "match_Arithmetic (Number v) (Number v') = (if v = v' then Some (fmempty) else None)" |
  "match_Arithmetic (Variable v) e = Some (fmupd v e fmempty)" |
  "match_Arithmetic _ _ = None"

fun varof_Arithmetic :: "Arithmetic \<Rightarrow> string option" where
  "varof_Arithmetic (Variable s) = Some s" |
  "varof_Arithmetic _ = None"

fun var_Arithmetic :: "string \<Rightarrow> Arithmetic" where
  "var_Arithmetic v = Variable v"

fun rewrite_Arithmetic :: "(Arithmetic \<Rightarrow> Arithmetic) \<Rightarrow> Arithmetic \<Rightarrow> Arithmetic" where
  "rewrite_Arithmetic f (Add x y) = f (Add (rewrite_Arithmetic f x) (rewrite_Arithmetic f y))" |
  "rewrite_Arithmetic f (Sub x y) = f (Sub (rewrite_Arithmetic f x) (rewrite_Arithmetic f y))" |
  "rewrite_Arithmetic f (UMinus x) = f (UMinus (rewrite_Arithmetic f x))" |
  "rewrite_Arithmetic f (Number v) = f (Number v)" |
  "rewrite_Arithmetic f (Variable s) = f (Variable s)"

fun subexprs_Arithmetic :: "Arithmetic \<Rightarrow> Arithmetic list" where
  "subexprs_Arithmetic (Add x y) = [x, y]" |
  "subexprs_Arithmetic (Sub x y) = [x, y]" |
  "subexprs_Arithmetic (UMinus x) = [x]" |
  "subexprs_Arithmetic (Number v) = []" |
  "subexprs_Arithmetic (Variable s) = []"

fun chain_Arithmetic :: "(Arithmetic \<Rightarrow> nat \<Rightarrow> (nat \<times> Arithmetic)) \<Rightarrow> Arithmetic \<Rightarrow> nat \<Rightarrow> (nat \<times> Arithmetic)" where
  "chain_Arithmetic f (Add x y) n =
    (let (n', x') = f x n in
    (let (n'', y') = f y n' in
      (n'', Add x' y')))" |
  "chain_Arithmetic f (Sub x y) n =
    (let (n', x') = f x n in
    (let (n'', y') = f y n' in
      (n'', Sub x' y')))" |
  "chain_Arithmetic f (UMinus x) n =
    (let (n', x') = f x n in
      (n', UMinus x'))" |
  "chain_Arithmetic f (Number v) n = (n, (Number v))" |
  "chain_Arithmetic f (Variable s) n = (n, (Variable s))"

datatype ArithmeticCondition =
  IsSub Arithmetic |
  IsNumber Arithmetic

fun eval_condition :: "ArithmeticCondition \<Rightarrow> bool option" where
  "eval_condition (IsSub (Sub x y)) = Some True" |
  "eval_condition (IsNumber (Number v)) = Some True" |
  "eval_condition (IsSub (Variable v)) = None" |
  "eval_condition (IsNumber (Variable v)) = None" |
  "eval_condition _ = Some False"

fun ground_condition :: "ArithmeticCondition \<Rightarrow> (string \<rightharpoonup> Arithmetic) \<Rightarrow> ArithmeticCondition" where
  "ground_condition (IsSub (Variable v)) f = (case f v of 
                                              Some v' \<Rightarrow> (IsSub v') |
                                              None \<Rightarrow> (IsSub (Variable v)))" |
  "ground_condition (IsNumber (Variable v)) f = (case f v of 
                                              Some v' \<Rightarrow> (IsNumber v') |
                                              None \<Rightarrow> (IsNumber (Variable v)))" |
  "ground_condition e f = e"

fun is_ground_condition :: "ArithmeticCondition \<Rightarrow> bool" where
  "is_ground_condition (IsSub e) = (\<not>(is_Variable e))" |
  "is_ground_condition (IsNumber e) = (\<not>(is_Variable e))"

datatype Transformer =
  UnaryMinus Arithmetic |
  Plus Arithmetic Arithmetic |
  Result Arithmetic

fun eval_transformer :: "Transformer \<Rightarrow> Arithmetic option" where
  "eval_transformer (UnaryMinus (Number x)) = Some (Number (-x))" |
  "eval_transformer (Plus (Number x) (Number y)) = Some (Number (plus x y))" |
  "eval_transformer (Result a) = Some a" |
  "eval_transformer _ = None"

fun ground_transformer :: "Transformer \<Rightarrow> (string \<rightharpoonup> Arithmetic) \<Rightarrow> Transformer" where
  "ground_transformer (UnaryMinus (Variable v)) f = (case f v of 
                                              Some v' \<Rightarrow> (UnaryMinus v') |
                                              None \<Rightarrow> (UnaryMinus (Variable v)))" |
  "ground_transformer (Plus (Variable x) (Variable y)) f = (case f x of 
                                              Some x' \<Rightarrow> (
                                                case f y of Some y' \<Rightarrow> (Plus x' y')
                                                            | None \<Rightarrow> (Plus (Variable x) (Variable y)))
                                              | None \<Rightarrow> (Plus (Variable x) (Variable y)))" |
  "ground_transformer (Result (Variable v)) f = (case f v of 
                                              Some v' \<Rightarrow> (Result v') |
                                              None \<Rightarrow> (Result (Variable v)))" |
  "ground_transformer e f = e"

fun is_ground_transformer :: "Transformer \<Rightarrow> bool" where
  "is_ground_transformer (UnaryMinus e) = is_Variable e" |
  "is_ground_transformer (Plus e1 e2) = (is_Variable e1 \<or> is_Variable e2)" |
  "is_ground_transformer (Result e) = is_Variable e"

setup \<open>Locale_Code.open_block\<close>
interpretation Arithmetic: CompiledRewrites
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


subsubsection "Stratego Rules"

definition "eval = Arithmetic.eval"
definition "var = var_Arithmetic"

notation Arithmetic.conditional_rewrite_to ("_ \<rightarrow> _ where _")
notation Arithmetic.not ("not _")
notation Arithmetic.condition ("condition _")
notation Arithmetic.func ("func _")

type_synonym StrategyRule = "(Arithmetic, ArithmeticCondition, Transformer) Arithmetic.Strategy"

code_datatype fmap_of_list
lemma fmlookup_of_list[code]: "fmlookup (fmap_of_list m) = map_of m"
  by (simp add: fmlookup_of_list)

export_code "eval" checking SML

definition RedundantAdd :: "StrategyRule" where
  "RedundantAdd = ((Add (var ''b'') (Number 0)) \<rightarrow> (var ''b''))"

value "eval (RedundantAdd) ((Add (Number 10) (Number 10)), fmempty)"

definition RedundantSub :: "StrategyRule" where
  "RedundantSub = ((Sub (var ''a'') (Number 0)) \<rightarrow> (var ''a'') where condition (IsSub (var ''a'')))"

value "eval (RedundantSub) ((Sub (Number 10) (Number 0)), fmempty)"
value "eval (RedundantSub) ((Sub (Sub (Number 100) (Number 1000)) (Number 0)), fmempty)"


definition ShiftConstRight :: "StrategyRule" where
  "ShiftConstRight = 
    ((Add (var ''a'') (var ''b'')) \<rightarrow> (Add (var ''b'') (var ''a''))
      where ((var ''a'')!; not (Number 0?)))"

definition ShiftConstRight2 :: "StrategyRule" where
  "ShiftConstRight2 = 
    ((Add (var ''a'') (var ''b'')) \<rightarrow> (Add (var ''b'') (var ''a''))
      where (condition (IsNumber (var ''a''))))"

definition EvalMinus :: "StrategyRule" where
  "EvalMinus = 
    ((UMinus (Variable ''a'')) \<rightarrow> ((Variable ''b''))
      where (condition (IsNumber (Variable ''a'')); func (UnaryMinus (Variable ''a'')); (Variable ''b'')?))"

definition EvalMinus1 :: "StrategyRule" where
  "EvalMinus1 =
    (UMinus (Variable ''a'')) \<rightarrow> Variable ''b''
      where (condition (IsNumber (Variable ''a'')); (Variable ''b'') := (func (UnaryMinus (Variable ''a''))))"

definition EvalAdd :: "StrategyRule" where
  "EvalAdd =
    ((Add (Variable ''a'') (Variable ''b'')) \<rightarrow> ((Variable ''c''))
      where (
        (condition (IsNumber (Variable ''a'')));
        (condition (IsNumber (Variable ''a'')));
        ((Variable ''c'') := (func (Plus (Variable ''a'') (Variable ''b''))))
      ))"

subsubsection "Rewrite Application"

text "
The combination of @{term RedundantAdd} and @{term RedundantSub}
provides us a rule that will eliminate zero in either add or sub expressions.
It is defined as @{term \<open>RedundantAdd <+ RedundantSub\<close>}.
The expanded version of this rule is:

@{value \<open>RedundantAdd <+ RedundantSub\<close>}"

\<comment> \<open>Failing to apply the rule\<close>
value "eval (RedundantAdd <+ RedundantSub) ((Add (Number 10) (Number 10)), fmempty)"
text \<open>@{value "eval (RedundantAdd <+ RedundantSub) ((Add (Number 10) (Number 10)), fmempty)"}\<close>

\<comment> \<open>Successful application\<close>
value "eval (RedundantAdd <+ RedundantSub) ((Add (Number 10) (Number 0)), fmempty)"
text \<open>@{value "eval (RedundantAdd <+ RedundantSub) ((Add (Number 10) (Number 0)), fmempty)"}\<close>

\<comment> \<open>Successful application in the second rule\<close>
value "eval (RedundantSub <+ RedundantAdd) ((Add (Number 10) (Number 0)), fmempty)"
text \<open>@{value "eval (RedundantSub <+ RedundantAdd) ((Add (Number 10) (Number 0)), fmempty)"}\<close>

value "ShiftConstRight"
value "eval ShiftConstRight ((Add (Number 0) (Number 10)), fmempty)"
value "eval ShiftConstRight ((Add (Number 10) (Add (Number 10) (Number 20))), fmempty)"
value "eval ShiftConstRight ((Add (Number 10) (Number 120)), fmempty)"

value "eval ShiftConstRight2 ((Add (Number 0) (Number 10)), fmempty)"
value "eval ShiftConstRight2 ((Add (Number 10) (Add (Number 10) (Number 20))), fmempty)"
value "eval ShiftConstRight2 ((Add (Number 10) (Number 120)), fmempty)"

value "eval EvalMinus ((UMinus (Number 10)), fmempty)"
value "eval EvalMinus ((UMinus (Add (Number 10) (Number 10))), fmempty)"
text \<open>@{value "eval EvalMinus ((UMinus (Number 10)), fmempty)"}\<close>

value "eval EvalAdd ((UMinus (Number 10)), fmempty)"
value "eval EvalAdd ((Add (Number 10) (Number 10)), fmempty)"
text \<open>@{value "eval EvalAdd ((Add (Number 10) (Number 10)), fmempty)"}\<close>

subsubsection \<open>Example: Match Pattern\<close>


definition "join = Arithmetic.join"
definition "generate = Arithmetic.generate"
definition "match_pattern = Arithmetic.match_pattern"
definition "optimized_export = Arithmetic.optimized_export"

export_code "optimized_export" checking SML

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
    (Result (var ''x''))"
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