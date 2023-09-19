theory Arithmetic
  imports "HOL-Library.Finite_Map" "HOL-Library.Monad_Syntax"
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

end