section "Stratego"
theory Stratego
  imports Main "HOL-Library.Finite_Map" "HOL-Library.Word" Locale_Code.Locale_Code
begin

no_notation plus (infixl "+" 65)
no_notation less ("(_/ < _)"  [51, 51] 50)

text \<open>
We generalize the concept of a datatype that can be rewritten using Stratego
using the @{term Rewritable} class.

\begin{description}
  \item[rewrite] Provides a mechanism for rewriting the AST given 
    a leaf to leaf function applied to the root of the AST and returning the transformed AST.
  \item[match] Given two ASTs, return a binding of variables of the first AST to the concrete second AST
    if it matches, else return None.
  \item[varof] Extract the identifier of the given AST if it is a variable, else None.
  \item[var] Construct an AST to represent the variable given.
\end{description}
\<close>

type_synonym 'e Binding = "(string, 'e) fmap"

locale Rewritable = size +
  fixes rewrite :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes match :: "'a \<Rightarrow> 'a \<Rightarrow> ((string, 'a) fmap) option"
  fixes varof :: "'a \<Rightarrow> string option"
  fixes var :: "string \<Rightarrow> 'a"

  fixes eval_condition :: "'b \<Rightarrow> bool"
  fixes ground_condition :: "'b \<Rightarrow> 'a Binding \<Rightarrow> 'b option"

  fixes transform :: "'c \<Rightarrow> 'a \<Rightarrow> 'a option"

  fixes subexprs :: "'a \<Rightarrow> 'a list"
  (*fixes map :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"*)
  fixes chain :: "('a \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a)) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a)"
  (*assumes "varof (var a) = Some a"
  assumes "traverse f t = traverse f (traverse f t)"*)
  assumes shrinks: "\<forall>e' \<in> set (subexprs e). size e > size e'"
  assumes "map f (subexprs e) = subexprs (snd (chain (\<lambda>e a. (plus a 1, f e)) e 0))"
  assumes "length (subexprs e) = fst (chain (\<lambda>e a. (plus a 1, f e)) e 0)"
  (*assumes chain_term: "All chain_dom"*)
begin
fun map_tree :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "map_tree f xs = snd (chain (\<lambda>e a. (plus a 1, f e)) xs (0::nat))"

fun maybe_map_tree :: "('a \<Rightarrow> 'a option) \<Rightarrow> 'a \<Rightarrow> 'a option" where
  "maybe_map_tree f xs = 
    (let (flag, e') = (chain (\<lambda>e a. (if (f e) = None then 1 else 0, the (f e))) xs (0::nat)) in
      (if flag = 1 then None else Some e'))"

fun pattern_variables :: "'a \<Rightarrow> string list" where
  "pattern_variables e = List.map_filter varof (subexprs e)"




subsection "Rewrite Language"
datatype ('e, 'cond, 't) Strategy =
  id | \<comment> \<open>identity operator\<close>
  fail | \<comment> \<open>fail operator\<close>
  condition "'cond" | \<comment> \<open>check a condition holds for the subject\<close>
  func "'t" | \<comment> \<open>apply an arbitrary function transformation to the subject\<close>
  ematch 'e ("_?" [121] 120) | \<comment> \<open>match the subject to the given Rewritable, updating the binding\<close>
  promote 'e ("_!" [121] 120) | \<comment> \<open>ground and promote the given Rewritable to the subject\<close>
  conditional "('e, 'cond, 't) Strategy" "('e, 'cond, 't) Strategy" "('e, 'cond, 't) Strategy" ("_ < _ + _" 105) \<comment> \<open>if the first strategy succeeds, apply the second, else the third\<close>

subsubsection "Language Extensions"

abbreviation seq :: "('a, 'b, 'c) Strategy \<Rightarrow> ('a, 'b, 'c) Strategy \<Rightarrow> ('a, 'b, 'c) Strategy"
  (infixl ";" 110) where
  "s1; s2 \<equiv> s1 < s2 + fail"

abbreviation else :: "('a, 'b, 'c) Strategy \<Rightarrow> ('a, 'b, 'c) Strategy \<Rightarrow> ('a, 'b, 'c) Strategy"
  ("_ <+ _" 111) where
  "s1 <+ s2 \<equiv> s1 < id + s2"

abbreviation rewrite_to :: "'a \<Rightarrow> 'a \<Rightarrow> ('a, 'b, 'c) Strategy"
  ("_ \<rightarrow> _") where
  "(s1 \<rightarrow> s2) \<equiv> s1?; s2!"

abbreviation "wheref" :: "('a, 'b, 'c) Strategy \<Rightarrow> ('a, 'b, 'c) Strategy" where
  "wheref x \<equiv> var ''_''?; x; var ''_''!"

abbreviation conditional_rewrite_to :: "'a \<Rightarrow> 'a \<Rightarrow> ('a, 'b, 'c) Strategy \<Rightarrow> ('a, 'b, 'c) Strategy"
  ("_ \<rightarrow> _ where _") where 
  "s1 \<rightarrow> s2 where s3 \<equiv> s1?; wheref s3; s2!"

abbreviation not :: "('a, 'b, 'c) Strategy \<Rightarrow> ('a, 'b, 'c) Strategy" where 
  "not s \<equiv> (s < fail + id)"

abbreviation "apply" :: "('c) \<Rightarrow> 'a \<Rightarrow> ('a, 'b, 'c) Strategy" 
  ("<_>(_)") where
  "(<f>(vars)) \<equiv> vars!; func f"

abbreviation "pred" :: "('b) \<Rightarrow> 'a \<Rightarrow> ('a, 'b, 'c) Strategy" 
  ("<_>?(_)") where
  "(<f>?(vars)) \<equiv> vars!; condition f"

abbreviation assign :: "'a \<Rightarrow> ('a, 'b, 'c) Strategy \<Rightarrow> ('a, 'b, 'c) Strategy" 
  ("_ := _") where 
  \<comment> \<open>This should be trm => vars but this doesn't work well in Isabelle so swapped argument order.\<close>
  "vars := trm \<equiv> trm; vars?"


subsection "Rewrite Semantics"

type_synonym 'e State = "'e \<times> 'e Binding"

fun ground :: "('a) Binding \<Rightarrow> 'a \<Rightarrow> 'a" where
  "ground b trm = (case varof trm of
    Some v \<Rightarrow> (case fmlookup b v of Some v' \<Rightarrow> v' | None \<Rightarrow> trm) |
    None \<Rightarrow> trm)"

fun substitute :: "('a) Binding \<Rightarrow> 'a \<Rightarrow> 'a" where
  "substitute b trm = rewrite (ground b) trm"

fun eval :: "('a, 'b, 'c) Strategy \<Rightarrow> ('a) State \<Rightarrow> ('a State \<times> bool)" where
  "eval (s!) (sub, b) = ((substitute b s, b), True)" |
  "eval (s?) (sub, b) =
      (case match s sub of
        None \<Rightarrow> ((sub, b), False) |
        Some v \<Rightarrow> ((sub, b ++\<^sub>f v), True))" |
  "eval (s1 < s2 + s3) u =
      (let (u', suc) = eval s1 u in
        if suc then eval s2 u' else eval s3 u')" |
  "eval id u = (u, True)" |
  "eval fail u = (u, False)" |
  "eval (condition e) (sub, b) = (case (ground_condition e b) of 
                                    Some e' \<Rightarrow> ((sub, b), eval_condition e') |
                                    None \<Rightarrow> ((sub, b), False))" |
  "eval (func f) (sub, b) = (case transform f sub of
                                Some sub' \<Rightarrow> ((sub', b), True) |
                                None \<Rightarrow> ((sub, b), False))"

end


fun chain_list :: "'b \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> ('b \<times> 'c)) \<Rightarrow> 'a list \<Rightarrow> ('b \<times> 'c list)" where
  "chain_list a f [] = (a, [])" |
  "chain_list a f (x # xs) =
    (let (a', x') = f x a in
    (let (a'', xs') = (chain_list a' f xs) in (a'', x' # xs')))"

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
  "union s1 s2 = 
      (case s1 of
       None \<Rightarrow> None |
       Some s1' \<Rightarrow>
           (case s2 of
            None \<Rightarrow> None |
            Some s2' \<Rightarrow> (if compatible s1' s2' then Some (s1' ++\<^sub>f s2') else None)
           )
      )"

fun rewrite_Arithmetic :: "(Arithmetic \<Rightarrow> Arithmetic) \<Rightarrow> Arithmetic \<Rightarrow> Arithmetic" where
  "rewrite_Arithmetic f (Add x y) = f (Add (rewrite_Arithmetic f x) (rewrite_Arithmetic f y))" |
  "rewrite_Arithmetic f (Sub x y) = f (Sub (rewrite_Arithmetic f x) (rewrite_Arithmetic f y))" |
  "rewrite_Arithmetic f (UMinus x) = f (UMinus (rewrite_Arithmetic f x))" |
  "rewrite_Arithmetic f (Number v) = f (Number v)" |
  "rewrite_Arithmetic f (Variable s) = f (Variable s)"

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

(*
locale ConditionalRewritable = Rewritable +
  fixes condition :: "'b \<Rightarrow> 'a Strategy"
  fixes eval_condition :: "'b \<Rightarrow> bool"
  fixes ground :: "'b \<Rightarrow> 'a Binding \<Rightarrow> 'b option"
begin

lemma eval_condition[code]:
  "eval (condition e) (s, state) = (case (ground e state) of 
                                    Some e' \<Rightarrow> ((s, state), eval_condition e') |
                                    None \<Rightarrow> ((s, state), False))"
  sorry

end
*)

datatype ArithmeticCondition =
  IsSub Arithmetic |
  IsNumber Arithmetic

fun eval_condition :: "ArithmeticCondition \<Rightarrow> bool" where
  "eval_condition (IsSub (Sub x y)) = True" |
  "eval_condition (IsNumber (Number v)) = True" |
  "eval_condition _ = False"

fun ground_condition :: "ArithmeticCondition \<Rightarrow> (string, Arithmetic) fmap \<Rightarrow> ArithmeticCondition option" where
  "ground_condition (IsSub (Variable v)) f = (case fmlookup f v of 
                                              Some v' \<Rightarrow> Some (IsSub v') |
                                              None \<Rightarrow> None)" |
  "ground_condition (IsNumber (Variable v)) f = (case fmlookup f v of 
                                              Some v' \<Rightarrow> Some (IsNumber v') |
                                              None \<Rightarrow> None)" |
  "ground_condition e f = None"


datatype Transformer =
  UnaryMinus |
  Plus

fun transform_eval :: "Transformer \<Rightarrow> Arithmetic \<Rightarrow> Arithmetic option" where
  "transform_eval UnaryMinus (Number v) = Some (Number (-v))" |
  "transform_eval Plus (Add (Number v1) (Number v2)) = Some (Number (plus v1 v2))" |
  "transform_eval _ _ = None"

setup \<open>Locale_Code.open_block\<close>
interpretation Arithmetic: Rewritable 
  size_Arithmetic
  rewrite_Arithmetic
  match_Arithmetic
  varof_Arithmetic
  var_Arithmetic
  "eval_condition"
  "ground_condition"
  transform_eval
  subexprs_Arithmetic
  chain_Arithmetic
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


(*
setup \<open>Locale_Code.open_block\<close>
interpretation ArithmeticCondition : ConditionalRewritable
  size_Arithmetic
  rewrite_Arithmetic
  match_Arithmetic
  varof_Arithmetic
  var_Arithmetic
  subexprs_Arithmetic
  chain_Arithmetic
  condition
  
  by standard
setup \<open>Locale_Code.close_block\<close>
*)


subsubsection "Rewrite Rules"

definition "eval = Arithmetic.eval"
definition "var = var_Arithmetic"

notation Arithmetic.conditional_rewrite_to ("_ \<rightarrow> _ where _")
notation Arithmetic.not ("not _")
notation Arithmetic.condition ("condition _")
notation Arithmetic.func ("func _")

type_synonym StrategyRule = "(Arithmetic, ArithmeticCondition, Transformer) Arithmetic.Strategy"


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
      where (condition (IsNumber (Variable ''a'')); ((Variable ''a'')!; func UnaryMinus); (Variable ''b'')?))"

definition EvalMinus1 :: "StrategyRule" where
  "EvalMinus1 =
    (UMinus (Variable ''a'')) \<rightarrow> Variable ''b''
      where (condition (IsNumber (Variable ''a'')); (Variable ''b'') := (<UnaryMinus>(Variable ''a'')))"

definition EvalAdd :: "StrategyRule" where
  "EvalAdd =
    ((Add (Variable ''a'') (Variable ''b'')) \<rightarrow> ((Variable ''c''))
      where (
        (condition (IsNumber (Variable ''a'')));
        (condition (IsNumber (Variable ''a'')));
        ((Variable ''c'') := <Plus>(Add (Variable ''a'') (Variable ''b'')))
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
value "eval ShiftConstRight ((Add (Number 10) (Number 10)), fmempty)"

value "eval ShiftConstRight2 ((Add (Number 0) (Number 10)), fmempty)"
value "eval ShiftConstRight2 ((Add (Number 10) (Add (Number 10) (Number 20))), fmempty)"
value "eval ShiftConstRight2 ((Add (Number 10) (Number 10)), fmempty)"

value "eval EvalMinus ((UMinus (Number 10)), fmempty)"
value "eval EvalMinus ((UMinus (Add (Number 10) (Number 10))), fmempty)"
text \<open>@{value "eval EvalMinus ((UMinus (Number 10)), fmempty)"}\<close>

value "eval EvalAdd ((UMinus (Number 10)), fmempty)"
value "eval EvalAdd ((Add (Number 10) (Number 10)), fmempty)"
text \<open>@{value "eval EvalAdd ((Add (Number 10) (Number 10)), fmempty)"}\<close>

notation plus (infixl "+" 65)
notation less ("(_/ < _)"  [51, 51] 50)

end