section "Stratego"
theory Stratego
  imports Main "HOL-Library.Finite_Map" "HOL-Library.Word"
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
class Rewritable = size +
  fixes rewrite :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes match :: "'a \<Rightarrow> 'a \<Rightarrow> ((string, 'a) fmap) option"
  fixes varof :: "'a \<Rightarrow> string option"
  fixes var :: "string \<Rightarrow> 'a"
  fixes subexprs :: "'a \<Rightarrow> 'a list"
  (*fixes map :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"*)
  fixes chain :: "nat \<Rightarrow> ('a \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a)) \<Rightarrow> 'a \<Rightarrow> (nat \<times> 'a)"
  (*assumes "varof (var a) = Some a"
  assumes "traverse f t = traverse f (traverse f t)"*)
  assumes shrinks: "\<forall>e' \<in> set (subexprs e). size e > size e'"
begin
fun map_tree :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "map_tree f xs = snd (chain (0::nat) (\<lambda>e a. (plus a 1, f e)) xs)"
end


fun chain_list :: "'b \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> ('b \<times> 'c)) \<Rightarrow> 'a list \<Rightarrow> ('b \<times> 'c list)" where
  "chain_list a f [] = (a, [])" |
  "chain_list a f (x # xs) =
    (let (a', x') = f x a in
    (let (a'', xs') = (chain_list a' f xs) in (a'', x' # xs')))"



subsection "Rewrite Language"
datatype ('a::Rewritable) Strategy =
  id | \<comment> \<open>identity operator\<close>
  fail | \<comment> \<open>fail operator\<close>
  func "'a \<Rightarrow> 'a" | \<comment> \<open>apply an arbitrary function transformation to the subject\<close>
  ematch 'a ("_?" [121] 120) | \<comment> \<open>match the subject to the given Rewritable, updating the binding\<close>
  promote 'a ("_!" [121] 120) | \<comment> \<open>ground and promote the given Rewritable to the subject\<close>
  condition "'a Strategy" "'a Strategy" "'a Strategy" ("_ < _ + _" 105) \<comment> \<open>if the first strategy succeeds, apply the second, else the third\<close>

subsubsection "Language Extensions"

abbreviation seq :: "'a::Rewritable Strategy \<Rightarrow> 'a Strategy \<Rightarrow> 'a Strategy"
  (infixl ";" 110) where
  "s1; s2 \<equiv> s1 < s2 + fail"

abbreviation else :: "'a::Rewritable Strategy \<Rightarrow> 'a Strategy \<Rightarrow> 'a Strategy"
  ("_ <+ _" 111) where
  "s1 <+ s2 \<equiv> s1 < id + s2"

abbreviation rewrite_to :: "'a::Rewritable \<Rightarrow> 'a \<Rightarrow> 'a Strategy"
  ("_ \<rightarrow> _") where
  "(s1 \<rightarrow> s2) \<equiv> s1?; s2!"

abbreviation "wheref" :: "('a::Rewritable) Strategy \<Rightarrow> 'a Strategy" where
  "wheref x \<equiv> var ''_''?; x; var ''_''!"

abbreviation conditional_rewrite_to :: "'a::Rewritable \<Rightarrow> 'a \<Rightarrow> 'a Strategy \<Rightarrow> 'a Strategy"
  ("_ \<rightarrow> _ where _") where 
  "s1 \<rightarrow> s2 where s3 \<equiv> s1?; wheref s3; s2!"

definition not :: "('a::Rewritable) Strategy \<Rightarrow> 'a Strategy" where 
  "not s = (s < fail + id)"

abbreviation "apply" :: "(('a::Rewritable) \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Strategy" 
  ("<_>(_)") where
  "(<f>(vars)) \<equiv> vars!; func f"

fun wrap_pred :: "(('a::Rewritable) \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "wrap_pred f = (\<lambda>t. if f t then var ''true'' else var ''false'')"

abbreviation "pred" :: "(('a::Rewritable) \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a Strategy" 
  ("<_>?(_)") where
  "(<f>?(vars)) \<equiv> vars!; func (wrap_pred f); var ''true''?"

abbreviation assign :: "('a::Rewritable) \<Rightarrow> 'a Strategy \<Rightarrow> 'a Strategy" 
  ("_ := _") where 
  \<comment> \<open>This should be trm => vars but this doesn't work well in Isabelle so swapped argument order.\<close>
  "vars := trm \<equiv> trm; vars?"


subsection "Rewrite Semantics"

type_synonym 'a Binding = "(string, 'a) fmap"
type_synonym 'a State = "'a \<times> 'a Binding"

fun ground :: "('a::Rewritable) Binding \<Rightarrow> 'a \<Rightarrow> 'a" where
  "ground b trm = (case varof trm of
    Some v \<Rightarrow> (case fmlookup b v of Some v' \<Rightarrow> v' | None \<Rightarrow> trm) |
    None \<Rightarrow> trm)"

fun substitute :: "('a::Rewritable) Binding \<Rightarrow> 'a \<Rightarrow> 'a" where
  "substitute b trm = rewrite (ground b) trm"

fun eval :: "'a Strategy \<Rightarrow> ('a::Rewritable) State \<Rightarrow> ('a State \<times> bool)" where
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
  "eval (func f) (sub, b) = ((f sub, b), True)"


subsection "Example: Simple Arithmetic Rewrites"

datatype (discs_sels) Arithmetic =
  Add Arithmetic Arithmetic |
  Sub Arithmetic Arithmetic |
  UMinus Arithmetic |
  Number int |
  Variable string


instantiation Arithmetic :: Rewritable begin

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

fun chain_Arithmetic :: "nat \<Rightarrow> (Arithmetic \<Rightarrow> nat \<Rightarrow> (nat \<times> Arithmetic)) \<Rightarrow> Arithmetic \<Rightarrow> (nat \<times> Arithmetic)" where
  "chain_Arithmetic n f (Add x y) =
    (let (n', x') = f x n in
    (let (n'', y') = f y n' in
      (n'', Add x' y')))" |
  "chain_Arithmetic n f (Sub x y) =
    (let (n', x') = f x n in
    (let (n'', y') = f y n' in
      (n'', Sub x' y')))" |
  "chain_Arithmetic n f (UMinus x) =
    (let (n', x') = f x n in
      (n', UMinus x'))" |
  "chain_Arithmetic n f (Number v) = (n, (Number v))" |
  "chain_Arithmetic n f (Variable s) = (n, (Variable s))"

(*
fun map_Arithmetic where
  "map_Arithmetic f (Add x y) = (Add (f x) (f y))" |
  "map_Arithmetic f (Sub x y) = (Sub (f x) (f y))" |
  "map_Arithmetic f (UMinus x) = (UMinus (f x))" |
  "map_Arithmetic f (Number v) = (Number v)" |
  "map_Arithmetic f (Variable s) = (Variable s)"*)

(*instance proof qed*)
instance proof
  fix e :: Arithmetic
  show "\<forall>e' \<in> set (subexprs e). size e > size e'"
    by (cases e; simp)
qed
end



subsubsection "Rewrite Rules"

definition RedundantAdd :: "Arithmetic Strategy" where
  "RedundantAdd = ((Add (Variable ''a'') (Number (0::int))) \<rightarrow> (Variable ''a''))"

definition RedundantSub :: "Arithmetic Strategy" where
  "RedundantSub = ((Sub (Variable ''a'') (Number (0::int))) \<rightarrow> (Variable ''a''))"

definition ShiftConstRight :: "Arithmetic Strategy" where
  "ShiftConstRight = 
    ((Add (Variable ''a'') (Variable ''b'')) \<rightarrow> (Add (Variable ''b'') (Variable ''a''))
      where ((Variable ''a'')!; not (Number 0?)))"

fun negate :: "Arithmetic \<Rightarrow> Arithmetic" where
  "negate (Number v) = (Number (-v))" |
  "negate x = x"

definition EvalMinus :: "Arithmetic Strategy" where
  "EvalMinus = 
    ((UMinus (Variable ''a'')) \<rightarrow> ((Variable ''b''))
      where (<is_Number>?(Variable ''a''); ((Variable ''a'')!; func negate); (Variable ''b'')?))"

definition EvalMinus1 :: "Arithmetic Strategy" where
  "EvalMinus1 =
    (UMinus (Variable ''a'')) \<rightarrow> Variable ''b''
      where (<is_Number>?(Variable ''a''); (Variable ''b'') := (<negate>(Variable ''a'')))"

fun add :: "Arithmetic \<Rightarrow> Arithmetic" where
  "add (Add (Number v1) (Number v2)) = (Number (plus v1 v2))" |
  "add x = x"

definition EvalAdd :: "Arithmetic Strategy" where
  "EvalAdd =
    (Add (Variable ''a'') (Variable ''b'')) \<rightarrow> ((Variable ''c''))
      where (
        <is_Number>?(Variable ''a'');
        <is_Number>?(Variable ''b'');
        (Variable ''c'') := <add>(Add (Variable ''a'') (Variable ''b''))
      )"

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

value "eval EvalMinus ((UMinus (Number 10)), fmempty)"
value "eval EvalMinus ((UMinus (Add (Number 10) (Number 10))), fmempty)"
text \<open>@{value "eval EvalMinus ((UMinus (Number 10)), fmempty)"}\<close>

value "eval EvalAdd ((UMinus (Number 10)), fmempty)"
value "eval EvalAdd ((Add (Number 10) (Number 10)), fmempty)"
text \<open>@{value "eval EvalAdd ((Add (Number 10) (Number 10)), fmempty)"}\<close>

end