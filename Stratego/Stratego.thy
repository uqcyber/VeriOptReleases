section "Stratego"
theory Stratego
  imports Main "HOL-Library.Finite_Map" "HOL-Library.Word" Locale_Code.Locale_Code "HOL-Library.Monad_Syntax"
begin

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

locale Groundable =
  fixes eval :: "'a \<Rightarrow> 'c option"
  fixes ground :: "'a \<Rightarrow> (string \<rightharpoonup> 'b) \<Rightarrow> 'a"
  fixes is_ground :: "'a \<Rightarrow> bool"

type_synonym 'e Binding = "(string, 'e) fmap"

locale Rewritable =
  size size +
  Groundable eval_condition ground_condition is_ground_condition +
  Groundable eval_result ground_result is_ground_result
  for size :: "'a \<Rightarrow> nat"
  and eval_condition :: "'b \<Rightarrow> bool option"
  and ground_condition :: "'b \<Rightarrow> (string \<rightharpoonup> 'a) \<Rightarrow> 'b"
  and is_ground_condition :: "'b \<Rightarrow> bool"
  and eval_result :: "'c \<Rightarrow> 'a option"
  and ground_result :: "'c \<Rightarrow> (string \<rightharpoonup> 'a) \<Rightarrow> 'c"
  and is_ground_result :: "'c \<Rightarrow> bool"
 +
  fixes subexprs :: "'a \<Rightarrow> 'a list"
  fixes chain :: "('a \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a)) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a)"
  fixes rewrite :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes match_term :: "'a \<Rightarrow> 'a \<Rightarrow> ((string, 'a) fmap) option"
  fixes varof :: "'a \<Rightarrow> string option"
  fixes var :: "string \<Rightarrow> 'a"

  (*fixes eval_condition :: "'b \<Rightarrow> bool"
  fixes ground_condition :: "'b \<Rightarrow> (string \<rightharpoonup> 'a) \<Rightarrow> 'b option"

  fixes transform :: "'c \<Rightarrow> 'a \<Rightarrow> 'a option"*)

  assumes "a' \<subseteq>\<^sub>m a \<Longrightarrow> is_ground_condition (ground_condition c a') \<Longrightarrow> ground_condition c a' = ground_condition c a"
  assumes shrinks: "\<forall>e' \<in> set (subexprs e). size e > size e'"
  assumes "map f (subexprs e) = subexprs (snd (chain (\<lambda>e a. (plus a 1, f e)) e 0))"
  assumes "length (subexprs e) = fst (chain (\<lambda>e a. (plus a 1, f e)) e 0)"
  assumes "eval_condition c = None \<equiv> \<not>(is_ground_condition c)"
begin
(*fun rewrite :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "rewrite f xs = snd (chain (\<lambda>e a. (plus a 1, f e)) xs (0::nat))"*)

no_notation plus (infixl "+" 65)
no_notation less ("(_/ < _)"  [51, 51] 50)

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
      (case match_term s sub of
        None \<Rightarrow> ((sub, b), False) |
        Some v \<Rightarrow> ((sub, b ++\<^sub>f v), True))" |
  "eval (s1 < s2 + s3) u =
      (let (u', suc) = eval s1 u in
        if suc then eval s2 u' else eval s3 u')" |
  "eval id u = (u, True)" |
  "eval fail u = (u, False)" |
  "eval (condition e) (sub, b) = (case eval_condition (ground_condition e (fmlookup b)) of 
                                    Some e' \<Rightarrow> ((sub, b), e') |
                                    None \<Rightarrow> ((sub, b), False))" |
  "eval (func f) (sub, b) = (case eval_result (ground_result f (fmlookup b)) of
                                Some e' \<Rightarrow> ((e', b), True) |
                                None \<Rightarrow> ((sub, b), False))"

end


fun chain_list :: "'b \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> ('b \<times> 'c)) \<Rightarrow> 'a list \<Rightarrow> ('b \<times> 'c list)" where
  "chain_list a f [] = (a, [])" |
  "chain_list a f (x # xs) =
    (let (a', x') = f x a in
    (let (a'', xs') = (chain_list a' f xs) in (a'', x' # xs')))"

end