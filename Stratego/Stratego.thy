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
class Rewritable =
  fixes rewrite :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"
  fixes match :: "'a \<Rightarrow> 'a \<Rightarrow> ((string, 'a) fmap) option"
  fixes varof :: "'a \<Rightarrow> string option"
  fixes var :: "string \<Rightarrow> 'a"
  fixes subexprs :: "'a \<Rightarrow> 'a list"
  (*fixes map :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"*)
  fixes chain :: "nat \<Rightarrow> ('a \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a)) \<Rightarrow> 'a \<Rightarrow> (nat \<times> 'a)"
  (*assumes "varof (var a) = Some a"
  assumes "traverse f t = traverse f (traverse f t)"*)
begin
fun map :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "map f xs = snd (chain (0::nat) (\<lambda>e a. (plus a 1, f e)) xs)"
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
  ("[_](_)") where
  "([f](vars)) \<equiv> vars!; func (wrap_pred f); var ''true''?"

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

(*fun chain :: "'b \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> ('b \<times> 'a)) \<Rightarrow> 'a list \<Rightarrow> ('b \<times> 'a list)" where
  "chain a f [] = (a, [])" |
  "chain a f (x # xs) =
    (let (a', x') = f x a in
    (let (a'', xs') = (chain a' f xs) in (a'', x' # xs')))"*)

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

instance proof qed

(*instance proof
  fix a :: string
  fix f :: "Arithmetic \<Rightarrow> Arithmetic"
  fix t :: Arithmetic
  show "traverse f t = traverse f (traverse f t)"
    apply (induction t) apply simp sorry
qed*)
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
      where ([is_Number](Variable ''a''); ((Variable ''a'')!; func negate); (Variable ''b'')?))"

definition EvalMinus1 :: "Arithmetic Strategy" where
  "EvalMinus1 =
    (UMinus (Variable ''a'')) \<rightarrow> ((Variable ''b''))
      where ([is_Number](Variable ''a''); (Variable ''b'') := (<negate>(Variable ''a'')))"

fun add :: "Arithmetic \<Rightarrow> Arithmetic" where
  "add (Add (Number v1) (Number v2)) = (Number (plus v1 v2))" |
  "add x = x"

definition EvalAdd :: "Arithmetic Strategy" where
  "EvalAdd =
    (Add (Variable ''a'') (Variable ''b'')) \<rightarrow> ((Variable ''c''))
      where (
        [is_Number](Variable ''a'');
        [is_Number](Variable ''b'');
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






class ShallowRewritable =
  fixes base :: "'a itself \<Rightarrow> Arithmetic itself"

syntax "_type_base" :: "type \<Rightarrow> string" (\<open>(1BASE/(1'(_')))\<close>)

translations "BASE('a)" \<rightharpoonup>
  "CONST base (CONST Pure.type :: 'a itself)"

print_translation \<open>
  let
    fun len_of_itself_tr' ctxt [Const (\<^const_syntax>\<open>Pure.type\<close>, Type (_, [T]))] =
      Syntax.const \<^syntax_const>\<open>_type_base\<close> $ Syntax_Phases.term_of_typ ctxt T
  in [(\<^const_syntax>\<open>base\<close>, len_of_itself_tr')] end
\<close>

(* TODO: can this be automatically generated? *)
(*datatype ShallowArithmetic =
  Add string string |
  Sub string string |
  UMinus string |
  Number int
*)

type_synonym VarName = "string"
type_synonym Vars = "VarName fset"

type_synonym Scope = "Vars \<times> (VarName \<rightharpoonup> VarName)"

fun remove_var :: "VarName \<Rightarrow> Scope \<Rightarrow> Scope" where
  "remove_var v (vs, m) = (vs - {|v|}, m)"
fun add_var :: "VarName \<Rightarrow> Scope \<Rightarrow> Scope" where
  "add_var v (vs, m) = (vs |\<union>| {|v|}, m)"


function fresh_var :: "VarName \<Rightarrow> Scope \<Rightarrow> VarName" where
  "fresh_var v s = 
    (if v |\<in>| (fst s) 
      then fresh_var (v @ ''z'') (remove_var v s)
      else v)"
  by fastforce+
(*(* For some reason, by proving that this function terminates the definition of match_pattern
   no longer terminates. *)
termination
  apply (relation "measure (\<lambda>(v, s). (fcard (fst s)))")
  apply simp
  using fcard_fminus1_less by force*)

fun fresh :: "VarName \<Rightarrow> Scope \<Rightarrow> Scope \<times> VarName" where
  "fresh v s = (let v = fresh_var v s in (add_var v s, v))"


lemma fresh [code]:
  "fresh_var v s = 
    (if v |\<in>| (fst s) 
      then fresh_var (v @ ''z'') (remove_var v s)
      else v)"
  sorry (* This will not be required when termination is proved *)


value "(fresh ''a'' o fst o fresh ''a'' o fst o fresh ''a'') ({|''e''|}, Map.empty)"

datatype 'a MATCH =
  match VarName "'a" |
  equality VarName VarName (infixl "==" 52) |
  andthen "'a MATCH" "'a MATCH" (infixl "&&" 50) |
  condition "'a" |
  noop

value "subexprs (Add (Add (Number 1) (Number 2)) (Number 3))"
value "map_MATCH ::Arithmetic MATCH"
value "case_MATCH ((match ''hey'' (Number 5))::Arithmetic MATCH)"
value "set_MATCH ((match ''hey'' (Number 5))::Arithmetic MATCH)"

value "map_MATCH (\<lambda>x. ''hi'') ((match ''hey'' (Number 5))::Arithmetic MATCH)"


text \<open>The definitions of la and ra help to feed the scope through when generating a match pattern.\<close>
definition la :: "('b \<Rightarrow> 'a) \<Rightarrow> (Scope \<Rightarrow> Scope \<times> 'b) \<Rightarrow> (Scope \<Rightarrow> Scope \<times> 'a)"
  (infix "\<langle>" 65)
  where
  "la f f' s = (fst (f' s), f (snd (f' s)))"

definition ra :: "(Scope \<Rightarrow> Scope \<times> ('b \<Rightarrow> 'a)) \<Rightarrow> (Scope \<Rightarrow> Scope \<times> 'b) \<Rightarrow> (Scope \<Rightarrow> Scope \<times> 'a)"
  (infixl "\<rangle>" 54)
  where
  "ra f f' s = ((fst (f' (fst (f s)))), (snd (f s)) (snd (f' (fst (f s)))))"

text \<open>Join generates the lhs and feeds the scope through to then generate the rhs.
      The resulting match pattern is an sequential match of the lhs and rhs, @{term "lhs && rhs"}.
      The resulting scope is the result of generating the rhs after the lhs.\<close>
(*definition join :: "('b \<Rightarrow> 'c \<times> ('d::Rewritable) MATCH) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'a \<times> 'd MATCH) \<Rightarrow> 'b \<Rightarrow> 'a \<times> 'd MATCH"
  (infixl "|>" 53) where
  "join x y s = 
    (let (lhs_scope, lhs_match) = x s in
    (let (rhs_scope, rhs_match) = (y s lhs_scope) in
    (rhs_scope, (lhs_match && rhs_match))))"

abbreviation descend where
  "descend f e v \<equiv> (\<lambda>s s'. f e (snd (fresh v s)) s')"*)

fun register_name where
  "register_name (s, m) vn v = (s, m(vn\<mapsto>v))"

(*
typedef (overloaded) ('a, 'b) fixed_list =
  "{l::'b list. LENGTH('a::len) = length l}"
  by (metis Ex_list_of_length mem_Collect_eq)

lemma "Rep_fixed_list ((Abs_fixed_list [1, 2])::(2, nat) fixed_list) = [1, 2]"
  sledgehammer

fun convert :: "('a::len, 'b) fixed_list \<Rightarrow> ('a, 'b) fixed_list" where
  "convert (Abs_fixed_list [x, y]) = (Abs_fixed_list [y, x])"
*)


(*
fun replace_subexprs :: "Scope \<Rightarrow> ('a::Rewritable) list \<Rightarrow> Scope \<times> ('a::Rewritable) list" where
  "replace_subexprs s = chain s (\<lambda>e s'. (let (s'', v) = (fresh ''a'' s') in (s'', var v)))"
*)

value "chain"

fun nth_fresh :: "VarName \<Rightarrow> Scope \<Rightarrow> nat \<Rightarrow> (Scope \<times> VarName)" where
  "nth_fresh v s 0 = fresh v s" |
  "nth_fresh v s (Suc n) = fresh v (fst (nth_fresh v s n))"

(*lemma nth_fresh [code]:
  "nth_fresh v s n = fresh v (fst (nth_fresh v s (n-1)))"
  sorry*)

(*termination nth_fresh sorry*)

fun replace_subexprs :: "Scope \<Rightarrow> ('a::Rewritable) \<Rightarrow> (Scope \<times> ('a::Rewritable))" where
  "replace_subexprs s e =
    (let (n, e') = chain 0 (\<lambda>e n. (plus n 1, var (snd (nth_fresh ''a'' s n)))) e
      in (fst (nth_fresh ''a'' s n), e'))"

fun expression_vars :: "Scope \<Rightarrow> ('a::Rewritable) \<Rightarrow> (Scope \<times> string list)" where
  "expression_vars s e = 
    (chain_list s (\<lambda>e' s'. (fresh ''a'' s')) (subexprs e))"

value "expression_vars ({|''e''|}, Map.empty) (Sub (Add (Variable ''x'') (Variable ''y'')) (Variable ''y''))"

fun replace_subexpr :: "string list \<Rightarrow> ('a::Rewritable) \<Rightarrow> ('a::Rewritable)" where
  "replace_subexpr vs e = snd (chain 0 (\<lambda>e n. (plus n 1, var (vs!n))) e)"

(*fun replace_subexprs :: "Scope \<Rightarrow> ('a::Rewritable) \<Rightarrow> ('a::Rewritable)" where
  "replace_subexprs s = map (\<lambda>_. var (snd (fresh ''a'' s)))"*)

type_synonym 'a MatchGenerator = "'a \<Rightarrow> VarName \<Rightarrow> Scope \<Rightarrow> Scope \<times> 'a MATCH"

abbreviation generate_subexprs :: "'a::Rewritable MatchGenerator \<Rightarrow> 'a \<Rightarrow> Scope \<Rightarrow> string list \<Rightarrow> ((Scope \<times> nat) \<times> 'a MATCH list)" where
  "generate_subexprs f e s vs \<equiv> 
     (chain_list (s, 0) (\<lambda>e' (s', n). 
        (let (scope, m) = (f e' (vs!n) s') in ((scope, plus n 1), m))) (subexprs e))"

fun join :: "('a MATCH) list \<Rightarrow> 'a MATCH" where
  "join [] = noop" |
  "join [x] = x" |
  "join (x # xs) = (x && join xs)"

function match_pattern :: "'a::Rewritable MatchGenerator" where
  "match_pattern e v =
    (case varof e of
      Some vn \<Rightarrow> (\<lambda>s. case (snd s) vn of 
        None \<Rightarrow> (register_name s vn v, noop) |
        Some v' \<Rightarrow> (register_name s vn v, equality v' v)) |
      None \<Rightarrow> (\<lambda>s.
        (let (s', vs) = expression_vars s e in
        (let e' = (replace_subexpr vs e) in
        (let ((s'', _), e'') = (generate_subexprs match_pattern e s' vs) in
                        (s'', (match v e' && join e'')))))))"
  using old.prod.exhaust apply blast
  by fastforce

termination match_pattern sorry

value "match_pattern
(Sub (Add (Variable ''x'') (Variable ''y'')) (Variable ''y''))
''e'' ({|''e''|}, Map.empty)"

value "match_pattern
(Sub 
    (Add 
        (Sub (Variable ''x'') (Variable ''x''))
        (Sub (Variable ''y'') (Variable ''x'')))
    (Variable ''y''))
''e'' ({|''e''|}, Map.empty)"


(*"match v \<langle> ((\<lambda>y. e) \<langle> fresh ''a'') |> descend match_pattern e ''a'')"

fun match_pattern :: "('a::Rewritable) \<Rightarrow> VarName \<Rightarrow> Scope \<Rightarrow> Scope \<times> 'a MATCH" where
  "match_pattern (UnaryExpr op e) v =
    match v \<langle>
      (UnaryPattern op \<langle> fresh ''a'')
    |> descend match_pattern e ''a''" |
  "match_pattern (BinaryExpr op e1 e2) v =
    match v \<langle> 
      (BinaryPattern op \<langle> fresh ''a'' \<rangle> fresh ''b'')
    |> descend match_pattern e1 ''a''
    |> descend match_pattern e2 ''b''" |
  "match_pattern (ConditionalExpr b e1 e2) v =
    match v \<langle>
      (ConditionalPattern \<langle> fresh ''a'' \<rangle> fresh ''b'' \<rangle> fresh ''c'')
    |> descend match_pattern b ''a''
    |> descend match_pattern e1 ''b''
    |> descend match_pattern e2 ''c''" |
  \<comment> \<open>If a variable is reused, generate an equality check, else, generate a noop.\<close>
  "match_pattern (VariableExpr vn st) v = 
    (\<lambda>s. case (snd s) vn of 
      None \<Rightarrow> (register_name s vn v, noop) |
      Some v' \<Rightarrow> (register_name s vn v, equality v' v))" |
  "match_pattern (ConstantExpr c) v =
    (\<lambda>s. (s, match v (ConstantPattern c)))" |
  "match_pattern (ConstantVar c) v =
    (\<lambda>s. (s, match v (ConstantVarPattern c)))" |
  "match_pattern _ v = (\<lambda>s. (s, noop))"*)

definition gen_pattern :: "('a::Rewritable) \<Rightarrow> VarName \<Rightarrow> 'a MATCH" where
  "gen_pattern p v = snd (match_pattern p v ({|v|}, Map.empty))"

subsubsection \<open>Match Primitive Semantics\<close>
type_synonym 'a Subst = "VarName \<rightharpoonup> 'a::Rewritable"

fun equal_ignore_vars :: "'a::Rewritable \<Rightarrow> 'a \<Rightarrow> bool" where
  "equal_ignore_vars e1 e2 = ((map (\<lambda>_. var ''a'') e1) = (map (\<lambda>_. var ''a'') e2))"

fun eval_match :: "('a::Rewritable) MATCH \<Rightarrow> 'a Subst \<Rightarrow> ('a Subst) option" where
  "eval_match (match v e) s =
    (case s v of
      Some e' \<Rightarrow>
        (if equal_ignore_vars e e' then
          Some (s((List.map (the o varof) (subexprs e)) [\<mapsto>] subexprs e')) else None) |
      None \<Rightarrow> None)" |
  "eval_match (equality v1 v2) s =
    (if v1 \<in> dom s \<and> v2 \<in> dom s \<and> s v1 = s v2 then Some s else None)" |
  "eval_match (andthen m1 m2) s =
      (case eval_match m1 s of 
        None \<Rightarrow> None |
        Some s' \<Rightarrow> eval_match m2 s')" |
  "eval_match noop s = Some s" |
  "eval_match (condition sc) s = None"

(*
fun eval_match :: "'a MATCH \<Rightarrow> 'a Subst \<Rightarrow> ('a Subst) option" where
  "eval_match (match v (UnaryPattern op1 x)) s =
    (case s v of 
      Some (UnaryExpr op2 xe) \<Rightarrow>
        (if op1 = op2 then
          (if x \<in> dom s then
            (if s x = Some xe then Some s else None)
          else Some (s(x\<mapsto>xe)))
         else None) |
      Some _ \<Rightarrow> None |
      None \<Rightarrow> None)" |
  "eval_match (match v (BinaryPattern op1 x y)) s =
    (case s v of
      Some (BinaryExpr op2 xe ye) \<Rightarrow>
        (if op1 = op2 
          then 
          (if x \<in> dom s \<and> s x \<noteq> Some xe then None else 
          (if y \<in> dom s \<and> s y \<noteq> Some ye then None else 
          (if x \<in> dom s \<and> y \<in> dom s then Some s else
          (if x \<in> dom s then Some (s(y\<mapsto>ye)) else
          (if y \<in> dom s then Some (s(x\<mapsto>xe)) else
          Some (s(x\<mapsto>xe, y\<mapsto>ye)))))))
          else None) |
      Some _ \<Rightarrow> None |
      None \<Rightarrow> None)" |
  "eval_match (match v (ConditionalPattern c tb fb)) s =
    (case s v of
      Some (ConditionalExpr ce te fe) \<Rightarrow>
        (if c \<in> dom s \<and> s c \<noteq> Some ce then None else 
          (if tb \<in> dom s \<and> s tb \<noteq> Some te then None else
          (if fb \<in> dom s \<and> s fb \<noteq> Some fe then None else 
          (if c \<in> dom s \<and> tb \<in> dom s \<and> fb \<in> dom s then Some s else
          (if c \<in> dom s \<and> tb \<in> dom s then Some (s(fb\<mapsto>fe)) else
          (if c \<in> dom s \<and> fb \<in> dom s then Some (s(tb\<mapsto>te)) else
          (if tb \<in> dom s \<and> fb \<in> dom s then Some (s(c\<mapsto>ce)) else
          (if c \<in> dom s then Some (s(tb\<mapsto>te, fb\<mapsto>fe)) else
          (if tb \<in> dom s then Some (s(c\<mapsto>ce, fb\<mapsto>fe)) else
          (if fb \<in> dom s then Some (s(c\<mapsto>ce, tb\<mapsto>te)) else
          Some (s(c\<mapsto>ce, tb\<mapsto>te, fb\<mapsto>fe)))))))))))) |
      Some _ \<Rightarrow> None |
      None \<Rightarrow> None)" |
  "eval_match (match v (ConstantPattern c1)) s =
    (case s v of 
      Some (ConstantExpr c2) \<Rightarrow>
        (if c1 = c2 then Some s else None) |
      Some _ \<Rightarrow> None |
      None \<Rightarrow> None)" |
  "eval_match (equality v1 v2) s =
    (if v1 \<in> dom s \<and> v2 \<in> dom s \<and> s v1 = s v2 then Some s else None)" |
  "eval_match (andthen m1 m2) s =
      (case eval_match m1 s of 
        None \<Rightarrow> None |
        Some s' \<Rightarrow> eval_match m2 s')" |
  "eval_match noop s = Some s" |
  "eval_match (condition sc) s = (if eval_condition sc then Some s else None)" |
  "eval_match _ s = None"
*)


subsection \<open>Combining Rules\<close>

datatype 'a Rules =
  base "'a::Rewritable" |
  cond "'a MATCH" "'a Rules" (infixl "?" 52) |
  else "'a Rules" "'a Rules" (infixl "else" 50) |
  seq "'a Rules" "'a Rules" (infixl "\<then>" 49) |
  choice "('a Rules) list"

function ground_expr :: "'a::Rewritable \<Rightarrow> Scope \<Rightarrow> 'a" where
  "ground_expr e (s, m) =
    (case varof e of
      Some v \<Rightarrow>(case m v of None \<Rightarrow> var v 
                | Some v' \<Rightarrow> var v') |
      None \<Rightarrow> map (\<lambda>e'. ground_expr e' (s, m)) e)"
  apply auto[1]
  by fastforce

termination ground_expr sorry
(*
    UnaryExpr op (ground_expr e s)" |
  "ground_expr (BinaryExpr op e1 e2) s = 
    BinaryExpr op (ground_expr e1 s) (ground_expr e2 s)" |
  "ground_expr (ConditionalExpr b e1 e2) s = 
    ConditionalExpr (ground_expr b s) (ground_expr e1 s) (ground_expr e2 s)" |
  "ground_expr (VariableExpr vn st) (s, m) = 
    (case m vn of None \<Rightarrow> VariableExpr vn st 
                | Some v' \<Rightarrow> VariableExpr v' st)" |
  "ground_expr e s = e"*)

(*fun ground_result :: "Result \<Rightarrow> Scope \<Rightarrow> Result" where
  "ground_result (ExpressionResult e) s = ExpressionResult (ground_expr e s)" |
  "ground_result (forZero e) s = forZero (ground_expr e s)"

fun ground_condition :: "SideCondition \<Rightarrow> Scope \<Rightarrow> SideCondition" where
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
  "ground_condition (Empty) s = Empty"*)

fun generate :: "'a::Rewritable \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a Rules" where
  "generate p r sc = 
    (let (s, m) = match_pattern p ''e'' ({||}, (\<lambda>x. None))
     in ((m && condition (ground_expr sc s)) ? (base (ground_expr r s))))"

subsubsection \<open>Rules Semantics\<close>
definition start_unification where
  "start_unification e = ((\<lambda>x. None)(STR ''e'' := Some e))"

text \<open>Replace any variable expressions with value in a substitution.\<close>
fun evaluated_terms where
  "evaluated_terms f es s = (List.map (\<lambda>e. f e s) es)"

fun has_none :: "('a option) list \<Rightarrow> bool" where
  "has_none [] = False" |
  "has_none (x # xs) = ((x = None) \<and> has_none xs)"

function eval_expr :: "'a::Rewritable \<Rightarrow> 'a Subst \<Rightarrow> 'a option" where
  "eval_expr e u =
    (case varof e of
        Some v \<Rightarrow> u v
      | None \<Rightarrow> 
        (if has_none (evaluated_terms eval_expr (subexprs e) u)
          then None
          else Some (map (the o (\<lambda>e'. eval_expr e' u)) e)))"
  by fastforce+

termination eval_expr sorry

(*
  "eval_expr (UnaryExpr op e) u = (case (eval_expr e u)
    of None \<Rightarrow> None | Some e' \<Rightarrow> Some (UnaryExpr op e'))" |
  "eval_expr (BinaryExpr op e1 e2) u = (case (eval_expr e1 u)
    of None \<Rightarrow> None | Some e1' \<Rightarrow> 
    (case (eval_expr e2 u)
      of None \<Rightarrow> None | Some e2' \<Rightarrow> Some (BinaryExpr op e1' e2')))" |
  "eval_expr (ConditionalExpr e1 e2 e3) u = (case (eval_expr e1 u)
    of None \<Rightarrow> None | Some e1' \<Rightarrow>
    (case (eval_expr e2 u)
      of None \<Rightarrow> None | Some e2' \<Rightarrow>
        (case (eval_expr e2 u)
          of None \<Rightarrow> None | Some e3' \<Rightarrow> Some (ConditionalExpr e1' e2' e3'))))" |
  "eval_expr e u = Some e"


fun eval_result :: "Result \<Rightarrow> Subst \<Rightarrow> IRExpr option" where
  "eval_result (ExpressionResult e) s = (eval_expr e s)" |
  "eval_result (forZero e) s = (case eval_expr e s of
    None \<Rightarrow> None |
    Some r \<Rightarrow> Some (ConstantExpr (IntVal (stp_bits (stamp_expr r)) 0)))"

lemma remove1_size:
  "x \<in> set xs \<Longrightarrow> size (remove1 x xs) < size xs"
  by (metis diff_less length_pos_if_in_set length_remove1 zero_less_one)
*)

inductive eval_rules :: "('a::Rewritable) Rules \<Rightarrow> 'a Subst \<Rightarrow> 'a option \<Rightarrow> bool" where
  \<comment> \<open>Evaluate the result\<close>
  "eval_rules (base e) u (eval_expr e u)" |

  \<comment> \<open>Evaluate a condition\<close>
  "\<lbrakk>eval_match m u = Some u' \<and>
    eval_rules r u' e\<rbrakk>
   \<Longrightarrow> eval_rules (cond m r) u e" |
  "\<lbrakk>eval_match m u = None\<rbrakk>
   \<Longrightarrow> eval_rules (cond m r) u None" |

  \<comment> \<open>Evaluate else\<close>
  "\<lbrakk>eval_rules r1 u (Some r)\<rbrakk>
   \<Longrightarrow> eval_rules (r1 else r2) u (Some r)" |
  "\<lbrakk>eval_rules r1 u None \<and>
    eval_rules r2 u e\<rbrakk>
   \<Longrightarrow> eval_rules (r1 else r2) u e" |

  \<comment> \<open>Evaluate choice\<close>
  "\<lbrakk>rule \<in> set rules \<and>
    eval_rules rule u (Some r)\<rbrakk>
   \<Longrightarrow> eval_rules (choice rules) u (Some r)" |
  "\<lbrakk>\<forall> rule \<in> set rules. eval_rules rule u None\<rbrakk>
   \<Longrightarrow> eval_rules (choice rules) u None" |
  "\<lbrakk>rules = []\<rbrakk>
   \<Longrightarrow> eval_rules (choice rules) u None" |

  \<comment> \<open>Evaluate sequential\<close>
  "\<lbrakk>eval_rules r1 u (Some e') \<and>
    eval_rules r2 (u(''e'' \<mapsto> e')) r\<rbrakk>
   \<Longrightarrow> eval_rules (r1 \<then> r2) u r" |
  "\<lbrakk>eval_rules r1 u None \<and>
    eval_rules r2 u r\<rbrakk>
   \<Longrightarrow> eval_rules (r1 \<then> r2) u r"











subsection \<open>Rule Optimization\<close>

fun elim_noop :: "'a MATCH \<Rightarrow> 'a MATCH" where
  "elim_noop (lhs && noop) = elim_noop lhs" |
  "elim_noop (noop && rhs) = elim_noop rhs" |
  "elim_noop (lhs && rhs) = ((elim_noop lhs) && (elim_noop rhs))" |
  "elim_noop m = m"

fun eliminate_noop :: "'a::Rewritable Rules \<Rightarrow> 'a Rules" where
  "eliminate_noop (base e) = base e" |
  "eliminate_noop (m ? r) = elim_noop m ? eliminate_noop r" |
  "eliminate_noop (r1 else r2) = (eliminate_noop r1 else eliminate_noop r2)" |
  "eliminate_noop (choice rules) = choice (List.map eliminate_noop rules)" |
  "eliminate_noop (r1 \<then> r2) = (eliminate_noop r1 \<then> eliminate_noop r2)"

fun elim_empty :: "'a MATCH \<Rightarrow> 'a MATCH" where
  "elim_empty (condition Empty) = noop" |
  "elim_empty (m1 && m2) = (elim_empty m1 && elim_empty m2)" |
  "elim_empty m = m"

fun eliminate_empty :: "'a::Rewritable Rules \<Rightarrow> 'a Rules" where
  "eliminate_empty (base e) = base e" |
  "eliminate_empty (m ? r) = elim_empty m ? eliminate_empty r" |
  "eliminate_empty (r1 else r2) = (eliminate_empty r1 else eliminate_empty r2)" |
  "eliminate_empty (choice rules) = choice (List.map eliminate_empty rules)" |
  "eliminate_empty (r1 \<then> r2) = (eliminate_empty r1 \<then> eliminate_empty r2)"


notation plus (infixl "+" 65)
fun combined_size :: "'a::Rewritable Rules \<Rightarrow> nat" where
  "combined_size (m ? r) = (2 * size m) + combined_size r" |
  "combined_size (base e) = 0" |
  "combined_size (r1 else r2) = combined_size r1 + combined_size r2" |
  "combined_size (choice (rule # rules)) = 1 + combined_size rule + combined_size (choice rules)" |
  "combined_size (choice []) = 1" |
  "combined_size (r1 \<then> r2) = combined_size r1 + combined_size r2"
no_notation plus (infixl "+" 65)

function (sequential) lift_match :: "'a::Rewritable Rules \<Rightarrow> 'a Rules" where
  "lift_match (r1 else r2) = ((lift_match r1) else (lift_match r2))" |
  "lift_match (choice rules) = choice (List.map lift_match rules)" |
  "lift_match ((m1 && m2) ? r) = (lift_match (m1 ? (m2 ? r)))" |
  "lift_match (m ? r) = m ? (lift_match r)" |
  "lift_match (base e) = (base e)" |
  "lift_match (r1 \<then> r2) = (lift_match r1 \<then> lift_match r2)"
  by pat_completeness auto
termination lift_match
  apply (relation "measures [combined_size, size]") apply auto[1]
  apply auto[1] apply auto[1] apply simp
  subgoal for rules x apply (induction rules) apply simp by fastforce
  apply simp subgoal for m2 r apply (cases m2) sorry
        apply simp+
  apply blast
  by auto

fun join_conditions :: "'a::Rewritable Rules \<Rightarrow> 'a Rules option" where
  "join_conditions (m1 ? r1 else m2 ? r2) = 
    (if m1 = m2
      then Some (m1 ? (r1 else r2)) else None)" |
  "join_conditions (m1 ? (m2 ? r1)) = 
    (if m1 = m2
      then Some ((m1 ? r1)) else None)" |
  "join_conditions r = None"

function lift_common :: "'a::Rewritable Rules \<Rightarrow> 'a Rules" where
  "lift_common (r1 else r2) = (
    case join_conditions (r1 else r2) 
    of Some r \<Rightarrow> lift_common r |
       None \<Rightarrow> (lift_common r1 else lift_common r2))" |
  "lift_common (m ? r) = (
    case join_conditions (m ? r) 
    of Some r' \<Rightarrow> lift_common r' |
       None \<Rightarrow> (m ? lift_common r))" |
  "lift_common (choice rules) = choice (List.map lift_common rules)" |
  "lift_common (base e) = base e" |
  "lift_common (r1 \<then> r2) = (lift_common r1 \<then> lift_common r2)"
  using combined_size.cases 
  apply (smt (verit, ccfv_threshold))
  by simp+
termination
  apply (relation "measures [size]") apply auto[1]
    apply simp subgoal for r1 r2 apply (induction r1 rule: join_conditions.induct) by simp+
   apply auto[1] sorry

notation plus (infixl "+" 65)
fun common_size :: "'a::Rewritable Rules \<Rightarrow> nat" where
  "common_size (m ? r) = 1 + common_size r" |
  "common_size (base e) = 0" |
  "common_size (r1 else r2) = 1 + common_size r1 + common_size r2" |
  "common_size (choice (rule # rules)) = 1 + common_size rule + common_size (choice rules)" |
  "common_size (choice []) = 0" |
  "common_size (r1 \<then> r2) = 1 + common_size r1 + common_size r2"
no_notation plus (infixl "+" 65)

fun find_common :: "'a::Rewritable MATCH \<Rightarrow> 'a Rules \<Rightarrow> 'a Rules option" where
  "find_common m (m' ? r) = (if m = m' then Some r else None)" |
  "find_common m r = None"

fun find_uncommon :: "'a::Rewritable MATCH \<Rightarrow> 'a Rules \<Rightarrow> 'a Rules option" where
  "find_uncommon m (m' ? r) = (if m = m' then None else Some (m' ? r))" |
  "find_uncommon m r = Some r"

definition join_common :: "'a::Rewritable MATCH \<Rightarrow> 'a Rules list \<Rightarrow> 'a Rules list" where
  "join_common m rules = List.map_filter (find_common m) rules"

definition join_uncommon :: "'a::Rewritable MATCH \<Rightarrow> 'a Rules list \<Rightarrow> 'a Rules list" where
  "join_uncommon m rules = List.map_filter (find_uncommon m) rules"

function (sequential) combine_conditions :: "'a::Rewritable Rules \<Rightarrow> 'a Rules" where
  "combine_conditions (base e) = base e" |
  "combine_conditions (r1 else r2) = (combine_conditions r1 else combine_conditions r2)" |
  "combine_conditions (m ? r) = (m ? combine_conditions r)" |
  "combine_conditions (choice ((m ? r) # rules)) = 
    choice ((m ? combine_conditions (choice (r # join_common m rules)))
      # [combine_conditions (choice (join_uncommon m rules))])" |
  "combine_conditions (choice rules) = 
    choice (List.map combine_conditions rules)" |
  "combine_conditions (r1 \<then> r2) = (combine_conditions r1 \<then> combine_conditions r2)"
  apply pat_completeness+
  by simp+

termination combine_conditions sorry

fun eliminate_choice :: "'a::Rewritable Rules \<Rightarrow> 'a Rules" where
  "eliminate_choice (base e) = base e" |
  "eliminate_choice (r1 else r2) = (eliminate_choice r1 else eliminate_choice r2)" |
  "eliminate_choice (m ? r) = (m ? eliminate_choice r)" |
  "eliminate_choice (choice (r # [])) = eliminate_choice r" |
  "eliminate_choice (choice rules) = 
    choice (List.map eliminate_choice rules)" |
  "eliminate_choice (r1 \<then> r2) = (eliminate_choice r1 \<then> eliminate_choice r2)"

definition optimized_export where
  "optimized_export = eliminate_choice \<circ> combine_conditions o lift_common o lift_match o eliminate_noop o eliminate_empty"


value "optimized_export
(generate
(Add (Sub (Variable ''x'') (Variable ''y'')) (Variable ''y''))
(Variable ''x'')
(Variable ''y''))"


fun compile :: "'a::Rewritable Strategy \<Rightarrow> 'a Rules" where
  "compile (s1 \<rightarrow> s2) = gen_pattern s1 ''e'' ? base s2"(* |
  "compile (s1 \<rightarrow> s2 where c) = ((gen_pattern s1 ''e'') ? base s2)"*)

value "compile RedundantAdd"
value "compile RedundantSub"
value "compile ShiftConstRight"
value "compile EvalMinus1"
value "compile EvalAdd"

end