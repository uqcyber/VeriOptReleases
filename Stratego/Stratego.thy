section "Stratego"
theory Stratego
  imports Rewritable
begin

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

context Rewritable begin

abbreviation "wheref" :: "('a, 'b, 'c) Strategy \<Rightarrow> ('a, 'b, 'c) Strategy" where
  "wheref x \<equiv> var ''_''?; x; var ''_''!"

abbreviation conditional_rewrite_to :: "'a \<Rightarrow> 'a \<Rightarrow> ('a, 'b, 'c) Strategy \<Rightarrow> ('a, 'b, 'c) Strategy"
  ("_ \<rightarrow> _ where _") where 
  "s1 \<rightarrow> s2 where s3 \<equiv> s1?; wheref s3; s2!"

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

notation plus (infixl "+" 65)
notation less ("(_/ < _)"  [51, 51] 50)

end