theory Rewritable
  imports Main "HOL-Library.Finite_Map" Locale_Code.Locale_Code
begin

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

  assumes "a' \<subseteq>\<^sub>m a \<Longrightarrow> is_ground_condition (ground_condition c a') \<Longrightarrow> ground_condition c a' = ground_condition c a"
  assumes shrinks: "\<forall>e' \<in> set (subexprs e). size e > size e'"
  assumes "map f (subexprs e) = subexprs (snd (chain (\<lambda>e a. (plus a 1, f e)) e 0))"
  assumes "length (subexprs e) = fst (chain (\<lambda>e a. (plus a 1, f e)) e 0)"
  assumes "eval_condition c = None \<equiv> \<not>(is_ground_condition c)"


end