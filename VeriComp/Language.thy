section \<open>The Static Representation of a Language\<close>

theory Language
  imports Semantics
begin

locale language =
  semantics step final
  for
    step :: "'state \<Rightarrow> 'state \<Rightarrow> bool" and
    final :: "'state \<Rightarrow> bool" +
  fixes
    load :: "'prog \<Rightarrow> 'state \<Rightarrow> bool"

context language begin

text \<open>
The language locale represents the concrete program representation (type variable @{typ 'prog}), which can be transformed into a program state (type variable @{typ 'state}) by the @{term load } function.
The set of initial states of the transition system is implicitly defined by the codomain of @{term load}.
\<close>


subsection \<open>Program behaviour\<close>

definition prog_behaves :: "'prog \<Rightarrow> 'state behaviour \<Rightarrow> bool" (infix "\<Down>" 50) where
  "prog_behaves = load OO state_behaves"

text \<open>If both the @{term load} and @{term step} relations are deterministic, then so is the behaviour of a program.\<close>

lemma right_unique_prog_behaves:
  assumes
    right_unique_load: "right_unique load" and
    right_unique_step: "right_unique step"
  shows "right_unique prog_behaves"
  unfolding prog_behaves_def
  using right_unique_state_behaves[OF right_unique_step] right_unique_load
  by (auto intro: right_unique_OO)

end

end