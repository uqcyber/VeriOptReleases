theory Transfer_Extras
  imports Main
begin

lemma rtranclp_complete_run_right_unique:
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and x y z :: 'a
  assumes "right_unique R"
  shows "R\<^sup>*\<^sup>* x y \<Longrightarrow> (\<nexists>w. R y w) \<Longrightarrow> R\<^sup>*\<^sup>* x z \<Longrightarrow> (\<nexists>w. R z w) \<Longrightarrow> y = z"
proof (induction x arbitrary: z rule: converse_rtranclp_induct)
  case base
  then show ?case
    by (auto elim: converse_rtranclpE)
next
  case (step x w)
  hence "R\<^sup>*\<^sup>* w z"
    using right_uniqueD[OF \<open>right_unique R\<close>]
    by (metis converse_rtranclpE)
  with step show ?case
    by simp
qed

lemma tranclp_complete_run_right_unique:
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and x y z :: 'a
  assumes "right_unique R"
  shows "R\<^sup>+\<^sup>+ x y \<Longrightarrow> (\<nexists>w. R y w) \<Longrightarrow> R\<^sup>+\<^sup>+ x z \<Longrightarrow> (\<nexists>w. R z w) \<Longrightarrow> y = z"
  using right_uniqueD[OF \<open>right_unique R\<close>, of x]
  by (auto dest!: tranclpD intro!: rtranclp_complete_run_right_unique[OF \<open>right_unique R\<close>, of _ y z])

end