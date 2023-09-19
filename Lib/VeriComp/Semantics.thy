section \<open>The Dynamic Representation of a Language\<close>

theory Semantics
  imports Main Behaviour Inf Transfer_Extras begin

text \<open>
The definition of programming languages is separated into two parts: an abstract semantics and a concrete program representation.
\<close>

definition finished :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" where
  "finished r x = (\<nexists>y. r x y)"

lemma finished_star:
  assumes "finished r x"
  shows "r\<^sup>*\<^sup>* x y \<Longrightarrow> x = y"
proof (induction y rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step y z)
  then show ?case
    using assms by (auto simp: finished_def)
qed

locale semantics =
  fixes
    step :: "'state \<Rightarrow> 'state \<Rightarrow> bool" (infix "\<rightarrow>" 50) and
    final :: "'state \<Rightarrow> bool"
  assumes
    final_finished: "final s \<Longrightarrow> finished step s"
begin

text \<open>
The semantics locale represents the semantics as an abstract machine.
It is expressed by a transition system with a transition relation @{term step}---usually written as an infix @{text \<rightarrow>} arrow---and final states @{term final}.
\<close>

lemma finished_step:
  "step s s' \<Longrightarrow> \<not>finished step s"
by (auto simp add: finished_def)

abbreviation eval :: "'state \<Rightarrow> 'state \<Rightarrow> bool" (infix "\<rightarrow>\<^sup>*" 50) where
  "eval \<equiv> step\<^sup>*\<^sup>*"

abbreviation inf_step :: "'state \<Rightarrow> bool" where
  "inf_step \<equiv> inf step"

notation
  inf_step ("'(\<rightarrow>\<^sup>\<infinity>')" [] 50) and
  inf_step ("_ \<rightarrow>\<^sup>\<infinity>" [55] 50)

lemma inf_not_finished: "s \<rightarrow>\<^sup>\<infinity> \<Longrightarrow> \<not> finished step s"
  using inf.cases finished_step by metis

lemma eval_deterministic:
  assumes
    deterministic: "\<And>x y z. step x y \<Longrightarrow> step x z \<Longrightarrow> y = z" and
    "s1 \<rightarrow>\<^sup>* s2" and "s1 \<rightarrow>\<^sup>* s3" and "finished step s2" and "finished step s3"
  shows "s2 = s3"
proof -
  have "right_unique step"
    using deterministic by (auto intro: right_uniqueI)
  with assms show ?thesis
    by (auto simp: finished_def intro: rtranclp_complete_run_right_unique)
qed

lemma step_converges_or_diverges: "(\<exists>s'. s \<rightarrow>\<^sup>* s' \<and> finished step s') \<or> s \<rightarrow>\<^sup>\<infinity>"
  by (smt (verit, del_insts) finished_def inf.coinduct rtranclp.intros(2) rtranclp.rtrancl_refl)

subsection \<open>Behaviour of a dynamic execution\<close>

inductive state_behaves :: "'state \<Rightarrow> 'state behaviour \<Rightarrow> bool" (infix "\<down>" 50) where
  state_terminates:
    "s1 \<rightarrow>\<^sup>* s2 \<Longrightarrow> finished step s2 \<Longrightarrow> final s2 \<Longrightarrow> s1 \<down> (Terminates s2)" |
  state_diverges:
    "s1 \<rightarrow>\<^sup>\<infinity> \<Longrightarrow> s1 \<down> Diverges" |
  state_goes_wrong:
    "s1 \<rightarrow>\<^sup>* s2 \<Longrightarrow> finished step s2 \<Longrightarrow> \<not> final s2 \<Longrightarrow> s1 \<down> (Goes_wrong s2)"


text \<open>
Even though the @{term step} transition relation in the @{locale semantics} locale need not be deterministic, if it happens to be, then the behaviour of a program becomes deterministic too.
\<close>

lemma right_unique_state_behaves:
  assumes
    "right_unique (\<rightarrow>)"
  shows "right_unique (\<down>)"
proof (rule right_uniqueI)
  fix s b1 b2
  assume "s \<down> b1" "s \<down> b2"
  thus "b1 = b2"
    by (auto simp: finished_def simp del: not_ex
        elim!: state_behaves.cases
        dest: rtranclp_complete_run_right_unique[OF \<open>right_unique (\<rightarrow>)\<close>, of s]
        dest: final_finished star_inf[OF \<open>right_unique (\<rightarrow>)\<close>, THEN inf_not_finished])
qed

lemma left_total_state_behaves: "left_total (\<down>)"
proof (rule left_totalI)
  fix s
  show "\<exists>b. s \<down> b"
    using step_converges_or_diverges[of s]
  proof (elim disjE exE conjE)
    fix s'
    assume "s \<rightarrow>\<^sup>* s'" and "finished (\<rightarrow>) s'"
    thus "\<exists>b. s \<down> b"
      by (cases "final s'") (auto intro: state_terminates state_goes_wrong)
  next
    assume "s \<rightarrow>\<^sup>\<infinity>"
    thus "\<exists>b. s \<down> b"
      by (auto intro: state_diverges)
  qed
qed

subsection \<open>Safe states\<close>

definition safe where
  "safe s \<longleftrightarrow> (\<forall>s'. step\<^sup>*\<^sup>* s s' \<longrightarrow> final s' \<or> (\<exists>s''. step s' s''))"

lemma final_safeI: "final s \<Longrightarrow> safe s"
  by (metis final_finished finished_star safe_def)

lemma step_safe: "step s s' \<Longrightarrow> safe s \<Longrightarrow> safe s'"
  by (simp add: converse_rtranclp_into_rtranclp safe_def)

lemma steps_safe: "step\<^sup>*\<^sup>* s s' \<Longrightarrow> safe s \<Longrightarrow> safe s'"
  by (meson rtranclp_trans safe_def)

lemma safe_state_behaves_not_wrong:
  assumes "safe s" and "s \<down> b"
  shows "\<not> is_wrong b"
  using \<open>s \<down> b\<close>
proof (cases rule: state_behaves.cases)
  case (state_goes_wrong s2)
  then show ?thesis
    using \<open>safe s\<close> by (auto simp: safe_def finished_def)
qed simp_all

end

end