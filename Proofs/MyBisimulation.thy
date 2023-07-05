section \<open>Proof Infrastructure\<close>
subsection \<open>Bisimulation\<close>

theory MyBisimulation
imports
  Stuttering
begin

(* WIP strong bisimilar
fun strongly_bisimilar :: "
(IRGraph \<times> ID \<times> MapState \<times> FieldRefHeap) rel
\<Rightarrow> (IRGraph \<times> ID \<times> MapState \<times> FieldRefHeap)
\<Rightarrow> (IRGraph \<times> ID \<times> MapState \<times> FieldRefHeap)
\<Rightarrow> bool"
  where
  "strongly_bisimilar \<R> (g1, nid1, m1, h1) (g2, nid2, m2, h2) =
    ((((g1, nid1, m1, h1), (g2, nid2, m2, h2)) \<in> \<R>) \<longrightarrow>
    ((\<forall>P'. (g1 \<turnstile> (nid1, m1, h1) \<rightarrow> P') \<longrightarrow> (\<exists>Q' . (g2 \<turnstile> (nid2, m2, h2) \<rightarrow> Q') \<and> ((g1,P'), (g2,Q')) \<in> \<R>)) \<and>
    (\<forall>Q'. (g2 \<turnstile> (nid2, m2, h2) \<rightarrow> Q') \<longrightarrow> (\<exists>P' . (g1 \<turnstile> (nid1, m1, h1) \<rightarrow> P') \<and> ((g1,P'), (g2,Q')) \<in> \<R>))))"
*)

inductive weak_bisimilar :: "ID \<Rightarrow> IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool"
  ("_ . _ \<sim> _") for nid where
  "\<lbrakk>\<forall>P'. (g m p h \<turnstile> nid \<leadsto> P') \<longrightarrow> (\<exists>Q' . (g' m p h \<turnstile> nid \<leadsto> Q') \<and> P' = Q');
    \<forall>Q'. (g' m p h \<turnstile> nid \<leadsto> Q') \<longrightarrow> (\<exists>P' . (g m p h \<turnstile> nid \<leadsto> P') \<and> P' = Q')\<rbrakk>
  \<Longrightarrow> nid . g \<sim> g'"

text \<open>A strong bisimilution between no-op transitions\<close>
inductive strong_noop_bisimilar :: "ID \<Rightarrow> MapState \<Rightarrow> FieldRefHeap \<Rightarrow> IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool"
  ("_ _ _ | _ \<sim> _") for nid where
  "\<lbrakk>\<forall>P'. (g, p \<turnstile> (nid, m, h) \<rightarrow> P') \<longrightarrow> (\<exists>Q' . (g', p \<turnstile> (nid, m, h) \<rightarrow> Q') \<and> P' = Q');
    \<forall>Q'. (g', p \<turnstile> (nid, m, h) \<rightarrow> Q') \<longrightarrow> (\<exists>P' . (g, p \<turnstile> (nid, m, h) \<rightarrow> P') \<and> P' = Q')\<rbrakk>
  \<Longrightarrow> nid m h | g \<sim> g'"

lemma lockstep_strong_bisimilulation:
  assumes "g' = replace_node nid node g"
  assumes "g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h)"
  assumes "g', p \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h)"
  shows "nid m h | g \<sim> g'"
  by (metis strong_noop_bisimilar.simps stepDet assms(2,3))

lemma no_step_bisimulation:
  assumes "\<forall>m p h nid' m' h'. \<not>(g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h'))"
  assumes "\<forall>m p h nid' m' h'. \<not>(g', p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h'))"
  shows "nid m h | g \<sim> g'"
  by (simp add: assms(1,2) strong_noop_bisimilar.intros)

end