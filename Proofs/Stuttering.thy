subsection \<open>Stuttering\<close>

theory Stuttering
  imports
    Semantics.IRStepThms
begin

inductive stutter:: "IRGraph \<Rightarrow> MapState \<Rightarrow> Params \<Rightarrow> FieldRefHeap \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> bool" ("_ _ _ _ \<turnstile> _ \<leadsto> _" 55)
  for g m p h where

  StutterStep:
  "\<lbrakk>g, p \<turnstile> (nid,m,h) \<rightarrow> (nid',m,h)\<rbrakk>
   \<Longrightarrow> g m p h \<turnstile> nid \<leadsto> nid'" |

  Transitive:
  "\<lbrakk>g, p \<turnstile> (nid,m,h) \<rightarrow> (nid'',m,h);
    g m p h \<turnstile> nid'' \<leadsto> nid'\<rbrakk>
   \<Longrightarrow> g m p h \<turnstile> nid \<leadsto> nid'"

lemma stuttering_successor:
  assumes "(g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h))"
  shows "{P'. (g m p h \<turnstile> nid \<leadsto> P')} = {nid'} \<union> {nid''. (g m p h \<turnstile> nid' \<leadsto> nid'')}"
proof -
  have nextin: "nid' \<in> {P'. (g m p h \<turnstile> nid \<leadsto> P')}"
    using assms StutterStep by fast
  have nextsubset: "{nid''. (g m p h \<turnstile> nid' \<leadsto> nid'')} \<subseteq> {P'. (g m p h \<turnstile> nid \<leadsto> P')}"
    by (metis Collect_mono assms stutter.Transitive)
  have "\<forall>n \<in> {P'. (g m p h \<turnstile> nid \<leadsto> P')} . n = nid' \<or> n \<in> {nid''. (g m p h \<turnstile> nid' \<leadsto> nid'')}"
    by (metis (no_types, lifting) Pair_inject assms mem_Collect_eq stutter.simps stepDet)
  then show ?thesis
    using nextin nextsubset by (auto simp add: mk_disjoint_insert)
qed

end