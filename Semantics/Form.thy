subsection \<open>Formedness Properties\<close>

theory Form
imports
  Semantics.TreeToGraph
begin

definition wf_start where
  "wf_start g = (0 \<in> ids g \<and>
    is_StartNode (kind g 0))"

definition wf_closed where
  "wf_closed g = 
    (\<forall> n \<in> ids g .
      inputs g n \<subseteq> ids g \<and>
      succ g n \<subseteq> ids g \<and>
      kind g n \<noteq> NoNode)"

definition wf_phis where
  "wf_phis g = 
    (\<forall> n \<in> ids g.
      is_PhiNode (kind g n) \<longrightarrow>
      length (ir_values (kind g n))
       = length (ir_ends 
           (kind g (ir_merge (kind g n)))))"

definition wf_ends where
  "wf_ends g = 
    (\<forall> n \<in> ids g .
      is_AbstractEndNode (kind g n) \<longrightarrow>
      card (usages g n) > 0)"

fun wf_graph :: "IRGraph \<Rightarrow> bool" where
  "wf_graph g = (wf_start g \<and> wf_closed g \<and> wf_phis g \<and> wf_ends g)"

lemmas wf_folds =
  wf_graph.simps
  wf_start_def
  wf_closed_def
  wf_phis_def
  wf_ends_def

fun wf_stamps :: "IRGraph \<Rightarrow> bool" where
  "wf_stamps g = (\<forall> n \<in> ids g . 
    (\<forall> v m p e . (g \<turnstile> n \<simeq> e) \<and> ([m, p] \<turnstile> e \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr e)))"

fun wf_stamp :: "IRGraph \<Rightarrow> (ID \<Rightarrow> Stamp) \<Rightarrow> bool" where
  "wf_stamp g s = (\<forall> n \<in> ids g . 
    (\<forall> v m p e . (g \<turnstile> n \<simeq> e) \<and> ([m, p] \<turnstile> e \<mapsto> v) \<longrightarrow> valid_value v (s n)))"

lemma wf_empty: "wf_graph start_end_graph"
  unfolding wf_folds by (simp add: start_end_graph_def)

lemma wf_eg2_sq: "wf_graph eg2_sq"
  unfolding wf_folds by (simp add: eg2_sq_def)

fun wf_logic_node_inputs :: "IRGraph \<Rightarrow> ID \<Rightarrow> bool" where 
"wf_logic_node_inputs g n =
  (\<forall> inp \<in> set (inputs_of (kind g n)) . (\<forall> v m p . ([g, m, p] \<turnstile> inp \<mapsto> v) \<longrightarrow> wf_bool v))"

fun wf_values :: "IRGraph \<Rightarrow> bool" where
  "wf_values g = (\<forall> n \<in> ids g .
    (\<forall> v m p . ([g, m, p] \<turnstile> n \<mapsto> v) \<longrightarrow> 
       (is_LogicNode (kind g n) \<longrightarrow> 
        wf_bool v \<and> wf_logic_node_inputs g n)))"

end