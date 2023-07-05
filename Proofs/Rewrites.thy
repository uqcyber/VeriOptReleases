subsection \<open>Graph Rewriting\<close>

theory
  Rewrites
imports
  Stuttering
begin

fun replace_usages :: "ID \<Rightarrow> ID \<Rightarrow> IRGraph \<Rightarrow> IRGraph" where
  "replace_usages nid nid' g = replace_node nid (RefNode nid', stamp g nid') g"

lemma replace_usages_effect:
  assumes "g' = replace_usages nid nid' g"
  shows "kind g' nid = RefNode nid'"
  using replace_usages.simps replace_node_lookup assms by blast

lemma replace_usages_changeonly:
  assumes "nid \<in> ids g"
  assumes "g' = replace_usages nid nid' g"
  shows "changeonly {nid} g g'"
  by (metis add_changed add_node_def replace_node_def replace_usages.simps assms(2))

lemma replace_usages_unchanged:
  assumes "nid \<in> ids g"
  assumes "g' = replace_usages nid nid' g"
  shows "unchanged (ids g - {nid}) g g'"
  using assms disjoint_change replace_usages_changeonly by presburger

fun nextNid :: "IRGraph \<Rightarrow> ID" where
  "nextNid g = (Max (ids g)) + 1"

lemma max_plus_one:
  fixes c :: "ID set"
  shows "\<lbrakk>finite c; c \<noteq> {}\<rbrakk> \<Longrightarrow> (Max c) + 1 \<notin> c"
  by (meson Max_gr_iff less_add_one less_irrefl)

lemma ids_finite:
  "finite (ids g)"
  by simp

lemma nextNidNotIn:
  "ids g \<noteq> {} \<longrightarrow> nextNid g \<notin> ids g"
  unfolding nextNid.simps using ids_finite max_plus_one by blast

fun bool_to_val_width1 :: "bool \<Rightarrow> Value" where
  "bool_to_val_width1 True = (IntVal 1 1)" |
  "bool_to_val_width1 False = (IntVal 1 0)"

fun constantCondition :: "bool \<Rightarrow> ID \<Rightarrow> IRNode \<Rightarrow> IRGraph \<Rightarrow> IRGraph" where
  "constantCondition val nid (IfNode cond t f) g = 
    replace_node nid (IfNode (nextNid g) t f, stamp g nid) 
      (add_node (nextNid g) ((ConstantNode (bool_to_val_width1 val)), constantAsStamp (bool_to_val_width1 val)) g)" |
  "constantCondition cond nid _ g = g"

lemma constantConditionTrue:
  assumes "kind g ifcond = IfNode cond t f"
  assumes "g' = constantCondition True ifcond (kind g ifcond) g"
  shows "g', p \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
proof -
  have ifn: "\<And> c t f. IfNode c t f \<noteq> NoNode"
    by simp
  then have if': "kind g' ifcond = IfNode (nextNid g) t f"
    using assms constantCondition.simps(1) replace_node_lookup by presburger
  have truedef: "bool_to_val True = (IntVal 32 1)"
    by auto
  from ifn have "ifcond \<noteq> (nextNid g)"
    by (metis assms(1) emptyE ids_some nextNidNotIn)
  moreover have "\<And> c. ConstantNode c \<noteq> NoNode"
    by simp
  ultimately have "kind g' (nextNid g) = ConstantNode (bool_to_val_width1 True)"
    using add_changed
    by (smt (z3) find_new_kind replace_node_unchanged singletonD replace_node_def not_in_g assms
        other_node_unchanged constantCondition.simps(1) add_node_def)
  then have c': "kind g' (nextNid g) = ConstantNode (IntVal 1 1)"
    by simp
  have "valid_value (IntVal 1 1) (constantAsStamp (IntVal 1 1))"
    by fastforce
  then have "[g', m, p] \<turnstile> nextNid g \<mapsto> IntVal 1 1"
    using Value.distinct(1) \<open>kind g' (nextNid g) = ConstantNode (bool_to_val_width1 True)\<close>
    by (metis bool_to_val_width1.simps(1) wf_value_def encodeeval_def ConstantExpr ConstantNode)
  from if' c' show ?thesis
    by (metis (no_types, opaque_lifting) val_to_bool.simps(1) \<open>[g',m,p] \<turnstile> nextNid g \<mapsto> IntVal 1 1\<close>
        encodeeval_def zero_neq_one IfNode)
qed

lemma constantConditionFalse:
  assumes "kind g ifcond = IfNode cond t f"
  assumes "g' = constantCondition False ifcond (kind g ifcond) g"
  shows "g', p \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
proof -
  have ifn: "\<And> c t f. IfNode c t f \<noteq> NoNode"
    by simp
  then have if': "kind g' ifcond = IfNode (nextNid g) t f"
    by (metis assms constantCondition.simps(1) replace_node_lookup)
  have falsedef: "bool_to_val False = (IntVal 32 0)"
    by auto
  from ifn have "ifcond \<noteq> (nextNid g)"
    by (metis assms(1) equals0D ids_some nextNidNotIn)
  moreover have "\<And> c. ConstantNode c \<noteq> NoNode"
    by simp
  ultimately have "kind g' (nextNid g) = ConstantNode (bool_to_val_width1 False)"
    by (smt (z3) add_changed add_node_def assms constantCondition.simps(1) find_new_kind not_in_g
        other_node_unchanged replace_node_def singletonD)
  then have c': "kind g' (nextNid g) = ConstantNode (IntVal 1 0)"
    by simp
  have "valid_value (IntVal 1 0) (constantAsStamp (IntVal 1 0))"
    by auto
  then have "[g', m, p] \<turnstile> nextNid g \<mapsto> IntVal 1 0"
    by (meson ConstantExpr ConstantNode c' encodeeval_def wf_value_def)
  from if' c' show ?thesis
    by (metis (no_types, opaque_lifting) val_to_bool.simps(1) \<open>[g',m,p] \<turnstile> nextNid g \<mapsto> IntVal 1 0\<close>
        encodeeval_def IfNode)
qed

lemma diff_forall:
  assumes "\<forall>n\<in>ids g - {nid}. cond n"
  shows "\<forall>n. n \<in> ids g \<and> n \<notin> {nid} \<longrightarrow> cond n"
  by (meson Diff_iff assms)

lemma replace_node_changeonly:
  assumes "g' = replace_node nid node g"
  shows "changeonly {nid} g g'"
  by (metis add_changed add_node_def replace_node_def assms)

lemma add_node_changeonly:
  assumes "g' = add_node nid node g"
  shows "changeonly {nid} g g'"
  by (metis Rep_IRGraph_inverse add_node.rep_eq assms replace_node.rep_eq replace_node_changeonly)

lemma constantConditionNoEffect:
  assumes "\<not>(is_IfNode (kind g nid))"
  shows "g = constantCondition b nid (kind g nid) g"
  using assms constantCondition.simps
  apply (cases "kind g nid")
  prefer 15 prefer 16
   apply (metis is_IfNode_def)
   apply (metis)
  by presburger+

lemma constantConditionIfNode:
  assumes "kind g nid = IfNode cond t f"
  shows "constantCondition val nid (kind g nid) g = 
    replace_node nid (IfNode (nextNid g) t f, stamp g nid) 
     (add_node (nextNid g) ((ConstantNode (bool_to_val_width1 val)), constantAsStamp (bool_to_val_width1 val)) g)"
  by (simp add: assms)

lemma constantCondition_changeonly:
  assumes "nid \<in> ids g"
  assumes "g' = constantCondition b nid (kind g nid) g"
  shows "changeonly {nid} g g'"
proof (cases "is_IfNode (kind g nid)")
  case True
  have "nextNid g \<notin> ids g"
    by (metis emptyE nextNidNotIn)
  then show ?thesis
    using assms replace_node_changeonly add_node_changeonly unfolding changeonly.simps
    by (metis (no_types, lifting) insert_iff is_IfNode_def constantCondition.simps(1) True)
next
  case False
  have "g = g'"
    using constantConditionNoEffect False assms(2) by presburger
  then show ?thesis
    by simp
qed

lemma constantConditionNoIf:
  assumes "\<forall>cond t f. kind g ifcond \<noteq> IfNode cond t f"
  assumes "g' = constantCondition val ifcond (kind g ifcond) g"
  shows "\<exists>nid' .(g m p h \<turnstile> ifcond \<leadsto> nid') \<longleftrightarrow> (g' m p h \<turnstile> ifcond \<leadsto> nid')"
proof -
  have "g' = g"
    using constantConditionNoEffect assms is_IfNode_def by presburger
  then show ?thesis
    by simp
qed

lemma constantConditionValid:
  assumes "kind g ifcond = IfNode cond t f"
  assumes "[g, m, p] \<turnstile> cond \<mapsto> v"
  assumes "const = val_to_bool v"
  assumes "g' = constantCondition const ifcond (kind g ifcond) g"
  shows "\<exists>nid' .(g m p h \<turnstile> ifcond \<leadsto> nid') \<longleftrightarrow> (g' m p h \<turnstile> ifcond \<leadsto> nid')"
proof (cases "const")
  case True
  have ifstep: "g, p \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
    by (meson IfNode True assms(1,2,3) encodeeval_def)
  have ifstep': "g', p \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
    using constantConditionTrue True assms(1,4) by presburger
  from ifstep ifstep' show ?thesis
    using StutterStep by blast
next
  case False
  have ifstep: "g, p \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
    by (meson IfNode False assms(1,2,3) encodeeval_def)
  have ifstep': "g', p \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
    using constantConditionFalse False assms(1,4) by presburger
  from ifstep ifstep' show ?thesis
    using StutterStep by blast
qed

end