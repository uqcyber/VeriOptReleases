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
    (let (g', nid') = Predicate.the (unrepE g (ConstantExpr (bool_to_val_width1 val))) in
      replace_node nid (IfNode nid' t f, stamp g nid) g')" |
  "constantCondition cond nid _ g = g"

inductive_cases unrepUnaryE:
  "unrep g (UnaryExpr op e) (g', nid)"
inductive_cases unrepBinaryE:
  "unrep g (BinaryExpr op e1 e2) (g', nid)"
inductive_cases unrepConditionalE:
  "unrep g (ConditionalExpr c t f) (g', nid)"
inductive_cases unrepParamE:
  "unrep g (ParameterExpr i s) (g', nid)"
inductive_cases unrepConstE:
  "unrep g (ConstantExpr c) (g', nid)"
inductive_cases unrepLeafE:
  "unrep g (LeafExpr n s) (g', nid)"
inductive_cases unrepVariableE:
  "unrep g (VariableExpr v s) (g', nid)"
inductive_cases unrepConstVarE:
  "unrep g (ConstantVar c) (g', nid)"

lemma uniqueDet:
  assumes "unique g e (g'\<^sub>1, nid\<^sub>1)"
  assumes "unique g e (g'\<^sub>2, nid\<^sub>2)"
  shows "g'\<^sub>1 = g'\<^sub>2 \<and> nid\<^sub>1 = nid\<^sub>2"
  using assms apply (induction)
   apply (metis Pair_inject assms(1) assms(2) option.distinct(1) option.inject unique.cases)
  by (metis Pair_inject assms(1) assms(2) option.discI option.inject unique.cases)

lemma unrepDet:
  assumes "unrep g e (g'\<^sub>1, nid\<^sub>1)"
  assumes "unrep g e (g'\<^sub>2, nid\<^sub>2)"
  shows "g'\<^sub>1 = g'\<^sub>2 \<and> nid\<^sub>1 = nid\<^sub>2"
  using assms proof (induction e arbitrary: g g'\<^sub>1 nid\<^sub>1 g'\<^sub>2 nid\<^sub>2)
case (UnaryExpr op e)
  then show ?case
    by (smt (verit, best) uniqueDet unrepUnaryE)
next
  case (BinaryExpr x1 e1 e2)
  then show ?case
    by (smt (verit, best) uniqueDet unrepBinaryE)
next
  case (ConditionalExpr e1 e2 e3)
  then show ?case 
   by (smt (verit, best) uniqueDet unrepConditionalE)
next
  case (ParameterExpr x1 x2)
  then show ?case
    by (smt (verit, best) uniqueDet unrepParamE)
next
  case (LeafExpr x1 x2)
  then show ?case 
    by (smt (verit, best) uniqueDet unrepLeafE)
next
  case (ConstantExpr x)
  then show ?case
    by (smt (verit, best) uniqueDet unrepConstE)
next
  case (ConstantVar x)
  then show ?case
    by (smt (verit, best) uniqueDet unrepConstVarE)
next
  case (VariableExpr x1 x2)
  then show ?case
    by (smt (verit, best) uniqueDet unrepVariableE)
qed


lemma unwrapUnrepE:
  assumes "unrep g e (g', nid')"
  shows "(g', nid') = Predicate.the (unrepE g e)"
  using assms unrepEI unrepDet unfolding Predicate.the_def
  by (metis eval_usages.cases pred.sel the_equality unrepE_def)

lemma constantCondition_sem:
  assumes "(unrep g (ConstantExpr (bool_to_val_width1 val)) (g', nid'))"
  shows "constantCondition val nid (IfNode cond t f) g =
    replace_node nid (IfNode nid' t f, stamp g nid) g'"
  using assms unfolding constantCondition.simps
  using unwrapUnrepE by auto

fun wf_insert :: "IRGraph \<Rightarrow> IRExpr \<Rightarrow> bool" where
  "wf_insert g (LeafExpr n s) = is_preevaluated (kind g n)" |
  "wf_insert g (VariableExpr v s) = False" |
  "wf_insert g (ConstantVar v) = False" |
  "wf_insert g _ = True"

(*
lemma
  assumes "wf_insert g e"
  shows "\<exists>g' nid'. unrep g e (g', nid')"
  using assms proof (induction e arbitrary: g)
    case (UnaryExpr op e)
    then obtain g' x where "g \<oplus> e \<leadsto> (g', x)"
      by blast
    then show ?case 
      apply (cases "find_node_and_stamp g' (unary_node op x, stamp_unary op (stamp g' x)) = Some n")
      using UnaryNodeSame apply blast
      by (meson UnaryNodeNew UnaryNodeSame not_Some_eq)
  next
    case (BinaryExpr op e1 e2)
    then obtain g' x where "g \<oplus> e1 \<leadsto> (g', x)"
      by blast
    also obtain g'' y where "g' \<oplus> e2 \<leadsto> (g'', y)"
      using BinaryExpr.IH(2) by force
    then show ?case 
      apply (cases "find_node_and_stamp g'' (bin_node op x y, stamp_binary op (stamp g'' x) (stamp g'' y)) = Some n")
      using BinaryNodeSame calculation apply blast
      by (meson BinaryNodeNew BinaryNodeSame calculation not_Some_eq)
  next
    case (ConditionalExpr e1 e2 e3)
    then obtain g' x where "g \<oplus> e1 \<leadsto> (g', x)"
      by blast
    also obtain g'' y where "g' \<oplus> e2 \<leadsto> (g'', y)"
      using ConditionalExpr.IH(2) by force
    moreover obtain g''' z where "g'' \<oplus> e3 \<leadsto> (g''', z)"
      using ConditionalExpr.IH(3) by force
    ultimately show ?case 
      by (meson option.exhaust_sel unrep.intros(5) unrep.intros(6))
  next
    case (ParameterExpr x1 x2)
    then show ?case
      by (meson option.exhaust_sel unrep.intros(3) unrep.intros(4))
  next
    case (LeafExpr x1 x2)
    then show ?case using assms sledgehammer
  next
    case (ConstantExpr x)
    then show ?case
      by (meson not_Some_eq unrep.intros(1) unrep.intros(2))
  next
    case (ConstantVar x)
    then show ?case sorry
  next
    case (VariableExpr x1 x2)
    then show ?case sledgehammer
  qed
*)

lemma insertConstUnique:
  "\<exists>g' nid'. unique g (ConstantNode c, s) (g', nid')"
  by (meson not_None_eq unique.simps)

lemma insertConst:
  "\<exists>g' nid'. unrep g (ConstantExpr c) (g', nid')"
  using UnrepConstantNode insertConstUnique by blast

lemma constantConditionTrue:
  assumes "kind g ifcond = IfNode cond t f"
  assumes "g' = constantCondition True ifcond (kind g ifcond) g"
  shows "g', p \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
proof -
  have ifn: "\<And> c t f. IfNode c t f \<noteq> NoNode"
    by simp
  obtain g'' nid' where unrep: "unrep g (ConstantExpr (bool_to_val_width1 True)) (g'', nid')"
    using insertConst by blast
  then have "kind g'' nid' = ConstantNode (bool_to_val_width1 True)"
    by (meson ConstUnrepE IRNode.distinct(1077) unique_kind)
  also have "nid' \<noteq> ifcond"
    by (metis ConstUnrepE IRNode.distinct(981) assms(1) calculation fresh_ids ids_some ifn unique.cases unrep unrepDet)
  moreover have "g' = replace_node ifcond (IfNode nid' t f, stamp g ifcond) g''"
    using assms constantCondition_sem unrep by presburger
  moreover have "kind g' nid' = ConstantNode (bool_to_val_width1 True)"
    using assms constantCondition.simps(1) replace_node_unchanged 
    by (metis DiffI calculation(1) calculation(2) calculation(3) emptyE insert_iff unrep unrep_contains)
  moreover have if': "kind g' ifcond = IfNode nid' t f"
    using ifn assms constantCondition.simps(1) replace_node_lookup
    using calculation(3) by blast
  have truedef: "bool_to_val True = (IntVal 32 1)"
    by auto
  from ifn have "ifcond \<noteq> (nextNid g)"
    by (metis assms(1) emptyE ids_some nextNidNotIn)
  moreover have "\<And> c. ConstantNode c \<noteq> NoNode"
    by simp
  ultimately have "kind g' nid' = ConstantNode (bool_to_val_width1 True)"
    using add_changed
    by fastforce
  then have c': "kind g' nid' = ConstantNode (IntVal 1 1)"
    by simp
  have "valid_value (IntVal 1 1) (constantAsStamp (IntVal 1 1))"
    by (metis less_numeral_extra(1) mask_1 neg_one_value new_int_unused_bits_zero rel_simps(25) validDefIntConst)
  then have "[g', m, p] \<turnstile> nid' \<mapsto> IntVal 1 1"
    using Value.distinct(1) \<open>kind g' nid' = ConstantNode (bool_to_val_width1 True)\<close>
    by (metis bool_to_val_width1.simps(1) wf_value_def encodeeval.simps ConstantExpr ConstantNode)
  from if' c' show ?thesis
    by (metis (no_types, opaque_lifting) val_to_bool.simps(1) \<open>[g',m,p] \<turnstile> nid' \<mapsto> IntVal 1 1\<close>
        zero_neq_one IfNode)
qed

lemma constantConditionFalse:
  assumes "kind g ifcond = IfNode cond t f"
  assumes "g' = constantCondition False ifcond (kind g ifcond) g"
  shows "g', p \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
proof -
  have ifn: "\<And> c t f. IfNode c t f \<noteq> NoNode"
    by simp
  obtain g'' nid' where unrep: "unrep g (ConstantExpr (bool_to_val_width1 False)) (g'', nid')"
    using insertConst by blast
  also have "kind g'' nid' = ConstantNode (bool_to_val_width1 False)"
    by (meson ConstUnrepE IRNode.distinct(1077) unique_kind unrep)
  moreover have "nid' \<noteq> ifcond"
    by (metis ConstUnrepE IRNode.distinct(981) assms(1) calculation(2) fresh_ids ids_some ifn unique.cases unrep unrepDet)
  moreover have "g' = replace_node ifcond (IfNode nid' t f, stamp g ifcond) g''"
    using assms(1) assms(2) constantCondition_sem unrep by presburger
  moreover have "kind g' nid' = ConstantNode (bool_to_val_width1 False)"
    using assms constantCondition.simps(1) replace_node_unchanged 
    by (metis DiffI calculation(2) calculation(3) calculation(4) emptyE insert_iff unrep unrep_contains)
  moreover have if': "kind g' ifcond = IfNode nid' t f"
    using ifn assms constantCondition.simps(1) replace_node_lookup
    using calculation(4) by blast
  have falsedef: "bool_to_val False = (IntVal 32 0)"
    by auto
  then have c': "kind g' nid' = ConstantNode (IntVal 1 0)"
    by (simp add: calculation(5))
  have "valid_value (IntVal 1 0) (constantAsStamp (IntVal 1 0))"
    using rel_simps(25) take_bit_of_0 validDefIntConst zero_less_one by blast
  then have "[g', m, p] \<turnstile> nid' \<mapsto> IntVal 1 0"
    by (meson ConstantExpr ConstantNode c' encodeeval.simps wf_value_def)
  from if' c' show ?thesis
    by (meson IfNode \<open>[g'::IRGraph,m::nat \<Rightarrow> Value,p::Value list] \<turnstile> nid'::nat \<mapsto> IntVal (1::nat) (0::64 word)\<close> encodeeval.simps val_to_bool.simps(1))
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

(*lemma constantConditionIfNode:
  assumes "kind g nid = IfNode cond t f"
  shows "constantCondition val nid (kind g nid) g = 
    replace_node nid (IfNode (nextNid g) t f, stamp g nid) 
     (add_node (nextNid g) ((ConstantNode (bool_to_val_width1 val)), constantAsStamp (bool_to_val_width1 val)) g)"
  by (simp add: assms)*)

lemma changeonly_ConstantExpr:
  assumes "unrep g (ConstantExpr c) (g', nid)"
  shows "changeonly {} g g'"
  using assms 
  apply (cases "find_node_and_stamp g (ConstantNode c, constantAsStamp c) = None")
  apply (smt (verit, ccfv_threshold) New add_node_as_set_eq changeonly.simps fresh_ids new_def not_excluded_keep_type order.refl uniqueDet unrepConstE unrep_preserves_contains)
  by (metis changeonly.simps unique.cases unrepConstE unrepDet)


lemma constantCondition_changeonly:
  assumes "nid \<in> ids g"
  assumes "g' = constantCondition b nid (kind g nid) g"
  shows "changeonly {nid} g g'"
proof (cases "is_IfNode (kind g nid)")
  case True
  obtain g'' nid' where unrep: "unrep g (ConstantExpr (bool_to_val_width1 b)) (g'', nid')"
    using insertConst by blast
  also have "changeonly {} g g''"
    using changeonly_ConstantExpr unrep by blast
  moreover have "\<exists>t f ifcond. g' = replace_node nid (IfNode nid' t f, stamp g ifcond) g''"
    using assms constantCondition_sem unrep
    by (metis True is_IfNode_def)
  then show ?thesis
    using assms replace_node_changeonly add_node_changeonly unfolding changeonly.simps
    by (metis calculation(2) changeonly.elims(2) empty_iff)
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
    by (meson IfNode True assms(1,2,3) encodeeval.simps)
  have ifstep': "g', p \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
    using constantConditionTrue True assms(1,4) by presburger
  from ifstep ifstep' show ?thesis
    using StutterStep by blast
next
  case False
  have ifstep: "g, p \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
    by (meson IfNode False assms(1,2,3) encodeeval.simps)
  have ifstep': "g', p \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
    using constantConditionFalse False assms(1,4) by presburger
  from ifstep ifstep' show ?thesis
    using StutterStep by blast
qed

end