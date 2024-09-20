subsection \<open>Dynamic Frames\<close>

text \<open>
This theory defines two operators, 'unchanged' and 'changeonly',
that are useful for specifying which nodes in an IRGraph can change.
The dynamic framing idea originates from 'Dynamic Frames' in software verification,
started by Ioannis T. Kassios in "Dynamic frames: Support for framing, 
dependencies and sharing without restrictions", In FM 2006.
\<close>

theory IRGraphFrames
  imports
    Form
begin

fun unchanged :: "ID set \<Rightarrow> IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool" where
  "unchanged ns g1 g2 = (\<forall> n . n \<in> ns \<longrightarrow> 
    (n \<in> ids g1 \<and> n \<in> ids g2 \<and> kind g1 n = kind g2 n \<and> stamp g1 n = stamp g2 n))"

(* This allows new nodes to be added to g2, but only ns can change. *)
fun changeonly :: "ID set \<Rightarrow> IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool" where
  "changeonly ns g1 g2 = (\<forall> n . n \<in> ids g1 \<and> n \<notin> ns \<longrightarrow> 
    (n \<in> ids g1 \<and> n \<in> ids g2 \<and> kind g1 n = kind g2 n \<and> stamp g1 n = stamp g2 n))"

lemma node_unchanged:
  assumes "unchanged ns g1 g2"
  assumes "nid \<in> ns"
  shows "kind g1 nid = kind g2 nid"
  using assms by simp

lemma other_node_unchanged:
  assumes "changeonly ns g1 g2"
  assumes "nid \<in> ids g1"
  assumes "nid \<notin> ns"
  shows "kind g1 nid = kind g2 nid"
  using assms by simp

text \<open>Some notation for input nodes used\<close>

(* Relates all the nodes used in an 'eval', including the node itself. *)
inductive eval_uses:: "IRGraph \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> bool"
  for g where

  use0: "nid \<in> ids g
    \<Longrightarrow> eval_uses g nid nid" |

  use_inp: "nid' \<in> inputs g n
    \<Longrightarrow> eval_uses g nid nid'" |

  use_trans: "\<lbrakk>eval_uses g nid nid';
    eval_uses g nid' nid''\<rbrakk>
    \<Longrightarrow> eval_uses g nid nid''"

fun eval_usages :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID set" where
  "eval_usages g nid = {n \<in> ids g . eval_uses g nid n}"

lemma eval_usages_self:
  assumes "nid \<in> ids g"
  shows "nid \<in> eval_usages g nid"
  using assms by (simp add: ids.rep_eq eval_uses.intros(1))

lemma not_in_g_inputs: 
  assumes "nid \<notin> ids g"
  shows "inputs g nid = {}"
proof -
  have k: "kind g nid = NoNode" 
    using assms by (simp add: not_in_g)
  then show ?thesis 
    by (simp add: k)
qed

lemma child_member:
  assumes "n = kind g nid"
  assumes "n \<noteq> NoNode"
  assumes "List.member (inputs_of n) child"
  shows "child \<in> inputs g nid"  
  by (metis in_set_member inputs.simps assms(1,3))

lemma child_member_in:
  assumes "nid \<in> ids g"
  assumes "List.member (inputs_of (kind g nid)) child"
  shows "child \<in> inputs g nid"
  by (metis child_member ids_some assms)

(* Node inputs are not necessarily in ids g (unless wf_graph g).
   But this is true because 'inp' is defined using 'kind'. *)
lemma inp_in_g: 
  assumes "n \<in> inputs g nid"
  shows "nid \<in> ids g"
proof -
  have "inputs g nid \<noteq> {}"
    by (metis empty_iff empty_set assms)
  then have "kind g nid \<noteq> NoNode"
    by (metis not_in_g_inputs ids_some)
  then show ?thesis
    by (metis not_in_g)
qed

lemma inp_in_g_wf:
  assumes "wf_graph g"
  assumes "n \<in> inputs g nid"
  shows "n \<in> ids g"
  using assms wf_folds inp_in_g by blast

lemma kind_unchanged:
  assumes "nid \<in> ids g1"
  assumes "unchanged (eval_usages g1 nid) g1 g2"
  shows "kind g1 nid = kind g2 nid"
proof -
  show ?thesis
    using assms eval_usages_self by simp
qed

lemma stamp_unchanged:
  assumes "nid \<in> ids g1"
  assumes "unchanged (eval_usages g1 nid) g1 g2"
  shows "stamp g1 nid = stamp g2 nid"
  by (meson assms eval_usages_self unchanged.elims(2))
  
lemma child_unchanged:
  assumes "child \<in> inputs g1 nid"
  assumes "unchanged (eval_usages g1 nid) g1 g2"
  shows "unchanged (eval_usages g1 child) g1 g2"
  by (smt assms eval_usages.simps mem_Collect_eq unchanged.simps use_inp use_trans)

lemma eval_usages:
  assumes "us = eval_usages g nid"
  assumes "nid' \<in> ids g"
  shows "eval_uses g nid nid' \<longleftrightarrow> nid' \<in> us" (is "?P \<longleftrightarrow> ?Q")
  using assms by (simp add: ids.rep_eq)

lemma inputs_are_uses:
  assumes "nid' \<in> inputs g nid"
  shows "eval_uses g nid nid'"
  by (metis assms use_inp)

lemma inputs_are_usages:
  assumes "nid' \<in> inputs g nid"
  assumes "nid' \<in> ids g"
  shows "nid' \<in> eval_usages g nid"
  using assms by (simp add: inputs_are_uses)

lemma inputs_of_are_usages:
  assumes "List.member (inputs_of (kind g nid)) nid'"
  assumes "nid' \<in> ids g"
  shows "nid' \<in> eval_usages g nid"
  by (metis assms in_set_member inputs.elims inputs_are_usages)

lemma usage_includes_inputs:
  assumes "us = eval_usages g nid"
  assumes "ls = inputs g nid"
  assumes "ls \<subseteq> ids g"
  shows "ls \<subseteq> us"
  using inputs_are_usages assms by blast

lemma elim_inp_set:
  assumes "k = kind g nid"
  assumes "k \<noteq> NoNode"
  assumes "child \<in> set (inputs_of k)"
  shows "child \<in> inputs g nid"
  using assms by simp

lemma encode_in_ids:
  assumes "g \<turnstile> nid \<simeq> e"
  shows "nid \<in> ids g"
  using assms apply (induction rule: rep.induct) by fastforce+

lemma eval_in_ids:
  assumes "[g, m, p] \<turnstile> nid \<mapsto> v"
  shows "nid \<in> ids g"
  using assms encode_in_ids by (auto simp add: encodeeval.simps)

lemma transitive_kind_same:
  assumes "unchanged (eval_usages g1 nid) g1 g2"
  shows "\<forall> nid' \<in> (eval_usages g1 nid) . kind g1 nid' = kind g2 nid'"
  by (meson unchanged.elims(1) assms)

theorem stay_same_encoding:
  assumes nc: "unchanged (eval_usages g1 nid) g1 g2"
  assumes g1: "g1 \<turnstile> nid \<simeq> e"
  assumes wf: "wf_graph g1"
  shows "g2 \<turnstile> nid \<simeq> e"
proof -
  have dom: "nid \<in> ids g1"
    using g1 encode_in_ids by simp
  show ?thesis 
    using g1 nc wf dom 
  proof (induction e rule: rep.induct)
  case (ConstantNode n c)
  then have "kind g2 n = ConstantNode c"
    by (metis kind_unchanged)
  then show ?case 
    using rep.ConstantNode by presburger
next
  case (ParameterNode n i s)
  then have "kind g2 n = ParameterNode i"
    by (metis kind_unchanged)
  then show ?case
    by (metis ParameterNode.hyps(2) ParameterNode.prems(1,3) rep.ParameterNode stamp_unchanged)
next
  case (ConditionalNode n c t f ce te fe)
  then have "kind g2 n = ConditionalNode c t f"
    by (metis kind_unchanged)
  have "c \<in> eval_usages g1 n \<and> t \<in> eval_usages g1 n \<and> f \<in> eval_usages g1 n"
    by (metis inputs_of_ConditionalNode ConditionalNode.hyps(1,2,3,4) encode_in_ids inputs.simps 
        inputs_are_usages list.set_intros(1) set_subset_Cons subset_code(1))
  then show ?case 
    by (metis ConditionalNode.hyps(1) ConditionalNode.prems(1) IRNodes.inputs_of_ConditionalNode 
        \<open>kind g2 n = ConditionalNode c t f\<close> child_unchanged inputs.simps list.set_intros(1) 
        local.ConditionalNode(5,6,7,9) rep.ConditionalNode set_subset_Cons subset_code(1) 
        unchanged.elims(2))
next
  case (AbsNode n x xe)
  then have "kind g2 n = AbsNode x"
    by (metis kind_unchanged)
  then have "x \<in> eval_usages g1 n"
    by (metis inputs_of_AbsNode AbsNode.hyps(1,2) encode_in_ids inputs.simps inputs_are_usages 
        list.set_intros(1))
  then show ?case
    by (metis AbsNode.IH AbsNode.hyps(1) AbsNode.prems(1,3) IRNodes.inputs_of_AbsNode rep.AbsNode 
        \<open>kind g2 n = AbsNode x\<close> child_member_in child_unchanged local.wf member_rec(1) 
        unchanged.simps)
next
  case (ReverseBytesNode n x xe)
  then have "kind g2 n = ReverseBytesNode x"
    by (metis kind_unchanged)
  then have "x \<in> eval_usages g1 n"
    by (metis IRNodes.inputs_of_ReverseBytesNode ReverseBytesNode.hyps(1,2) encode_in_ids
        inputs.simps inputs_are_usages list.set_intros(1))
  then show ?case
    by (metis IRNodes.inputs_of_ReverseBytesNode ReverseBytesNode.IH ReverseBytesNode.hyps(1,2)
        ReverseBytesNode.prems(1) child_member_in child_unchanged local.wf member_rec(1)
        \<open>kind g2 n = ReverseBytesNode x\<close> encode_in_ids rep.ReverseBytesNode)
next
  case (BitCountNode n x xe)
  then have "kind g2 n = BitCountNode x"
    by (metis kind_unchanged)
  then have "x \<in> eval_usages g1 n"
    by (metis BitCountNode.hyps(1,2) IRNodes.inputs_of_BitCountNode encode_in_ids inputs.simps
        inputs_are_usages list.set_intros(1))
  then show ?case
    by (metis BitCountNode.IH BitCountNode.hyps(1,2) BitCountNode.prems(1) member_rec(1) local.wf
        IRNodes.inputs_of_BitCountNode \<open>kind g2 n = BitCountNode x\<close> encode_in_ids rep.BitCountNode
        child_member_in child_unchanged)
next
  case (NotNode n x xe)
  then have "kind g2 n = NotNode x"
    by (metis kind_unchanged)
  then have "x \<in> eval_usages g1 n"
    by (metis inputs_of_NotNode NotNode.hyps(1,2) encode_in_ids inputs.simps inputs_are_usages 
        list.set_intros(1))
  then show ?case
    by (metis NotNode.IH NotNode.hyps(1) NotNode.prems(1,3) IRNodes.inputs_of_NotNode rep.NotNode
        \<open>kind g2 n = NotNode x\<close> child_member_in child_unchanged local.wf member_rec(1) 
        unchanged.simps)
next
  case (NegateNode n x xe)
  then have "kind g2 n = NegateNode x"
    by (metis kind_unchanged)
  then have "x \<in> eval_usages g1 n"
    by (metis inputs_of_NegateNode NegateNode.hyps(1,2) encode_in_ids inputs.simps inputs_are_usages 
        list.set_intros(1))
  then show ?case
    by (metis IRNodes.inputs_of_NegateNode NegateNode.IH NegateNode.hyps(1) NegateNode.prems(1,3)  
        \<open>kind g2 n = NegateNode x\<close> child_member_in child_unchanged local.wf member_rec(1) 
        rep.NegateNode unchanged.elims(1))
next
  case (LogicNegationNode n x xe)
  then have "kind g2 n = LogicNegationNode x"
    by (metis kind_unchanged)
  then have "x \<in> eval_usages g1 n"
    by (metis inputs_of_LogicNegationNode inputs_of_are_usages LogicNegationNode.hyps(1,2) 
        encode_in_ids member_rec(1))
  then show ?case
    by (metis IRNodes.inputs_of_LogicNegationNode LogicNegationNode.IH LogicNegationNode.hyps(1,2)  
        LogicNegationNode.prems(1) \<open>kind g2 n = LogicNegationNode x\<close> child_unchanged encode_in_ids 
        inputs.simps list.set_intros(1) local.wf rep.LogicNegationNode)
next
  case (AddNode n x y xe ye)
  then have "kind g2 n = AddNode x y"
    by (metis kind_unchanged)
  then have "x \<in> eval_usages g1 n \<and> y \<in> eval_usages g1 n"
    by (metis AddNode.hyps(1,2,3) IRNodes.inputs_of_AddNode encode_in_ids in_mono inputs.simps 
        inputs_are_usages list.set_intros(1) set_subset_Cons)
  then show ?case
    by (metis AddNode.IH(1,2) AddNode.hyps(1,2,3) AddNode.prems(1) IRNodes.inputs_of_AddNode 
        \<open>kind g2 n = AddNode x y\<close> child_unchanged encode_in_ids in_set_member inputs.simps 
        local.wf member_rec(1) rep.AddNode)
next
  case (MulNode n x y xe ye)
  then have "kind g2 n = MulNode x y"
    by (metis kind_unchanged)
  then have "x \<in> eval_usages g1 n \<and> y \<in> eval_usages g1 n"
    by (metis MulNode.hyps(1,2,3) IRNodes.inputs_of_MulNode encode_in_ids in_mono inputs.simps 
        inputs_are_usages list.set_intros(1) set_subset_Cons)
  then show ?case 
    by (metis \<open>kind g2 n = MulNode x y\<close> child_unchanged inputs.simps list.set_intros(1) rep.MulNode 
        set_subset_Cons subset_iff unchanged.elims(2) inputs_of_MulNode MulNode(1,4,5,6,7))
next
  case (DivNode n x y xe ye)
  then have "kind g2 n = SignedFloatingIntegerDivNode x y"
    by (metis kind_unchanged)
  then have "x \<in> eval_usages g1 n \<and> y \<in> eval_usages g1 n"
    by (metis DivNode.hyps(1,2,3) IRNodes.inputs_of_SignedFloatingIntegerDivNode encode_in_ids in_mono inputs.simps 
        inputs_are_usages list.set_intros(1) set_subset_Cons)
  then show ?case 
    by (metis \<open>kind g2 n = SignedFloatingIntegerDivNode x y\<close> child_unchanged inputs.simps list.set_intros(1) rep.DivNode 
        set_subset_Cons subset_iff unchanged.elims(2) inputs_of_SignedFloatingIntegerDivNode DivNode(1,4,5,6,7))
next
  case (ModNode n x y xe ye)
  then have "kind g2 n = SignedFloatingIntegerRemNode x y"
    by (metis kind_unchanged)
  then have "x \<in> eval_usages g1 n \<and> y \<in> eval_usages g1 n"
    by (metis ModNode.hyps(1,2,3) IRNodes.inputs_of_SignedFloatingIntegerRemNode encode_in_ids in_mono inputs.simps 
        inputs_are_usages list.set_intros(1) set_subset_Cons)
  then show ?case 
    by (metis \<open>kind g2 n = SignedFloatingIntegerRemNode x y\<close> child_unchanged inputs.simps list.set_intros(1) rep.ModNode 
        set_subset_Cons subset_iff unchanged.elims(2) inputs_of_SignedFloatingIntegerRemNode ModNode(1,4,5,6,7))
next
  case (SubNode n x y xe ye)
  then have "kind g2 n = SubNode x y"
    by (metis kind_unchanged)
  then have "x \<in> eval_usages g1 n \<and> y \<in> eval_usages g1 n"
    by (metis SubNode.hyps(1,2,3) IRNodes.inputs_of_SubNode encode_in_ids in_mono inputs.simps 
        inputs_are_usages list.set_intros(1) set_subset_Cons)
  then show ?case
    by (metis \<open>kind g2 n = SubNode x y\<close> child_member child_unchanged encode_in_ids ids_some SubNode
        member_rec(1) rep.SubNode inputs_of_SubNode)
next
  case (AndNode n x y xe ye)
  then have "kind g2 n = AndNode x y"
    by (metis kind_unchanged)
  then have "x \<in> eval_usages g1 n \<and> y \<in> eval_usages g1 n"
    by (metis AndNode.hyps(1,2,3) IRNodes.inputs_of_AndNode encode_in_ids in_mono inputs.simps 
        inputs_are_usages list.set_intros(1) set_subset_Cons)
  then show ?case 
    by (metis AndNode(1,4,5,6,7) inputs_of_AndNode \<open>kind g2 n = AndNode x y\<close> child_unchanged 
        inputs.simps list.set_intros(1) rep.AndNode set_subset_Cons subset_iff unchanged.elims(2))
next
  case (OrNode n x y xe ye)
  then have "kind g2 n = OrNode x y"
    by (metis kind_unchanged)
  then have "x \<in> eval_usages g1 n \<and> y \<in> eval_usages g1 n"
    by (metis OrNode.hyps(1,2,3) IRNodes.inputs_of_OrNode encode_in_ids in_mono inputs.simps 
        inputs_are_usages list.set_intros(1) set_subset_Cons)
  then show ?case 
    by (metis inputs_of_OrNode \<open>kind g2 n = OrNode x y\<close> child_unchanged encode_in_ids rep.OrNode
        child_member ids_some member_rec(1) OrNode)
next
  case (XorNode n x y xe ye)
  then have "kind g2 n = XorNode x y"
    by (metis kind_unchanged)
  then have "x \<in> eval_usages g1 n \<and> y \<in> eval_usages g1 n"
    by (metis XorNode.hyps(1,2,3) IRNodes.inputs_of_XorNode encode_in_ids in_mono inputs.simps 
        inputs_are_usages list.set_intros(1) set_subset_Cons)
  then show ?case 
    by (metis inputs_of_XorNode \<open>kind g2 n = XorNode x y\<close> child_member child_unchanged rep.XorNode
        encode_in_ids ids_some member_rec(1) XorNode)
next
  case (ShortCircuitOrNode n x y xe ye)
  then have "kind g2 n = ShortCircuitOrNode x y"
    by (metis kind_unchanged)
  then have "x \<in> eval_usages g1 n \<and> y \<in> eval_usages g1 n"
    by (metis ShortCircuitOrNode.hyps(1,2,3) IRNodes.inputs_of_ShortCircuitOrNode inputs_are_usages
        in_mono inputs.simps list.set_intros(1) set_subset_Cons encode_in_ids)
  then show ?case 
    by (metis ShortCircuitOrNode inputs_of_ShortCircuitOrNode \<open>kind g2 n = ShortCircuitOrNode x y\<close> 
        child_member child_unchanged encode_in_ids ids_some member_rec(1) rep.ShortCircuitOrNode)
next
case (LeftShiftNode n x y xe ye)
  then have "kind g2 n = LeftShiftNode x y"
    by (metis kind_unchanged)
  then have "x \<in> eval_usages g1 n \<and> y \<in> eval_usages g1 n"
    by (metis LeftShiftNode.hyps(1,2,3) IRNodes.inputs_of_LeftShiftNode encode_in_ids inputs.simps
        inputs_are_usages list.set_intros(1) set_subset_Cons in_mono)
  then show ?case  
    by (metis LeftShiftNode inputs_of_LeftShiftNode \<open>kind g2 n = LeftShiftNode x y\<close> child_unchanged
        encode_in_ids ids_some member_rec(1) rep.LeftShiftNode child_member)
next
case (RightShiftNode n x y xe ye)
  then have "kind g2 n = RightShiftNode x y"
    by (metis kind_unchanged)
  then have "x \<in> eval_usages g1 n \<and> y \<in> eval_usages g1 n"
    by (metis RightShiftNode.hyps(1,2,3) IRNodes.inputs_of_RightShiftNode encode_in_ids inputs.simps
        inputs_are_usages list.set_intros(1) set_subset_Cons in_mono)
  then show ?case 
    by (metis RightShiftNode inputs_of_RightShiftNode \<open>kind g2 n = RightShiftNode x y\<close> child_member 
        child_unchanged encode_in_ids ids_some member_rec(1) rep.RightShiftNode)
next
case (UnsignedRightShiftNode n x y xe ye)
  then have "kind g2 n = UnsignedRightShiftNode x y"
    by (metis kind_unchanged)
  then have "x \<in> eval_usages g1 n \<and> y \<in> eval_usages g1 n"
    by (metis UnsignedRightShiftNode.hyps(1,2,3) IRNodes.inputs_of_UnsignedRightShiftNode in_mono
        encode_in_ids inputs.simps inputs_are_usages list.set_intros(1) set_subset_Cons)
  then show ?case  
    by (metis UnsignedRightShiftNode inputs_of_UnsignedRightShiftNode child_member child_unchanged
        \<open>kind g2 n = UnsignedRightShiftNode x y\<close> encode_in_ids ids_some rep.UnsignedRightShiftNode
        member_rec(1))
next
  case (IntegerBelowNode n x y xe ye)
  then have "kind g2 n = IntegerBelowNode x y"
    by (metis kind_unchanged)
  then have "x \<in> eval_usages g1 n \<and> y \<in> eval_usages g1 n"
    by (metis IntegerBelowNode.hyps(1,2,3) IRNodes.inputs_of_IntegerBelowNode encode_in_ids in_mono 
        inputs.simps inputs_are_usages list.set_intros(1) set_subset_Cons)
  then show ?case 
    by (metis inputs_of_IntegerBelowNode \<open>kind g2 n = IntegerBelowNode x y\<close> rep.IntegerBelowNode
        child_member child_unchanged encode_in_ids ids_some member_rec(1) IntegerBelowNode)
next
  case (IntegerEqualsNode n x y xe ye)
  then have "kind g2 n = IntegerEqualsNode x y"
    by (metis kind_unchanged)
  then have "x \<in> eval_usages g1 n \<and> y \<in> eval_usages g1 n"
    by (metis IntegerEqualsNode.hyps(1,2,3) IRNodes.inputs_of_IntegerEqualsNode inputs_are_usages
        in_mono inputs.simps encode_in_ids list.set_intros(1) set_subset_Cons)
  then show ?case 
    by (metis inputs_of_IntegerEqualsNode \<open>kind g2 n = IntegerEqualsNode x y\<close> rep.IntegerEqualsNode
        child_member child_unchanged encode_in_ids ids_some member_rec(1) IntegerEqualsNode)
next
  case (IntegerLessThanNode n x y xe ye)
  then have "kind g2 n = IntegerLessThanNode x y"
    by (metis kind_unchanged)
  then have "x \<in> eval_usages g1 n \<and> y \<in> eval_usages g1 n"
    by (metis IntegerLessThanNode.hyps(1,2,3) IRNodes.inputs_of_IntegerLessThanNode encode_in_ids 
        in_mono inputs.simps inputs_are_usages list.set_intros(1) set_subset_Cons)
  then show ?case 
    by (metis rep.IntegerLessThanNode inputs_of_IntegerLessThanNode child_unchanged encode_in_ids
        \<open>kind g2 n = IntegerLessThanNode x y\<close> child_member member_rec(1) IntegerLessThanNode 
        ids_some)
next
  case (IntegerTestNode n x y xe ye)
  then have "kind g2 n = IntegerTestNode x y"
    by (metis kind_unchanged)
  then have "x \<in> eval_usages g1 n \<and> y \<in> eval_usages g1 n"
    by (metis IntegerTestNode.hyps IRNodes.inputs_of_IntegerTestNode encode_in_ids
        in_mono inputs.simps inputs_are_usages list.set_intros(1) set_subset_Cons)
  then show ?case
    by (metis rep.IntegerTestNode inputs_of_IntegerTestNode child_unchanged encode_in_ids
        \<open>kind g2 n = IntegerTestNode x y\<close> child_member member_rec(1) IntegerTestNode ids_some)
next
  case (IntegerNormalizeCompareNode n x y xe ye)
  then have "kind g2 n = IntegerNormalizeCompareNode x y"
    by (metis kind_unchanged)
  then have "x \<in> eval_usages g1 n \<and> y \<in> eval_usages g1 n"
    by (metis IRNodes.inputs_of_IntegerNormalizeCompareNode IntegerNormalizeCompareNode.hyps(1,2,3)
        encode_in_ids in_set_member inputs.simps inputs_are_usages member_rec(1))
  then show ?case
    by (metis IRNodes.inputs_of_IntegerNormalizeCompareNode IntegerNormalizeCompareNode.IH(1,2)
        IntegerNormalizeCompareNode.hyps(1,2,3) IntegerNormalizeCompareNode.prems(1) inputs.simps
        \<open>kind (g2::IRGraph) (n::nat) = IntegerNormalizeCompareNode (x::nat) (y::nat)\<close> local.wf
        encode_in_ids list.set_intros(1) rep.IntegerNormalizeCompareNode set_subset_Cons in_mono
        child_unchanged)
next
  case (IntegerMulHighNode n x y xe ye)
  then have "kind g2 n = IntegerMulHighNode x y"
    by (metis kind_unchanged)
  then have "x \<in> eval_usages g1 n"
    by (metis IRNodes.inputs_of_IntegerMulHighNode IntegerMulHighNode.hyps(1,2) encode_in_ids
        inputs_of_are_usages member_rec(1))
  then show ?case
    by (metis inputs_of_IntegerMulHighNode IntegerMulHighNode.IH(1,2) IntegerMulHighNode.hyps(1,2,3)
        IntegerMulHighNode.prems(1) child_unchanged encode_in_ids inputs.simps list.set_intros(1,2)
        \<open>kind (g2::IRGraph) (n::nat) = IntegerMulHighNode (x::nat) (y::nat)\<close> rep.IntegerMulHighNode
        local.wf)
next
  case (NarrowNode n ib rb x xe)
  then have "kind g2 n = NarrowNode ib rb x"
    by (metis kind_unchanged)
  then have "x \<in> eval_usages g1 n"
    by (metis NarrowNode.hyps(1,2) IRNodes.inputs_of_NarrowNode inputs_are_usages encode_in_ids
        list.set_intros(1) inputs.simps)
  then show ?case  
    by (metis NarrowNode(1,3,4,5) inputs_of_NarrowNode \<open>kind g2 n = NarrowNode ib rb x\<close> inputs.elims
        child_unchanged list.set_intros(1) rep.NarrowNode unchanged.simps)
next
  case (SignExtendNode n ib rb x xe)
  then have "kind g2 n = SignExtendNode ib rb x"
    by (metis kind_unchanged)
  then have "x \<in> eval_usages g1 n"
    by (metis inputs_of_SignExtendNode SignExtendNode.hyps(1,2) inputs_are_usages encode_in_ids
        list.set_intros(1) inputs.simps)
  then show ?case 
    by (metis SignExtendNode(1,3,4,5,6) inputs_of_SignExtendNode in_set_member list.set_intros(1)
        \<open>kind g2 n = SignExtendNode ib rb x\<close> child_member_in child_unchanged rep.SignExtendNode 
        unchanged.elims(2))
next
  case (ZeroExtendNode n ib rb x xe)
  then have "kind g2 n = ZeroExtendNode ib rb x"
    by (metis kind_unchanged)
  then have "x \<in> eval_usages g1 n"
    by (metis ZeroExtendNode.hyps(1,2) IRNodes.inputs_of_ZeroExtendNode encode_in_ids inputs.simps 
        inputs_are_usages list.set_intros(1))
  then show ?case 
    by (metis ZeroExtendNode(1,3,4,5,6) inputs_of_ZeroExtendNode child_unchanged unchanged.simps 
        \<open>kind g2 n = ZeroExtendNode ib rb x\<close> child_member_in rep.ZeroExtendNode member_rec(1))
next
  case (LeafNode n s)
  then show ?case
    by (metis kind_unchanged rep.LeafNode stamp_unchanged)
next
  case (PiNode n n' gu)
  then have "kind g2 n = PiNode n' gu"
    by (metis kind_unchanged)
  then show ?case
    by (metis PiNode.IH \<open>kind (g2) (n) = PiNode (n') (gu)\<close> child_unchanged encode_in_ids rep.PiNode
        inputs.elims list.set_intros(1)PiNode.hyps PiNode.prems(1,2) IRNodes.inputs_of_PiNode)
next
  case (RefNode n n')
  then have "kind g2 n = RefNode n'"
    by (metis kind_unchanged)
  then have "n' \<in> eval_usages g1 n"
    by (metis IRNodes.inputs_of_RefNode RefNode.hyps(1,2) inputs_are_usages list.set_intros(1)
        inputs.elims encode_in_ids)
  then show ?case
    by (metis IRNodes.inputs_of_RefNode RefNode.IH RefNode.hyps(1,2) RefNode.prems(1) inputs.elims
        \<open>kind g2 n = RefNode n'\<close> child_unchanged encode_in_ids list.set_intros(1) rep.RefNode
        local.wf)
next
  case (IsNullNode n v)
  then have "kind g2 n = IsNullNode v"
    by (metis kind_unchanged)
  then show ?case
    by (metis IRNodes.inputs_of_IsNullNode IsNullNode.IH IsNullNode.hyps(1,2) IsNullNode.prems(1) 
        \<open>kind g2 n = IsNullNode v\<close> child_unchanged encode_in_ids inputs.simps list.set_intros(1) 
        local.wf rep.IsNullNode)
 qed
qed

(* Main theorem that we want. *)
theorem stay_same:
  assumes nc: "unchanged (eval_usages g1 nid) g1 g2"
  assumes g1: "[g1, m, p] \<turnstile> nid \<mapsto> v1"
  assumes wf: "wf_graph g1"
  shows "[g2, m, p] \<turnstile> nid \<mapsto> v1"
proof -
  have nid: "nid \<in> ids g1"
    using g1 eval_in_ids by simp
  then have "nid \<in> eval_usages g1 nid" 
    using eval_usages_self by simp
  then have kind_same: "kind g1 nid = kind g2 nid"
    using nc node_unchanged by blast
  obtain e where e: "(g1 \<turnstile> nid \<simeq> e) \<and> ([m,p] \<turnstile> e \<mapsto> v1)"
    using g1 by (auto simp add: encodeeval.simps)
  then have val: "[m,p] \<turnstile> e \<mapsto> v1"
    by (simp add: g1 encodeeval.simps)
  then show ?thesis 
    using e nc unfolding encodeeval.simps
  proof (induct e v1 arbitrary: nid rule: "evaltree.induct")
    case (ConstantExpr c)
    then show ?case
      by (meson local.wf stay_same_encoding)
  next
    case (ParameterExpr i s)
    have "g2 \<turnstile> nid \<simeq> ParameterExpr i s"
      by (meson local.wf stay_same_encoding ParameterExpr)
    then show ?case 
      by (meson ParameterExpr.hyps evaltree.ParameterExpr)
  next
    case (ConditionalExpr ce cond branch te fe v)
    then have "g2 \<turnstile> nid \<simeq> ConditionalExpr ce te fe"
      using local.wf stay_same_encoding by presburger
    then show ?case
      by (meson ConditionalExpr.prems(1))
  next
    case (UnaryExpr xe v op)
    then show ?case
      using local.wf stay_same_encoding by blast
  next
    case (BinaryExpr xe x ye y op)
    then show ?case
      using local.wf stay_same_encoding by blast
  next
    case (LeafExpr val nid s)
    then show ?case
      by (metis local.wf stay_same_encoding)
  qed
qed

lemma add_changed:
  assumes "gup = add_node new k g"
  shows "changeonly {new} g gup"
  by (simp add: assms add_node.rep_eq kind.rep_eq stamp.rep_eq)

lemma disjoint_change:
  assumes "changeonly change g gup"
  assumes "nochange = ids g - change"
  shows "unchanged nochange g gup"
  using assms by simp

lemma add_node_unchanged:
  assumes "new \<notin> ids g"
  assumes "nid \<in> ids g"
  assumes "gup = add_node new k g"
  assumes "wf_graph g"
  shows "unchanged (eval_usages g nid) g gup"
proof -
  have "new \<notin> (eval_usages g nid)" 
    using assms by simp
  then have "changeonly {new} g gup"
    using assms add_changed by simp
  then show ?thesis 
    using assms by auto
qed

lemma eval_uses_imp:
  "((nid' \<in> ids g \<and> nid = nid')
    \<or> nid' \<in> inputs g nid
    \<or> (\<exists>nid'' . eval_uses g nid nid'' \<and> eval_uses g nid'' nid'))
    \<longleftrightarrow> eval_uses g nid nid'"
  by (meson eval_uses.simps)

lemma wf_use_ids:
  assumes "wf_graph g"
  assumes "nid \<in> ids g"
  assumes "eval_uses g nid nid'"
  shows "nid' \<in> ids g"
  using assms(3) apply (induction rule: eval_uses.induct) using assms(1) inp_in_g_wf by auto

lemma no_external_use:
  assumes "wf_graph g"
  assumes "nid' \<notin> ids g"
  assumes "nid \<in> ids g"
  shows "\<not>(eval_uses g nid nid')"
proof -
  have 0: "nid \<noteq> nid'"
    using assms by auto
  have inp: "nid' \<notin> inputs g nid"
    using assms inp_in_g_wf by auto
  have rec_0: "\<nexists>n . n \<in> ids g \<and> n = nid'"
    using assms by simp
  have rec_inp: "\<nexists>n . n \<in> ids g \<and> n \<in> inputs g nid'"
    using assms(2) by (simp add: inp_in_g)
  have rec: "\<nexists>nid'' . eval_uses g nid nid'' \<and> eval_uses g nid'' nid'"
    using wf_use_ids assms by blast
  from inp 0 rec show ?thesis 
    using eval_uses_imp by blast
qed

end
