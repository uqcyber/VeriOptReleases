subsection \<open>Control-flow Semantics Theorems\<close>

theory IRStepThms
  imports
    IRStepObj
    TreeToGraphThms
begin

text \<open>
We prove that within the same graph, a configuration triple will always
transition to the same subsequent configuration. Therefore, our step semantics
is deterministic.
\<close>

(*
definition stepping_nodes :: "(IRNode \<Rightarrow> bool) set" where
  "stepping_nodes = {
    is_sequential_node,
    is_IfNode,
    is_AbstractEndNode,
    is_NewInstanceNode,
    is_LoadFieldNode,
    is_SignedDivNode,
    is_SignedRemNode,
    is_LoadFieldNode,
    is_StoreFieldNode
  }"

inductive_cases StepE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g, p \<turnstile> (nid,m,h) \<rightarrow> next"

lemma stepping_nodes_distinct:
  assumes "sel \<in> stepping_nodes \<and> sel node"
  shows "\<forall> oth \<in> stepping_nodes - {sel} . \<not>(oth node)"
  using assms unfolding stepping_nodes_def sorry


proof (induction arbitrary: m h rule: step.induct)
  case (SequentialNode nid nid')
  have "is_sequential_node \<in> stepping_nodes" unfolding stepping_nodes_def by simp
  then have distinct: "\<forall> oth \<in> stepping_nodes - {is_sequential_node} . \<not>(oth (kind g nid))"
    using stepping_nodes_distinct SequentialNode(1) by auto
  obtain next' where "g, p \<turnstile> (nid, m, h) \<rightarrow> next'"
    using SequentialNode.hyps(1) step.SequentialNode
    by blast
  then have "next' = (nid', m, h)"
    apply (induct rule: step.induct) using SequentialNode sorry
  show ?case apply (rule allI) (*using step.cases*) apply (induction rule: step.induct)
    using distinct unfolding stepping_nodes_def
    using is_IfNode_def is_NewInstanceNode_def is_LoadFieldNode_def is_SignedDivNode_def is_SignedRemNode_def
    is_LoadFieldNode_def is_StoreFieldNode_def 
    apply (rule stepping_nodes_distinct [where sel = is_sequential_node, where node = "kind g nid"])
  then show ?case apply (rule stepping_nodes_distinct [where sel = is_sequential_node, where node = "kind g nid"])?
next
  case (IfNode nid cond tb fb condE m val nid' h)
  then show ?case sorry
next
  case (EndNodes nid merge i phis inps inpsE m vs m' h)
  then show ?case sorry
next
  case (NewInstanceNode nid f obj nid' h' ref h m' m)
  then show ?case sorry
next
  case (LoadFieldNode nid f obj nid' objE m ref h v m')
  then show ?case sorry
next
  case (SignedDivNode nid x y zero sb nxt xe ye m v1 v2 v m' h)
  then show ?case sorry
next
  case (SignedRemNode nid x y zero sb nxt xe ye m v1 v2 v m' h)
  then show ?case sorry
next
  case (StaticLoadFieldNode nid f nid' h v m' m)
  then show ?case sorry
next
  case (StoreFieldNode nid f newval uu obj nid' newvalE objE m val ref h' h m')
  then show ?case sorry
next
  case (StaticStoreFieldNode nid f newval uv nid' newvalE m val h' h m')
  then show ?case sorry
qed
*)

subsubsection \<open>Control-flow Step is Deterministic\<close>

theorem stepDet:
   "(g, p \<turnstile> (nid,m,h) \<rightarrow> next) \<Longrightarrow>
   (\<forall> next'. ((g, p \<turnstile> (nid,m,h) \<rightarrow> next') \<longrightarrow> next = next'))"
proof (induction rule: "step.induct")
  case (SequentialNode nid "next" m h)
  have notif: "\<not>(is_IfNode (kind g nid))"
    by (metis is_IfNode_def SequentialNode.hyps(1) is_sequential_node.simps(22))
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (metis is_AbstractEndNode.simps SequentialNode.hyps(1) is_sequential_node.simps(18,36)
        is_EndNode.elims(2) is_LoopEndNode_def)
  have notnew: "\<not>(is_NewInstanceNode (kind g nid))"
    by (metis is_NewInstanceNode_def SequentialNode.hyps(1) is_sequential_node.simps(42))
  have notload: "\<not>(is_LoadFieldNode (kind g nid))"
    by (metis is_LoadFieldNode_def SequentialNode.hyps(1) is_sequential_node.simps(33))
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    by (metis is_StoreFieldNode_def SequentialNode.hyps(1) is_sequential_node.simps(54))
  have notdivrem:  "\<not>(is_IntegerDivRemNode (kind g nid))"
    by (metis is_IntegerDivRemNode.simps SequentialNode.hyps(1) is_sequential_node.simps(52,53)
        is_SignedDivNode_def is_SignedRemNode_def)
  from notif notend notnew notload notstore notdivrem
  show ?case
    by (smt (verit) SequentialNode Pair_inject IRNode.disc(898,1666,3266) IRNode.discI(39)
        step.cases is_sequential_node.simps(12,14,20,34,41,52,53,55))
next
  case (FixedGuardNode nid cond before "next" condE m p val h)
  have notseq: "\<not>(is_sequential_node (kind g nid))"
    using is_sequential_node.simps by (simp add: FixedGuardNode.hyps(1))
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: FixedGuardNode.hyps(1))
  have notloadindex: "\<not>(is_LoadIndexedNode (kind g nid))"
    by (simp add: FixedGuardNode.hyps(1))
  have notstoreindex: "\<not>(is_StoreIndexedNode (kind g nid))"
    by (simp add: FixedGuardNode.hyps(1))
  from notseq notend notloadindex notstoreindex
  show ?case
    by (smt (verit) IRNode.distinct(385,727,1459,1483,1505,1507,1527,1529,1533) IRNode.inject(13)
        step.cases Pair_inject FixedGuardNode.hyps(1,5) IRNode.disc(1730,3330))
next
  case (BytecodeExceptionNode nid args st n' ex h' ref h m' m)
  have notseq: "\<not>(is_sequential_node (kind g nid))"
    by (simp add: BytecodeExceptionNode.hyps(1))
  have notif: "\<not>(is_IfNode (kind g nid))"
    by (simp add: BytecodeExceptionNode.hyps(1))
  have notref: "\<not>(is_RefNode (kind g nid))"
    by (metis notseq is_RefNode_def is_sequential_node.simps(7))
  have notnew: "\<not>(is_NewInstanceNode (kind g nid))"
    by (simp add: BytecodeExceptionNode.hyps(1))
  have notload: "\<not>(is_LoadFieldNode (kind g nid))"
    by (simp add: BytecodeExceptionNode.hyps(1))
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    by (simp add: BytecodeExceptionNode.hyps(1))
  have notdivrem: "\<not>(is_IntegerDivRemNode (kind g nid))"
    by (simp add: BytecodeExceptionNode.hyps(1))
  have notfixedguard: "\<not>(is_FixedGuardNode (kind g nid))"
    by (simp add: BytecodeExceptionNode.hyps(1))
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: BytecodeExceptionNode.hyps(1))
  have notnewarray: "\<not>(is_NewArrayNode (kind g nid))"
    by (simp add: BytecodeExceptionNode.hyps(1))
  have notarraylength: "\<not>(is_ArrayLengthNode (kind g nid))"
    by (simp add: BytecodeExceptionNode.hyps(1))
  have notloadindex: "\<not>(is_LoadIndexedNode (kind g nid))"
    by (simp add: BytecodeExceptionNode.hyps(1))
  have notstoreindex: "\<not>(is_StoreIndexedNode (kind g nid))"
    by (simp add: BytecodeExceptionNode.hyps(1))
  from notseq notif notref notnew notload notstore notdivrem notfixedguard notend notnewarray
       notarraylength notloadindex notstoreindex
  show ?case
    apply simp
    by (smt (verit) BytecodeExceptionNode.hyps IRNode.disc(1666,2370,3074,3138,3266) Pair_inject
        IRNode.inject(7) IRNode.discI(4,53) repDet step.cases notend is_NewInstanceNode_def
        is_LoadIndexedNode_def is_IntegerDivRemNode.simps is_IfNode_def is_FixedGuardNode_def)
next
  case (IfNode nid cond tb fb m val "next" h)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    by (simp add: IfNode.hyps(1))
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: IfNode.hyps(1))
  have notdivrem: "\<not>(is_IntegerDivRemNode (kind g nid))"
    by (simp add: IfNode.hyps(1))
  have notnewarray: "\<not>(is_NewArrayNode (kind g nid))"
    by (simp add: IfNode.hyps(1))
  from notseq notend notdivrem notnewarray
  show ?case
    by (smt (verit) IRNode.inject(15) Pair_inject repDet evalDet IfNode.hyps step.cases
        IRNode.distinct(389,731,1459,1673,1675,1697,1717,1719,1723,1725) IRNode.disc(2370))
next
  case (EndNodes nid merge i phis inputs m vs m' h)
  have notseq: "\<not>(is_sequential_node (kind g nid))"
    by (metis is_EndNode.elims(2) is_LoopEndNode_def is_sequential_node.simps(18,36)
        is_AbstractEndNode.simps EndNodes.hyps(1))
  have notif: "\<not>(is_IfNode (kind g nid))"
    by (metis IRNode.distinct_disc(1682) is_AbstractEndNode.elims(2) EndNodes.hyps(1) is_IfNode_def
        is_EndNode.simps(16))
  have notref: "\<not>(is_RefNode (kind g nid))"
    by (metis notseq is_RefNode_def is_sequential_node.simps(7))
  have notnew: "\<not>(is_NewInstanceNode (kind g nid))"
    by (metis IRNode.distinct_disc(2930) is_EndNode.simps(40) is_NewInstanceNode_def
        is_AbstractEndNode.simps EndNodes.hyps(1))
  have notload: "\<not>(is_LoadFieldNode (kind g nid))"
    by (metis IRNode.distinct_disc(2654) is_EndNode.simps(28) is_LoadFieldNode_def EndNodes.hyps(1)
        is_AbstractEndNode.simps)
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    by (metis IRNode.distinct_disc(2956) is_EndNode.simps(53) is_StoreFieldNode_def EndNodes.hyps(1)
        is_AbstractEndNode.simps)
  have notdivrem: "\<not>(is_IntegerDivRemNode (kind g nid))"
    using EndNodes.hyps(1) is_SignedDivNode_def is_SignedRemNode_def by force
  have notfixedguard: "\<not>(is_FixedGuardNode (kind g nid))"
    by (metis IRNode.distinct_disc(1492) is_EndNode.simps(14) is_FixedGuardNode_def EndNodes.hyps(1)
        is_AbstractEndNode.simps)
  have notbytecodeexception: "\<not>(is_BytecodeExceptionNode (kind g nid))"
    by (metis IRNode.distinct_disc(763) is_BytecodeExceptionNode_def is_AbstractEndNode.simps
        is_EndNode.simps(8) EndNodes.hyps(1))
  have notnewarray: "\<not>(is_NewArrayNode (kind g nid))"
    by (metis IRNode.distinct_disc(2928) is_EndNode.simps(39) is_NewArrayNode_def EndNodes.hyps(1)
        is_AbstractEndNode.simps)
  have notarraylength: "\<not>(is_ArrayLengthNode (kind g nid))"
    by (metis IRNode.distinct_disc(421) is_EndNode.simps(5) is_ArrayLengthNode_def EndNodes.hyps(1)
        is_AbstractEndNode.simps)
  have notloadindex: "\<not>(is_LoadIndexedNode (kind g nid))"
    by (metis IRNode.distinct_disc(2721) is_EndNode.simps(29) is_LoadIndexedNode_def
        EndNodes.hyps(1) is_AbstractEndNode.simps)
  have notstoreindex: "\<not>(is_StoreIndexedNode (kind g nid))"
    by (metis IRNode.distinct_disc(2957) is_EndNode.simps(54) is_AbstractEndNode.simps
        EndNodes.hyps(1) is_StoreIndexedNode_def)
  from notseq notif notref notnew notload notstore notdivrem notfixedguard notbytecodeexception
       notnewarray notarraylength notloadindex notstoreindex
  show ?case
    by (smt (verit) is_FixedGuardNode_def repAllDet evalAllDet is_IfNode_def EndNodes step.cases
        is_RefNode_def Pair_inject is_LoadFieldNode_def is_NewInstanceNode_def is_StoreFieldNode_def
        is_SignedDivNode_def is_SignedRemNode_def is_IntegerDivRemNode.elims(3) is_NewArrayNode_def
        is_BytecodeExceptionNode_def is_ArrayLengthNode_def is_LoadIndexedNode_def
        is_StoreIndexedNode_def)
next
  case (NewArrayNode nid len st n' lenE m length' arrayType h' ref h refNo h'')
  have notseq: "\<not>(is_sequential_node (kind g nid))"
    by (simp add: NewArrayNode.hyps(1))
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: NewArrayNode.hyps(1))
  have notif: "\<not>(is_IfNode (kind g nid))"
    by (simp add: NewArrayNode.hyps(1))
  have notload: "\<not>(is_LoadFieldNode (kind g nid))"
    by (simp add: NewArrayNode.hyps(1))
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    by (simp add: NewArrayNode.hyps(1))
  have notfixedguard: "\<not>(is_FixedGuardNode (kind g nid))"
    by (simp add: NewArrayNode.hyps(1))
  have notbytecodeexception: "\<not>(is_BytecodeExceptionNode (kind g nid))"
    by (simp add: NewArrayNode.hyps(1))
  have notarraylength: "\<not>(is_ArrayLengthNode (kind g nid))"
    by (simp add: NewArrayNode.hyps(1))
  have notnew: "\<not>(is_NewInstanceNode (kind g nid))"
    by (simp add: NewArrayNode.hyps(1))
  from notseq notend notif notload notstore notfixedguard notbytecodeexception notarraylength notnew
  show ?case
    by (smt (verit) IRNode.disc(1666) repDet Value.inject(2) IRNode.distinct(2735,3327,3329,3335)
        is_FixedGuardNode_def is_NewInstanceNode_def is_ArrayLengthNode_def is_IfNode_def evalDet
        is_BytecodeExceptionNode_def is_StoreFieldNode_def IRNode.inject EndNodes evalAllDet
        Pair_inject step.cases NewArrayNode)
next
  case (ArrayLengthNode nid x nid' xE m ref h arrayVal length' m')
  have notseq: "\<not>(is_sequential_node (kind g nid))"
    by (simp add: ArrayLengthNode.hyps(1))
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: ArrayLengthNode.hyps(1))
  have notif: "\<not>(is_IfNode (kind g nid))"
    by (simp add: ArrayLengthNode.hyps(1))
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    by (simp add: ArrayLengthNode.hyps(1))
  have notfixedguard: "\<not>(is_FixedGuardNode (kind g nid))"
    by (simp add: ArrayLengthNode.hyps(1))
  have notbytecodeexception: "\<not>(is_BytecodeExceptionNode (kind g nid))"
    by (simp add: ArrayLengthNode.hyps(1))
  have notnew: "\<not>(is_NewInstanceNode (kind g nid))"
    by (simp add: ArrayLengthNode.hyps(1))
  have notnewarray: "\<not>(is_NewArrayNode (kind g nid))"
    by (simp add: ArrayLengthNode.hyps(1))
  have notloadindex: "\<not>(is_LoadIndexedNode (kind g nid))"
    by (simp add: ArrayLengthNode.hyps(1))
  from notseq notend notif notstore notfixedguard notbytecodeexception notnew notnewarray
       notloadindex
  show ?case
    by (smt (verit) IRNode.disc(217,218,239,240,243) Value.inject(2) ArrayLengthNode step.cases
        Pair_inject IRNode.inject is_StoreFieldNode_def is_BytecodeExceptionNode_def is_IfNode_def
        is_ArrayLengthNode_def is_NewInstanceNode_def is_FixedGuardNode_def is_NewArrayNode_def
        repDet evalDet)
next
  case (LoadIndexedNode nid index gu array nid' indexE m indexVal arrayE ref h arrayVal loaded m')
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    by simp
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: LoadIndexedNode.hyps(1))
  have notif: "\<not>(is_IfNode (kind g nid))"
    by (simp add: LoadIndexedNode.hyps(1))
  have notref: "\<not>(is_RefNode (kind g nid))"
    by (simp add: LoadIndexedNode.hyps(1))
  have notload: "\<not>(is_LoadFieldNode (kind g nid))"
    by (simp add: LoadIndexedNode.hyps(1))
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    by (simp add: LoadIndexedNode.hyps(1))
  have notdivrem: "\<not>(is_IntegerDivRemNode (kind g nid))"
    by (simp add: LoadIndexedNode.hyps(1))
  have notnewarray: "\<not>(is_NewArrayNode (kind g nid))"
    by (simp add: LoadIndexedNode.hyps(1))
  have notarraylength: "\<not>(is_ArrayLengthNode (kind g nid))"
    by (simp add: LoadIndexedNode.hyps(1))
  have notstoreindex: "\<not>(is_StoreIndexedNode (kind g nid))"
    by (simp add: LoadIndexedNode.hyps(1))
  have notfixedguard: "\<not>(is_FixedGuardNode (kind g nid))"
    by (simp add: LoadIndexedNode.hyps(1))
  have notbytecodeexception: "\<not>(is_BytecodeExceptionNode (kind g nid))"
    by (simp add: LoadIndexedNode.hyps(1))
  have notnew: "\<not>(is_NewInstanceNode (kind g nid))"
    by (simp add: LoadIndexedNode.hyps(1))
  from notseq notend notif notref notload notstore notdivrem notnewarray notarraylength notnew
       notstoreindex notfixedguard notbytecodeexception
  show ?case
    by (smt (verit) IRNode.distinct(2757,2759) IRNode.inject(28) Value.inject(2) evalDet repDet
        LoadIndexedNode.hyps Pair_inject step.cases is_ArrayLengthNode_def is_FixedGuardNode_def
        is_BytecodeExceptionNode_def is_IfNode_def is_LoadFieldNode_def is_StoreIndexedNode_def
        is_NewArrayNode_def is_NewInstanceNode_def is_StoreFieldNode_def)
next
  case (StoreIndexedNode nid ch val st i gu a nid' indexE m iv arrayE ref valE val0 h av new h' m')
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    by simp
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: StoreIndexedNode.hyps(1))
  have notif: "\<not>(is_IfNode (kind g nid))"
    by (simp add: StoreIndexedNode.hyps(1))
  have notref: "\<not>(is_RefNode (kind g nid))"
    by (simp add: StoreIndexedNode.hyps(1))
  have notload: "\<not>(is_LoadFieldNode (kind g nid))"
    by (simp add: StoreIndexedNode.hyps(1))
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    by (simp add: StoreIndexedNode.hyps(1))
  have notdivrem: "\<not>(is_IntegerDivRemNode (kind g nid))"
    by (simp add: StoreIndexedNode.hyps(1))
  have notnewarray: "\<not>(is_NewArrayNode (kind g nid))"
    by (simp add: StoreIndexedNode.hyps(1))
  have notarraylength: "\<not>(is_ArrayLengthNode (kind g nid))"
    by (simp add: StoreIndexedNode.hyps(1))
  have notfixedguard: "\<not>(is_FixedGuardNode (kind g nid))"
    by (simp add: StoreIndexedNode.hyps(1))
  have notbytecodeexception: "\<not>(is_BytecodeExceptionNode (kind g nid))"
    by (simp add: StoreIndexedNode.hyps(1))
  have notnew: "\<not>(is_NewInstanceNode (kind g nid))"
    by (simp add: StoreIndexedNode.hyps(1))
  from notseq notend notif notref notload notstore notdivrem notnewarray notarraylength notnew
       notfixedguard notbytecodeexception
  show ?case
    by (smt (verit) IRNode.disc(3305,3326,3327) IRNode.inject(53) StoreIndexedNode.hyps Pair_inject
        Value.inject(2) is_ArrayLengthNode_def is_IfNode_def is_BytecodeExceptionNode_def evalDet
        is_FixedGuardNode_def is_LoadFieldNode_def is_NewArrayNode_def step.cases repDet
        is_StoreIndexedNode_def is_NewInstanceNode_def is_StoreFieldNode_def)
next
  case (NewInstanceNode nid f obj nxt h' ref h m' m)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    by simp
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: NewInstanceNode.hyps(1))
  have notif: "\<not>(is_IfNode (kind g nid))"
    by (simp add: NewInstanceNode.hyps(1))
  have notref: "\<not>(is_RefNode (kind g nid))"
    by (simp add: NewInstanceNode.hyps(1))
  have notload: "\<not>(is_LoadFieldNode (kind g nid))"
    by (simp add: NewInstanceNode.hyps(1))
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    by (simp add: NewInstanceNode.hyps(1))
  have notdivrem:  "\<not>(is_IntegerDivRemNode (kind g nid))"
    by (simp add: NewInstanceNode.hyps(1))
  have notnewarray:  "\<not>(is_NewArrayNode (kind g nid))"
    by (simp add: NewInstanceNode.hyps(1))
  have notarraylength:  "\<not>(is_ArrayLengthNode (kind g nid))"
    by (simp add: NewInstanceNode.hyps(1))
  from notseq notend notif notref notload notstore notdivrem notnewarray notarraylength
  show ?case
    by (smt (verit) NewInstanceNode step.cases IRNode.disc(1666,2370,3266) IRNode.discI(4,15)
        Pair_inject IRNode.distinct(779,1507,2737,3373,3375,3381) IRNode.inject(39))
next
  case (LoadFieldNode nid f obj nxt m ref h v m')
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    by simp
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: LoadFieldNode.hyps(1))
  have notdivrem: "\<not>(is_IntegerDivRemNode (kind g nid))"
    by (simp add: LoadFieldNode.hyps(1))
  have notif: "\<not>(is_IfNode (kind g nid))"
    by (simp add: LoadFieldNode.hyps(1))
  have notref: "\<not>(is_RefNode (kind g nid))"
    by (simp add: LoadFieldNode.hyps(1))
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    by (simp add: LoadFieldNode.hyps(1))
  have notnewarray: "\<not>(is_NewArrayNode (kind g nid))"
    by (simp add: LoadFieldNode.hyps(1))
  have notarraylength: "\<not>(is_ArrayLengthNode (kind g nid))"
    by (simp add: LoadFieldNode.hyps(1))
  from notseq notend notdivrem notif notref notstore notnewarray notarraylength
  show ?case
    by (smt (verit) LoadFieldNode step.cases evalDet IRNode.inject(27) option.discI option.inject
        IRNode.distinct(755,1483,2647,2669,2689,2691,2697) Pair_inject repDet Value.inject(2)
        is_ArrayLengthNode_def is_IfNode_def is_NewArrayNode_def is_StoreFieldNode_def)
next
  case (SignedDivNode nid x y zero sb nxt m v1 v2 v m' h)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    by simp
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: SignedDivNode.hyps(1))
  have notif: "\<not>(is_IfNode (kind g nid))"
    by (simp add: SignedDivNode.hyps(1))
  have notref: "\<not>(is_RefNode (kind g nid))"
    by (simp add: SignedDivNode.hyps(1))
  have notload: "\<not>(is_LoadFieldNode (kind g nid))"
    by (simp add: SignedDivNode.hyps(1))
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    by (simp add: SignedDivNode.hyps(1))
  have notnewarray: "\<not>(is_NewArrayNode (kind g nid))"
    by (simp add: SignedDivNode.hyps(1))
  have notarraylength: "\<not>(is_ArrayLengthNode (kind g nid))"
    by (simp add: SignedDivNode.hyps(1))
  from notseq notend notif notref notload notstore notnewarray notarraylength
  show ?case
    by (smt (verit) IRNode.distinct(799,1527,2757,3373,3725,3731) evalDet IRNode.inject(49) repDet
        SignedDivNode Pair_inject is_ArrayLengthNode_def is_IfNode_def is_NewArrayNode_def
        is_LoadFieldNode_def is_StoreFieldNode_def step.cases)
next
  case (SignedRemNode nid x y zero sb nxt m v1 v2 v m' h)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    by simp
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: SignedRemNode.hyps(1))
  from notseq notend
  show ?case
    by (smt (verit) IRNode.distinct(459,801,1529,1719,2691,2759,3329,3375,3725,3753,3755) evalDet
        step.cases SignedRemNode repDet Pair_inject IRNode.inject(50))
next
  case (StaticLoadFieldNode nid f nxt h v m' m)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    by simp
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: StaticLoadFieldNode.hyps(1))
  have notdivrem: "\<not>(is_IntegerDivRemNode (kind g nid))"
    by (simp add: StaticLoadFieldNode.hyps(1))
  from notseq notend notdivrem
  show ?case
    by (smt (verit) IRNode.distinct(413,755,1483,1673,2647,2667,2669,2689,2691,2695,2697)
        IRNode.inject(27) step.cases StaticLoadFieldNode Pair_inject option.distinct(1))
next
  case (StoreFieldNode nid f newval uu obj nxt m val ref h' h m')
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    by simp
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: StoreFieldNode.hyps(1))
  have notdivrem: "\<not>(is_IntegerDivRemNode (kind g nid))"
    by (simp add: StoreFieldNode.hyps(1))
  have notif: "\<not>(is_IfNode (kind g nid))"
    by (simp add: StoreFieldNode.hyps(1))
  have notref: "\<not>(is_RefNode (kind g nid))"
    by (simp add: StoreFieldNode.hyps(1))
  have notload: "\<not>(is_LoadFieldNode (kind g nid))"
    by (simp add: StoreFieldNode.hyps(1))
  have notnewarray: "\<not>(is_NewArrayNode (kind g nid))"
    by (simp add: StoreFieldNode.hyps(1))
  have notarraylength: "\<not>(is_ArrayLengthNode (kind g nid))"
    by (simp add: StoreFieldNode.hyps(1))
  from notseq notend notdivrem notif notref notload notnewarray notarraylength
  show ?case
    by (smt (verit) IRNode.distinct(805,1533,2763,3379,3729,3753,3797) evalDet step.cases repDet
        IRNode.inject(52) StoreFieldNode option.discI Pair_inject Value.inject(2) option.inject
        is_ArrayLengthNode_def is_IfNode_def is_LoadFieldNode_def is_NewArrayNode_def)
next
  case (StaticStoreFieldNode nid f newval uv nxt m val h' h m')
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    by simp
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: StaticStoreFieldNode.hyps(1))
  have notdivrem: "\<not>(is_IntegerDivRemNode (kind g nid))"
    by (simp add: StaticStoreFieldNode.hyps(1))
  from notseq notend notdivrem
  show ?case
    by (smt (verit) IRNode.distinct(463,805,1533,1723,2695,2763,3333,3379,3729,3753,3797) evalDet
        IRNode.inject(52) step.cases StoreFieldNode StaticStoreFieldNode.hyps option.distinct(1)
        Pair_inject repDet)
qed

lemma stepRefNode:
  "\<lbrakk>kind g nid = RefNode nid'\<rbrakk> \<Longrightarrow> g, p \<turnstile> (nid,m,h) \<rightarrow> (nid',m,h)"
  by (metis IRNodes.successors_of_RefNode is_sequential_node.simps(7) nth_Cons_0 SequentialNode)

lemma IfNodeStepCases: 
  assumes "kind g nid = IfNode cond tb fb"
  assumes "g \<turnstile> cond \<simeq> condE"
  assumes "[m, p] \<turnstile> condE \<mapsto> v"
  assumes "g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h)"
  shows "nid' \<in> {tb, fb}"
  by (metis insert_iff old.prod.inject step.IfNode stepDet assms)

lemma IfNodeSeq:
  shows "kind g nid = IfNode cond tb fb \<longrightarrow> \<not>(is_sequential_node (kind g nid))"
  using is_sequential_node.simps(18,19) by simp
  
lemma IfNodeCond:
  assumes "kind g nid = IfNode cond tb fb"
  assumes "g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h)"
  shows "\<exists> condE v. ((g \<turnstile> cond \<simeq> condE) \<and> ([m, p] \<turnstile> condE \<mapsto> v))"
  using assms(2,1) by (induct "(nid,m,h)" "(nid',m,h)" rule: step.induct; auto)

lemma step_in_ids:
  assumes "g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h')"
  shows "nid \<in> ids g"
  using assms apply (induct "(nid, m, h)" "(nid', m', h')" rule: step.induct) apply fastforce
  prefer 4 prefer 14 defer defer
  using IRNode.distinct(481,823,1551,1741,2713,2781,3351,3397,3747,3771,3813,3831) ids_some
        apply presburger+
  by (metis IRNode.disc(1952) is_EndNode.simps(62) is_AbstractEndNode.simps not_in_g)

end
