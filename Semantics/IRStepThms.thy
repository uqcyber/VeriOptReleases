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
    using is_StoreFieldNode_def SequentialNode.hyps(1)
    by (metis is_sequential_node.simps(56))
  have notdivrem:  "\<not>(is_IntegerDivRemNode (kind g nid))"
    using is_IntegerDivRemNode.simps SequentialNode.hyps(1)
        is_SignedDivNode_def is_SignedRemNode_def
    by (metis is_sequential_node.simps(52) is_sequential_node.simps(55))
  from notif notend notnew notload notstore notdivrem
  show ?case
    using SequentialNode Pair_inject
        step.cases
    by (smt (verit) IRNode.disc(1718) IRNode.disc(3500) IRNode.disc(926) IRNode.discI(39) is_sequential_node.simps(12) is_sequential_node.simps(14) is_sequential_node.simps(20) is_sequential_node.simps(34) is_sequential_node.simps(41) is_sequential_node.simps(52) is_sequential_node.simps(55) is_sequential_node.simps(57))
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
    using step.cases Pair_inject FixedGuardNode.hyps(1,5)
    by (smt (verit) IRNode.disc(1784) IRNode.disc(3566) IRNode.distinct(1511) IRNode.distinct(1535) IRNode.distinct(1557) IRNode.distinct(1559) IRNode.distinct(1579) IRNode.distinct(1585) IRNode.distinct(1589) IRNode.distinct(397) IRNode.distinct(751) IRNode.inject(13))

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
    by (smt (verit) BytecodeExceptionNode.hyps(1) BytecodeExceptionNode.hyps(2) BytecodeExceptionNode.hyps(3) BytecodeExceptionNode.hyps(4) IRNode.discI(39) IRNode.inject(7) Pair_inject is_ArrayLengthNode_def is_FixedGuardNode_def is_IfNode_def is_IntegerDivRemNode.simps is_LoadFieldNode_def is_LoadIndexedNode_def is_NewArrayNode_def is_SignedDivNode_def is_SignedRemNode_def is_StoreFieldNode_def is_StoreIndexedNode_def step.cases)

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
    using Pair_inject repDet evalDet IfNode.hyps step.cases
    by (smt (verit) IRNode.disc(2444) IRNode.distinct(1511) IRNode.distinct(1733) IRNode.distinct(1735) IRNode.distinct(1757) IRNode.distinct(1777) IRNode.distinct(1783) IRNode.distinct(1787) IRNode.distinct(1789) IRNode.distinct(401) IRNode.distinct(755) IRNode.inject(15))
next
  case (EndNodes nid merge i phis inputs m vs m' h)
  have notseq: "\<not>(is_sequential_node (kind g nid))"
    by (metis is_EndNode.elims(2) is_LoopEndNode_def is_sequential_node.simps(18,36)
        is_AbstractEndNode.simps EndNodes.hyps(1))
  have notif: "\<not>(is_IfNode (kind g nid))"
    using is_AbstractEndNode.elims(2) EndNodes.hyps(1) is_IfNode_def
        is_EndNode.simps(16)
    by (metis IRNode.distinct_disc(1742))
  have notref: "\<not>(is_RefNode (kind g nid))"
    using notseq is_RefNode_def
    by (metis is_sequential_node.simps(7))
  have notnew: "\<not>(is_NewInstanceNode (kind g nid))"
    using is_EndNode.simps(40) is_NewInstanceNode_def
      is_AbstractEndNode.simps EndNodes.hyps(1)
    by (metis IRNode.distinct_disc(3053))
  have notload: "\<not>(is_LoadFieldNode (kind g nid))"
    using  is_EndNode.simps(28) is_LoadFieldNode_def EndNodes.hyps(1)
        is_AbstractEndNode.simps
    by (metis IRNode.distinct_disc(2762))
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    using is_EndNode.simps(53) is_StoreFieldNode_def EndNodes.hyps(1)
      is_AbstractEndNode.simps
    by (metis IRNode.distinct_disc(3084) is_EndNode.simps(55))
  have notdivrem: "\<not>(is_IntegerDivRemNode (kind g nid))"
    using EndNodes.hyps(1) is_SignedDivNode_def is_SignedRemNode_def by force
  have notfixedguard: "\<not>(is_FixedGuardNode (kind g nid))"
    using is_EndNode.simps(14) is_FixedGuardNode_def EndNodes.hyps(1)
        is_AbstractEndNode.simps
    by (metis IRNode.distinct_disc(1543))
  have notbytecodeexception: "\<not>(is_BytecodeExceptionNode (kind g nid))"
    using is_BytecodeExceptionNode_def is_AbstractEndNode.simps
      is_EndNode.simps(8) EndNodes.hyps(1)
    by (metis IRNode.distinct_disc(788))
  have notnewarray: "\<not>(is_NewArrayNode (kind g nid))"
    using is_EndNode.simps(39) is_NewArrayNode_def EndNodes.hyps(1)
      is_AbstractEndNode.simps
    by (metis IRNode.distinct_disc(3052))
  have notarraylength: "\<not>(is_ArrayLengthNode (kind g nid))"
    using is_EndNode.simps(5) is_ArrayLengthNode_def EndNodes.hyps(1)
        is_AbstractEndNode.simps
    by (metis IRNode.disc(1954))
  have notloadindex: "\<not>(is_LoadIndexedNode (kind g nid))"
    using is_EndNode.simps(29) is_LoadIndexedNode_def
      EndNodes.hyps(1) is_AbstractEndNode.simps
    by (metis IRNode.disc(1979))
  have notstoreindex: "\<not>(is_StoreIndexedNode (kind g nid))"
    using is_EndNode.simps(54) is_AbstractEndNode.simps
      EndNodes.hyps(1) is_StoreIndexedNode_def
    by (metis IRNode.distinct_disc(3085) is_EndNode.simps(56))
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
  show ?case sledgehammer
    by (smt (verit) IRNode.disc(1718) IRNode.disc(3500) IRNode.disc(926) IRNode.discI(39) IRNode.distinct(2847) IRNode.distinct(3479) IRNode.distinct(3485) IRNode.distinct(3491) IRNode.inject(38) NewArrayNode.hyps(1) NewArrayNode.hyps(2) NewArrayNode.hyps(3) NewArrayNode.hyps(4) NewArrayNode.hyps(5) NewArrayNode.hyps(6) NewArrayNode.hyps(7) NewArrayNode.hyps(8) Pair_inject Value.inject(2) evalDet is_ArrayLengthNode_def is_BytecodeExceptionNode_def is_FixedGuardNode_def repDet step.cases)
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
    by (smt (verit) ArrayLengthNode.hyps(1) ArrayLengthNode.hyps(2) ArrayLengthNode.hyps(3) ArrayLengthNode.hyps(4) ArrayLengthNode.hyps(5) ArrayLengthNode.hyps(6) IRNode.disc(1784) IRNode.disc(3500) IRNode.disc(926) IRNode.discI(39) IRNode.distinct(425) IRNode.distinct(469) IRNode.distinct(475) IRNode.distinct(481) IRNode.inject(4) Pair_inject Value.inject(2) evalDet is_BytecodeExceptionNode_def is_FixedGuardNode_def is_NewArrayNode_def repDet step.cases)
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
    by (smt (verit) IRNode.disc(1718) IRNode.disc(3500) IRNode.disc(3566) IRNode.disc(926) IRNode.discI(39) IRNode.inject(28) LoadIndexedNode.hyps(1) LoadIndexedNode.hyps(2) LoadIndexedNode.hyps(3) LoadIndexedNode.hyps(4) LoadIndexedNode.hyps(5) LoadIndexedNode.hyps(6) LoadIndexedNode.hyps(7) LoadIndexedNode.hyps(8) Value.inject(2) evalDet is_ArrayLengthNode_def is_BytecodeExceptionNode_def is_FixedGuardNode_def is_IntegerDivRemNode.simps is_NewArrayNode_def is_SignedDivNode_def is_SignedRemNode_def prod.inject repDet step.cases)
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
    by (smt (verit) IRNode.disc(1718) IRNode.disc(3500) IRNode.disc(926) IRNode.discI(39) IRNode.distinct(2881) IRNode.distinct(3931) IRNode.distinct(4009) IRNode.distinct(481) IRNode.inject(55) Pair_inject StoreIndexedNode.hyps(1) StoreIndexedNode.hyps(10) StoreIndexedNode.hyps(11) StoreIndexedNode.hyps(2) StoreIndexedNode.hyps(3) StoreIndexedNode.hyps(4) StoreIndexedNode.hyps(5) StoreIndexedNode.hyps(6) StoreIndexedNode.hyps(7) StoreIndexedNode.hyps(8) StoreIndexedNode.hyps(9) Value.inject(2) evalDet is_BytecodeExceptionNode_def is_FixedGuardNode_def is_NewArrayNode_def repDet step.cases)
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
    using NewInstanceNode step.cases
        Pair_inject
    by (smt (verit) IRNode.disc(1718) IRNode.disc(2444) IRNode.disc(3500) IRNode.discI(15) IRNode.discI(4) IRNode.distinct(1559) IRNode.distinct(2849) IRNode.distinct(3529) IRNode.distinct(3535) IRNode.distinct(3541) IRNode.distinct(803) IRNode.inject(39))
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
    using LoadFieldNode step.cases evalDet option.discI option.inject
        Pair_inject repDet Value.inject(2)
        is_ArrayLengthNode_def is_IfNode_def is_NewArrayNode_def is_StoreFieldNode_def
    by (smt (verit) IRNode.distinct(1535) IRNode.distinct(2755) IRNode.distinct(2777) IRNode.distinct(2797) IRNode.distinct(2803) IRNode.distinct(2809) IRNode.distinct(779) IRNode.inject(27))
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
    using evalDet repDet
        SignedDivNode Pair_inject is_ArrayLengthNode_def is_IfNode_def is_NewArrayNode_def
        is_LoadFieldNode_def is_StoreFieldNode_def step.cases
    by (smt (verit) IRNode.distinct(1579) IRNode.distinct(2869) IRNode.distinct(3529) IRNode.distinct(3925) IRNode.distinct(3931) IRNode.distinct(823) IRNode.inject(49))
next
  case (SignedRemNode nid x y zero sb nxt m v1 v2 v m' h)
  then have notseq: "\<not>(is_sequential_node (kind g nid))"
    by simp
  have notend: "\<not>(is_AbstractEndNode (kind g nid))"
    by (simp add: SignedRemNode.hyps(1))
  have notif: "\<not>(is_IfNode (kind g nid))"
    by (simp add: SignedRemNode.hyps(1))
  have notref: "\<not>(is_RefNode (kind g nid))"
    by (simp add: SignedRemNode.hyps(1))
  have notload: "\<not>(is_LoadFieldNode (kind g nid))"
    by (simp add: SignedRemNode.hyps(1))
  have notstore: "\<not>(is_StoreFieldNode (kind g nid))"
    by (simp add: SignedRemNode.hyps(1))
  have notnewarray: "\<not>(is_NewArrayNode (kind g nid))"
    by (simp add: SignedRemNode.hyps(1))
  have notarraylength: "\<not>(is_ArrayLengthNode (kind g nid))"
    by (simp add: SignedRemNode.hyps(1))
  have notdivnode: "\<not>(is_SignedDivNode (kind g nid))"
    by (simp add: SignedRemNode.hyps(1))
  from notseq notend notif notref notload notstore notnewarray notarraylength notdivnode
  show ?case 
    by (smt (verit) IRNode.disc(1718) IRNode.disc(2444) IRNode.disc(3500) IRNode.disc(926) IRNode.distinct(1585) IRNode.distinct(2875) IRNode.distinct(3535) IRNode.distinct(3925) IRNode.distinct(4009) IRNode.distinct(475) IRNode.distinct(829) IRNode.inject(52) SignedRemNode.hyps(1) SignedRemNode.hyps(2) SignedRemNode.hyps(3) SignedRemNode.hyps(4) SignedRemNode.hyps(5) SignedRemNode.hyps(6) SignedRemNode.hyps(7) evalDet prod.inject repDet step.cases)  
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
    by (smt (verit) IRNode.distinct(1535) IRNode.distinct(1733) IRNode.distinct(2755) IRNode.distinct(2775) IRNode.distinct(2777) IRNode.distinct(2797) IRNode.distinct(2803) IRNode.distinct(2807) IRNode.distinct(2809) IRNode.distinct(425) IRNode.distinct(779) IRNode.inject(27) Pair_inject StaticLoadFieldNode.hyps(1) StaticLoadFieldNode.hyps(2) StaticLoadFieldNode.hyps(3) option.discI step.cases)
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
    using  evalDet step.cases repDet
        StoreFieldNode option.discI Pair_inject Value.inject(2) option.inject
        is_ArrayLengthNode_def is_IfNode_def is_LoadFieldNode_def is_NewArrayNode_def
    by (smt (verit) IRNode.distinct(1589) IRNode.distinct(2879) IRNode.distinct(3539) IRNode.distinct(3929) IRNode.distinct(4007) IRNode.distinct(4051) IRNode.distinct(833) IRNode.inject(54))

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
    using evalDet
        IRNode.inject(52) step.cases StoreFieldNode StaticStoreFieldNode.hyps option.distinct(1)
        Pair_inject repDet
    by (smt (verit) IRNode.distinct(1589) IRNode.distinct(1787) IRNode.distinct(2807) IRNode.distinct(2879) IRNode.distinct(3489) IRNode.distinct(3539) IRNode.distinct(3929) IRNode.distinct(4007) IRNode.distinct(4051) IRNode.distinct(479) IRNode.distinct(833) IRNode.inject(54))
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
  using IRNode.distinct(1607) ids_some apply presburger
  using IRNode.distinct(851) ids_some apply presburger
  
  using IRNode.distinct(1805) ids_some apply presburger
             apply (metis IRNode.distinct(3507) not_in_g)
  apply (metis IRNode.distinct(497) not_in_g)
  apply (metis IRNode.distinct(2897) not_in_g)

  apply (metis IRNode.distinct(4085) not_in_g)
  using IRNode.distinct(3557) ids_some apply presburger
  apply (metis IRNode.distinct(2825) not_in_g)
  apply (metis IRNode.distinct(3947) not_in_g)
      apply (metis IRNode.distinct(4025) not_in_g)
  using IRNode.distinct(2825) ids_some apply presburger
  apply (metis IRNode.distinct(4067) not_in_g)
   apply (metis IRNode.distinct(4067) not_in_g)
  using IRNode.disc(1952) is_EndNode.simps(62) is_AbstractEndNode.simps not_in_g
  by (metis IRNode.disc(2014) is_EndNode.simps(64))

end
