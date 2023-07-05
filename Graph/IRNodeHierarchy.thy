subsection \<open>IR Graph Node Hierarchy\<close>

theory IRNodeHierarchy
imports IRNodes
begin

text \<open>
It is helpful to introduce a node hierarchy into our formalization.
Often the GraalVM compiler relies on explicit type checks to determine
which operations to perform on a given node, we try to mimic the same
functionality by using a suite of predicate functions over the IRNode
class to determine inheritance.

As one would expect, the function is<ClassName>Type will be true if
the node parameter is a subclass of the ClassName within the GraalVM compiler.

These functions have been automatically generated from the compiler.
\<close>

(* Datatype with no parameters don't generate selectors *)
fun is_EndNode :: "IRNode \<Rightarrow> bool" where
  "is_EndNode EndNode = True" |
  "is_EndNode _ = False"

(* nodeout: isabelle-subclass *)
fun is_VirtualState :: "IRNode \<Rightarrow> bool" where
  "is_VirtualState n = ((is_FrameState n))"

fun is_BinaryArithmeticNode :: "IRNode \<Rightarrow> bool" where
  "is_BinaryArithmeticNode n = ((is_AddNode n) \<or> (is_AndNode n) \<or> (is_MulNode n) \<or> (is_OrNode n) \<or> (is_SubNode n) \<or> (is_XorNode n) \<or> (is_IntegerNormalizeCompareNode n) \<or> (is_IntegerMulHighNode n))"

fun is_ShiftNode :: "IRNode \<Rightarrow> bool" where
  "is_ShiftNode n = ((is_LeftShiftNode n) \<or> (is_RightShiftNode n) \<or> (is_UnsignedRightShiftNode n))"

fun is_BinaryNode :: "IRNode \<Rightarrow> bool" where
  "is_BinaryNode n = ((is_BinaryArithmeticNode n) \<or> (is_ShiftNode n))"

fun is_AbstractLocalNode :: "IRNode \<Rightarrow> bool" where
  "is_AbstractLocalNode n = ((is_ParameterNode n))"

fun is_IntegerConvertNode :: "IRNode \<Rightarrow> bool" where
  "is_IntegerConvertNode n = ((is_NarrowNode n) \<or> (is_SignExtendNode n) \<or> (is_ZeroExtendNode n))"

fun is_UnaryArithmeticNode :: "IRNode \<Rightarrow> bool" where
  "is_UnaryArithmeticNode n = ((is_AbsNode n) \<or> (is_NegateNode n) \<or> (is_NotNode n) \<or> (is_BitCountNode n) \<or> (is_ReverseBytesNode n))"

fun is_UnaryNode :: "IRNode \<Rightarrow> bool" where
  "is_UnaryNode n = ((is_IntegerConvertNode n) \<or> (is_UnaryArithmeticNode n))"

fun is_PhiNode :: "IRNode \<Rightarrow> bool" where
  "is_PhiNode n = ((is_ValuePhiNode n))"

fun is_FloatingGuardedNode :: "IRNode \<Rightarrow> bool" where
  "is_FloatingGuardedNode n = ((is_PiNode n))"

fun is_UnaryOpLogicNode :: "IRNode \<Rightarrow> bool" where
  "is_UnaryOpLogicNode n = ((is_IsNullNode n))"

fun is_IntegerLowerThanNode :: "IRNode \<Rightarrow> bool" where
  "is_IntegerLowerThanNode n = ((is_IntegerBelowNode n) \<or> (is_IntegerLessThanNode n))"

fun is_CompareNode :: "IRNode \<Rightarrow> bool" where
  "is_CompareNode n = ((is_IntegerEqualsNode n) \<or> (is_IntegerLowerThanNode n))"

fun is_BinaryOpLogicNode :: "IRNode \<Rightarrow> bool" where
  "is_BinaryOpLogicNode n = ((is_CompareNode n) \<or> (is_IntegerTestNode n))"

fun is_LogicNode :: "IRNode \<Rightarrow> bool" where
  "is_LogicNode n = ((is_BinaryOpLogicNode n) \<or> (is_LogicNegationNode n) \<or> (is_ShortCircuitOrNode n) \<or> (is_UnaryOpLogicNode n))"

fun is_ProxyNode :: "IRNode \<Rightarrow> bool" where
  "is_ProxyNode n = ((is_ValueProxyNode n))"

fun is_FloatingNode :: "IRNode \<Rightarrow> bool" where
  "is_FloatingNode n = ((is_AbstractLocalNode n) \<or> (is_BinaryNode n) \<or> (is_ConditionalNode n) \<or> (is_ConstantNode n) \<or> (is_FloatingGuardedNode n) \<or> (is_LogicNode n) \<or> (is_PhiNode n) \<or> (is_ProxyNode n) \<or> (is_UnaryNode n))"

fun is_AccessFieldNode :: "IRNode \<Rightarrow> bool" where
  "is_AccessFieldNode n = ((is_LoadFieldNode n) \<or> (is_StoreFieldNode n))"

fun is_AbstractNewArrayNode :: "IRNode \<Rightarrow> bool" where
  "is_AbstractNewArrayNode n = ((is_DynamicNewArrayNode n) \<or> (is_NewArrayNode n))"

fun is_AbstractNewObjectNode :: "IRNode \<Rightarrow> bool" where
  "is_AbstractNewObjectNode n = ((is_AbstractNewArrayNode n) \<or> (is_NewInstanceNode n))"

fun is_AbstractFixedGuardNode :: "IRNode \<Rightarrow> bool" where
  "is_AbstractFixedGuardNode n = (is_FixedGuardNode n)"

fun is_IntegerDivRemNode :: "IRNode \<Rightarrow> bool" where
  "is_IntegerDivRemNode n = ((is_SignedDivNode n) \<or> (is_SignedRemNode n))"

fun is_FixedBinaryNode :: "IRNode \<Rightarrow> bool" where
  "is_FixedBinaryNode n = (is_IntegerDivRemNode n)"

fun is_DeoptimizingFixedWithNextNode :: "IRNode \<Rightarrow> bool" where
  "is_DeoptimizingFixedWithNextNode n = ((is_AbstractNewObjectNode n) \<or> (is_FixedBinaryNode n) \<or> (is_AbstractFixedGuardNode n))"

fun is_AbstractMemoryCheckpoint :: "IRNode \<Rightarrow> bool" where
  "is_AbstractMemoryCheckpoint n = ((is_BytecodeExceptionNode n) \<or> (is_InvokeNode n))"

fun is_AbstractStateSplit :: "IRNode \<Rightarrow> bool" where
  "is_AbstractStateSplit n = ((is_AbstractMemoryCheckpoint n))"

fun is_AbstractMergeNode :: "IRNode \<Rightarrow> bool" where
  "is_AbstractMergeNode n = ((is_LoopBeginNode n) \<or> (is_MergeNode n))"

fun is_BeginStateSplitNode :: "IRNode \<Rightarrow> bool" where
  "is_BeginStateSplitNode n = ((is_AbstractMergeNode n) \<or> (is_ExceptionObjectNode n) \<or> (is_LoopExitNode n) \<or> (is_StartNode n))"

fun is_AbstractBeginNode :: "IRNode \<Rightarrow> bool" where
  "is_AbstractBeginNode n = ((is_BeginNode n) \<or> (is_BeginStateSplitNode n) \<or> (is_KillingBeginNode n))"

fun is_AccessArrayNode :: "IRNode \<Rightarrow> bool" where
  "is_AccessArrayNode n = ((is_LoadIndexedNode n) \<or> (is_StoreIndexedNode n))"

fun is_FixedWithNextNode :: "IRNode \<Rightarrow> bool" where
  "is_FixedWithNextNode n = ((is_AbstractBeginNode n) \<or> (is_AbstractStateSplit n) \<or> (is_AccessFieldNode n) \<or> (is_DeoptimizingFixedWithNextNode n) \<or> (is_ControlFlowAnchorNode n) \<or> (is_ArrayLengthNode n) \<or> (is_AccessArrayNode n))"

fun is_WithExceptionNode :: "IRNode \<Rightarrow> bool" where
  "is_WithExceptionNode n = ((is_InvokeWithExceptionNode n))"

fun is_ControlSplitNode :: "IRNode \<Rightarrow> bool" where
  "is_ControlSplitNode n = ((is_IfNode n) \<or> (is_WithExceptionNode n))"

fun is_ControlSinkNode :: "IRNode \<Rightarrow> bool" where
  "is_ControlSinkNode n = ((is_ReturnNode n) \<or> (is_UnwindNode n))"

fun is_AbstractEndNode :: "IRNode \<Rightarrow> bool" where
  "is_AbstractEndNode n = ((is_EndNode n) \<or> (is_LoopEndNode n))"

fun is_FixedNode :: "IRNode \<Rightarrow> bool" where
  "is_FixedNode n = ((is_AbstractEndNode n) \<or> (is_ControlSinkNode n) \<or> (is_ControlSplitNode n) \<or> (is_FixedWithNextNode n))"

fun is_CallTargetNode :: "IRNode \<Rightarrow> bool" where
  "is_CallTargetNode n = ((is_MethodCallTargetNode n))"

fun is_ValueNode :: "IRNode \<Rightarrow> bool" where
  "is_ValueNode n = ((is_CallTargetNode n) \<or> (is_FixedNode n) \<or> (is_FloatingNode n))"

fun is_Node :: "IRNode \<Rightarrow> bool" where
  "is_Node n = ((is_ValueNode n) \<or> (is_VirtualState n))"

fun is_MemoryKill :: "IRNode \<Rightarrow> bool" where
  "is_MemoryKill n = ((is_AbstractMemoryCheckpoint n))"

fun is_NarrowableArithmeticNode :: "IRNode \<Rightarrow> bool" where
  "is_NarrowableArithmeticNode n = ((is_AbsNode n) \<or> (is_AddNode n) \<or> (is_AndNode n) \<or> (is_MulNode n) \<or> (is_NegateNode n) \<or> (is_NotNode n) \<or> (is_OrNode n) \<or> (is_ShiftNode n) \<or> (is_SubNode n) \<or> (is_XorNode n))"

fun is_AnchoringNode :: "IRNode \<Rightarrow> bool" where
  "is_AnchoringNode n = ((is_AbstractBeginNode n))"

fun is_DeoptBefore :: "IRNode \<Rightarrow> bool" where
  "is_DeoptBefore n = ((is_DeoptimizingFixedWithNextNode n))"

fun is_IndirectCanonicalization :: "IRNode \<Rightarrow> bool" where
  "is_IndirectCanonicalization n = ((is_LogicNode n))"

fun is_IterableNodeType :: "IRNode \<Rightarrow> bool" where
  "is_IterableNodeType n = ((is_AbstractBeginNode n) \<or> (is_AbstractMergeNode n) \<or> (is_FrameState n) \<or> (is_IfNode n) \<or> (is_IntegerDivRemNode n) \<or> (is_InvokeWithExceptionNode n) \<or> (is_LoopBeginNode n) \<or> (is_LoopExitNode n) \<or> (is_MethodCallTargetNode n) \<or> (is_ParameterNode n) \<or> (is_ReturnNode n) \<or> (is_ShortCircuitOrNode n))"

fun is_Invoke :: "IRNode \<Rightarrow> bool" where
  "is_Invoke n = ((is_InvokeNode n) \<or> (is_InvokeWithExceptionNode n))"

fun is_Proxy :: "IRNode \<Rightarrow> bool" where
  "is_Proxy n = ((is_ProxyNode n))"

fun is_ValueProxy :: "IRNode \<Rightarrow> bool" where
  "is_ValueProxy n = ((is_PiNode n) \<or> (is_ValueProxyNode n))"

fun is_ValueNodeInterface :: "IRNode \<Rightarrow> bool" where
  "is_ValueNodeInterface n = ((is_ValueNode n))"

fun is_ArrayLengthProvider :: "IRNode \<Rightarrow> bool" where
  "is_ArrayLengthProvider n = ((is_AbstractNewArrayNode n) \<or> (is_ConstantNode n))"

fun is_StampInverter :: "IRNode \<Rightarrow> bool" where
  "is_StampInverter n = ((is_IntegerConvertNode n) \<or> (is_NegateNode n) \<or> (is_NotNode n))"

fun is_GuardingNode :: "IRNode \<Rightarrow> bool" where
  "is_GuardingNode n = ((is_AbstractBeginNode n))"

fun is_SingleMemoryKill :: "IRNode \<Rightarrow> bool" where
  "is_SingleMemoryKill n = ((is_BytecodeExceptionNode n) \<or> (is_ExceptionObjectNode n) \<or> (is_InvokeNode n) \<or> (is_InvokeWithExceptionNode n) \<or> (is_KillingBeginNode n) \<or> (is_StartNode n))"

fun is_LIRLowerable :: "IRNode \<Rightarrow> bool" where
  "is_LIRLowerable n = ((is_AbstractBeginNode n) \<or> (is_AbstractEndNode n) \<or> (is_AbstractMergeNode n) \<or> (is_BinaryOpLogicNode n) \<or> (is_CallTargetNode n) \<or> (is_ConditionalNode n) \<or> (is_ConstantNode n) \<or> (is_IfNode n) \<or> (is_InvokeNode n) \<or> (is_InvokeWithExceptionNode n) \<or> (is_IsNullNode n) \<or> (is_LoopBeginNode n) \<or> (is_PiNode n) \<or> (is_ReturnNode n) \<or> (is_SignedDivNode n) \<or> (is_SignedRemNode n) \<or> (is_UnaryOpLogicNode n) \<or> (is_UnwindNode n))"

fun is_GuardedNode :: "IRNode \<Rightarrow> bool" where
  "is_GuardedNode n = ((is_FloatingGuardedNode n))"

fun is_ArithmeticLIRLowerable :: "IRNode \<Rightarrow> bool" where
  "is_ArithmeticLIRLowerable n = ((is_AbsNode n) \<or> (is_BinaryArithmeticNode n) \<or> (is_IntegerConvertNode n) \<or> (is_NotNode n) \<or> (is_ShiftNode n) \<or> (is_UnaryArithmeticNode n))"

fun is_SwitchFoldable :: "IRNode \<Rightarrow> bool" where
  "is_SwitchFoldable n = ((is_IfNode n))"

fun is_VirtualizableAllocation :: "IRNode \<Rightarrow> bool" where
  "is_VirtualizableAllocation n = ((is_NewArrayNode n) \<or> (is_NewInstanceNode n))"

fun is_Unary :: "IRNode \<Rightarrow> bool" where
  "is_Unary n = ((is_LoadFieldNode n) \<or> (is_LogicNegationNode n) \<or> (is_UnaryNode n) \<or> (is_UnaryOpLogicNode n))"

fun is_FixedNodeInterface :: "IRNode \<Rightarrow> bool" where
  "is_FixedNodeInterface n = ((is_FixedNode n))"

fun is_BinaryCommutative :: "IRNode \<Rightarrow> bool" where
  "is_BinaryCommutative n = ((is_AddNode n) \<or> (is_AndNode n) \<or> (is_IntegerEqualsNode n) \<or> (is_MulNode n) \<or> (is_OrNode n) \<or> (is_XorNode n))"

fun is_Canonicalizable :: "IRNode \<Rightarrow> bool" where
  "is_Canonicalizable n = ((is_BytecodeExceptionNode n) \<or> (is_ConditionalNode n) \<or> (is_DynamicNewArrayNode n) \<or> (is_PhiNode n) \<or> (is_PiNode n) \<or> (is_ProxyNode n) \<or> (is_StoreFieldNode n) \<or> (is_ValueProxyNode n))"

fun is_UncheckedInterfaceProvider :: "IRNode \<Rightarrow> bool" where
  "is_UncheckedInterfaceProvider n = ((is_InvokeNode n) \<or> (is_InvokeWithExceptionNode n) \<or> (is_LoadFieldNode n) \<or> (is_ParameterNode n))"

fun is_Binary :: "IRNode \<Rightarrow> bool" where
  "is_Binary n = ((is_BinaryArithmeticNode n) \<or> (is_BinaryNode n) \<or> (is_BinaryOpLogicNode n) \<or> (is_CompareNode n) \<or> (is_FixedBinaryNode n) \<or> (is_ShortCircuitOrNode n))"

fun is_ArithmeticOperation :: "IRNode \<Rightarrow> bool" where
  "is_ArithmeticOperation n = ((is_BinaryArithmeticNode n) \<or> (is_IntegerConvertNode n) \<or> (is_ShiftNode n) \<or> (is_UnaryArithmeticNode n))"

fun is_ValueNumberable :: "IRNode \<Rightarrow> bool" where
  "is_ValueNumberable n = ((is_FloatingNode n) \<or> (is_ProxyNode n))"

fun is_Lowerable :: "IRNode \<Rightarrow> bool" where
  "is_Lowerable n = ((is_AbstractNewObjectNode n) \<or> (is_AccessFieldNode n) \<or> (is_BytecodeExceptionNode n) \<or> (is_ExceptionObjectNode n) \<or> (is_IntegerDivRemNode n) \<or> (is_UnwindNode n))"

fun is_Virtualizable :: "IRNode \<Rightarrow> bool" where
  "is_Virtualizable n = ((is_IsNullNode n) \<or> (is_LoadFieldNode n) \<or> (is_PiNode n) \<or> (is_StoreFieldNode n) \<or> (is_ValueProxyNode n))"

fun is_Simplifiable :: "IRNode \<Rightarrow> bool" where
  "is_Simplifiable n = ((is_AbstractMergeNode n) \<or> (is_BeginNode n) \<or> (is_IfNode n) \<or> (is_LoopExitNode n) \<or> (is_MethodCallTargetNode n) \<or> (is_NewArrayNode n))"

fun is_StateSplit :: "IRNode \<Rightarrow> bool" where
  "is_StateSplit n = ((is_AbstractStateSplit n) \<or> (is_BeginStateSplitNode n) \<or> (is_StoreFieldNode n))"

fun is_ConvertNode :: "IRNode \<Rightarrow> bool" where
  "is_ConvertNode n = ((is_IntegerConvertNode n))"
(* nodeout *)

fun is_sequential_node :: "IRNode \<Rightarrow> bool" where
  "is_sequential_node (StartNode _ _) = True" |
  "is_sequential_node (BeginNode _) = True" |
  "is_sequential_node (KillingBeginNode _) = True" |
  "is_sequential_node (LoopBeginNode _ _ _ _) = True" |
  "is_sequential_node (LoopExitNode _ _ _) = True" |
  "is_sequential_node (MergeNode _ _ _) = True" |
  "is_sequential_node (RefNode _) = True" |
  "is_sequential_node (ControlFlowAnchorNode _) = True" |
  "is_sequential_node _ = False"

text \<open>
The following convenience function is useful in determining if
two IRNodes are of the same type irregardless of their edges.
It will return true if both the node parameters are the same node class.
\<close>

(* nodeout: isabelle-compare-type *)
fun is_same_ir_node_type :: "IRNode \<Rightarrow> IRNode \<Rightarrow> bool" where
"is_same_ir_node_type n1 n2 = (
  ((is_AbsNode n1) \<and> (is_AbsNode n2)) \<or>
  ((is_AddNode n1) \<and> (is_AddNode n2)) \<or>
  ((is_AndNode n1) \<and> (is_AndNode n2)) \<or>
  ((is_BeginNode n1) \<and> (is_BeginNode n2)) \<or>
  ((is_BytecodeExceptionNode n1) \<and> (is_BytecodeExceptionNode n2)) \<or>
  ((is_ConditionalNode n1) \<and> (is_ConditionalNode n2)) \<or>
  ((is_ConstantNode n1) \<and> (is_ConstantNode n2)) \<or>
  ((is_DynamicNewArrayNode n1) \<and> (is_DynamicNewArrayNode n2)) \<or>
  ((is_EndNode n1) \<and> (is_EndNode n2)) \<or>
  ((is_ExceptionObjectNode n1) \<and> (is_ExceptionObjectNode n2)) \<or>
  ((is_FrameState n1) \<and> (is_FrameState n2)) \<or>
  ((is_IfNode n1) \<and> (is_IfNode n2)) \<or>
  ((is_IntegerBelowNode n1) \<and> (is_IntegerBelowNode n2)) \<or>
  ((is_IntegerEqualsNode n1) \<and> (is_IntegerEqualsNode n2)) \<or>
  ((is_IntegerLessThanNode n1) \<and> (is_IntegerLessThanNode n2)) \<or>
  ((is_InvokeNode n1) \<and> (is_InvokeNode n2)) \<or>
  ((is_InvokeWithExceptionNode n1) \<and> (is_InvokeWithExceptionNode n2)) \<or>
  ((is_IsNullNode n1) \<and> (is_IsNullNode n2)) \<or>
  ((is_KillingBeginNode n1) \<and> (is_KillingBeginNode n2)) \<or>
  ((is_LeftShiftNode n1) \<and> (is_LeftShiftNode n2)) \<or>
  ((is_LoadFieldNode n1) \<and> (is_LoadFieldNode n2)) \<or>
  ((is_LogicNegationNode n1) \<and> (is_LogicNegationNode n2)) \<or>
  ((is_LoopBeginNode n1) \<and> (is_LoopBeginNode n2)) \<or>
  ((is_LoopEndNode n1) \<and> (is_LoopEndNode n2)) \<or>
  ((is_LoopExitNode n1) \<and> (is_LoopExitNode n2)) \<or>
  ((is_MergeNode n1) \<and> (is_MergeNode n2)) \<or>
  ((is_MethodCallTargetNode n1) \<and> (is_MethodCallTargetNode n2)) \<or>
  ((is_MulNode n1) \<and> (is_MulNode n2)) \<or>
  ((is_NarrowNode n1) \<and> (is_NarrowNode n2)) \<or>
  ((is_NegateNode n1) \<and> (is_NegateNode n2)) \<or>
  ((is_NewArrayNode n1) \<and> (is_NewArrayNode n2)) \<or>
  ((is_NewInstanceNode n1) \<and> (is_NewInstanceNode n2)) \<or>
  ((is_NotNode n1) \<and> (is_NotNode n2)) \<or>
  ((is_OrNode n1) \<and> (is_OrNode n2)) \<or>
  ((is_ParameterNode n1) \<and> (is_ParameterNode n2)) \<or>
  ((is_PiNode n1) \<and> (is_PiNode n2)) \<or>
  ((is_ReturnNode n1) \<and> (is_ReturnNode n2)) \<or>
  ((is_RightShiftNode n1) \<and> (is_RightShiftNode n2)) \<or>
  ((is_ShortCircuitOrNode n1) \<and> (is_ShortCircuitOrNode n2)) \<or>
  ((is_SignedDivNode n1) \<and> (is_SignedDivNode n2)) \<or>
  ((is_SignedRemNode n1) \<and> (is_SignedRemNode n2)) \<or>
  ((is_SignExtendNode n1) \<and> (is_SignExtendNode n2)) \<or>
  ((is_StartNode n1) \<and> (is_StartNode n2)) \<or>
  ((is_StoreFieldNode n1) \<and> (is_StoreFieldNode n2)) \<or>
  ((is_SubNode n1) \<and> (is_SubNode n2)) \<or>
  ((is_UnsignedRightShiftNode n1) \<and> (is_UnsignedRightShiftNode n2)) \<or>
  ((is_UnwindNode n1) \<and> (is_UnwindNode n2)) \<or>
  ((is_ValuePhiNode n1) \<and> (is_ValuePhiNode n2)) \<or>
  ((is_ValueProxyNode n1) \<and> (is_ValueProxyNode n2)) \<or>
  ((is_XorNode n1) \<and> (is_XorNode n2)) \<or>
  ((is_ZeroExtendNode n1) \<and> (is_ZeroExtendNode n2)))"

end
