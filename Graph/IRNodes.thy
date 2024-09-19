section \<open>Graph Representation\<close>
subsection \<open>IR Graph Nodes\<close>

theory IRNodes
  imports
    Values
begin

text \<open>
The GraalVM IR is represented using a graph data structure.
Here we define the nodes that are contained within the graph.
Each node represents a Node subclass in the GraalVM compiler,
the node classes have annotated fields to indicate input and successor edges.

We represent these classes with each IRNode constructor explicitly labelling
a reference to the node IDs that it stores as inputs and successors.

The inputs\_of and successors\_of functions partition those labelled references
into input edges and successor edges of a node.

To identify each Node, we use a simple natural number index.
Zero is always the start node in a graph.
For human readability, within nodes we write 
INPUT (or special case thereof) instead of ID for input edges, and
SUCC instead of ID for control-flow successor edges.
Optional edges are handled as "INPUT option" etc.
\<close>

(* Represents the InvokeKind of a CallTargetNode *)
datatype IRInvokeKind = 
  Interface | Special | Static | Virtual

(* Mimics isDirect in the compiler *)
fun isDirect :: "IRInvokeKind \<Rightarrow> bool" where
  "isDirect Interface = False" |
  "isDirect Special = True" |
  "isDirect Static = True" |
  "isDirect Virtual = False"

(* Mimics hasReceiver in the compiler *)
fun hasReceiver :: "IRInvokeKind \<Rightarrow> bool" where
  "hasReceiver Static = False" |
  "hasReceiver _ = True"

type_synonym ID = "nat"
type_synonym INPUT = "ID"   (* InputType.Value is the default *)
type_synonym INPUT_ASSOC = "ID" (* InputType.Association *)
type_synonym INPUT_STATE = "ID" (* InputType.State *)
type_synonym INPUT_GUARD = "ID" (* InputType.Guard *)
type_synonym INPUT_COND = "ID"  (* InputType.Condition *)
type_synonym INPUT_EXT = "ID"  (* InputType.Extension *)
type_synonym SUCC = "ID"

(* nodeout: isabelle-datatypes *)
datatype (discs_sels) IRNode =
  AbsNode (ir_value: "INPUT") 
  | AddNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | AndNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | ArrayLengthNode (ir_value: "INPUT") (ir_next: "SUCC")
  | BeginNode (ir_next: "SUCC") 
  | BitCountNode (ir_value: "INPUT")
  | BytecodeExceptionNode (ir_arguments: "INPUT list") (ir_stateAfter_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | ConditionalNode (ir_condition: "INPUT_COND") (ir_trueValue: "INPUT") (ir_falseValue: "INPUT") 
  | ConstantNode (ir_const: Value) 
  | ControlFlowAnchorNode (ir_next: "SUCC")
  | DynamicNewArrayNode (ir_elementType: "INPUT") (ir_length: "INPUT") (ir_voidClass_opt: "INPUT option") (ir_stateBefore_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | EndNode 
  | ExceptionObjectNode (ir_stateAfter_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | FixedGuardNode (ir_condition: "INPUT_COND") (ir_stateBefore_opt: "INPUT_STATE option") (ir_next: "SUCC")
  | FrameState (ir_monitorIds: "INPUT_ASSOC list") (ir_outerFrameState_opt: "INPUT_STATE option") (ir_values_opt: "INPUT list option") (ir_virtualObjectMappings_opt: "INPUT_STATE list option") 
  | IfNode (ir_condition: "INPUT_COND") (ir_trueSuccessor: "SUCC") (ir_falseSuccessor: "SUCC") 
  | IntegerBelowNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | IntegerEqualsNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | IntegerLessThanNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | IntegerMulHighNode (ir_x: "INPUT") (ir_y: "INPUT")
  | IntegerNormalizeCompareNode (ir_x: "INPUT") (ir_y: "INPUT")
  | IntegerTestNode (ir_x: "INPUT") (ir_y: "INPUT")
  | InvokeNode (ir_nid: ID) (ir_callTarget: "INPUT_EXT") (ir_classInit_opt: "INPUT option") (ir_stateDuring_opt: "INPUT_STATE option") (ir_stateAfter_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | InvokeWithExceptionNode (ir_nid: ID) (ir_callTarget: "INPUT_EXT") (ir_classInit_opt: "INPUT option") (ir_stateDuring_opt: "INPUT_STATE option") (ir_stateAfter_opt: "INPUT_STATE option") (ir_next: "SUCC") (ir_exceptionEdge: "SUCC") 
  | IsNullNode (ir_value: "INPUT") 
  | KillingBeginNode (ir_next: "SUCC") 
  | LeftShiftNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | LoadFieldNode (ir_nid: ID) (ir_field: string) (ir_object_opt: "INPUT option") (ir_next: "SUCC") 
  | LoadIndexedNode (ir_index: "INPUT") (ir_guard_opt: "INPUT_GUARD option") (ir_value: "INPUT") (ir_next: "SUCC")
  | LogicNegationNode (ir_value: "INPUT_COND") 
  | LoopBeginNode (ir_ends: "INPUT_ASSOC list") (ir_overflowGuard_opt: "INPUT_GUARD option") (ir_stateAfter_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | LoopEndNode (ir_loopBegin: "INPUT_ASSOC") 
  | LoopExitNode (ir_loopBegin: "INPUT_ASSOC") (ir_stateAfter_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | MergeNode (ir_ends: "INPUT_ASSOC list") (ir_stateAfter_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | MethodCallTargetNode (ir_targetMethod: string) (ir_arguments: "INPUT list") (ir_invoke_kind: "IRInvokeKind") 
  | MulNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | NarrowNode (ir_inputBits: nat) (ir_resultBits: nat) (ir_value: "INPUT") 
  | NegateNode (ir_value: "INPUT") 
  | NewArrayNode (ir_length: "INPUT") (ir_stateBefore_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | NewInstanceNode (ir_nid: ID) (ir_instanceClass: string) (ir_stateBefore_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | NotNode (ir_value: "INPUT") 
  | OrNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | ParameterNode (ir_index: nat) 
  | PiNode (ir_object: "INPUT") (ir_guard_opt: "INPUT_GUARD option") 
  | ReturnNode (ir_result_opt: "INPUT option") (ir_memoryMap_opt: "INPUT_EXT option") 
  | ReverseBytesNode (ir_value: "INPUT")
  | RightShiftNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | ShortCircuitOrNode (ir_x: "INPUT_COND") (ir_y: "INPUT_COND") 
  | SignExtendNode (ir_inputBits: nat) (ir_resultBits: nat) (ir_value: "INPUT") 
  | SignedDivNode (ir_nid: ID) (ir_x: "INPUT") (ir_y: "INPUT") (ir_zeroCheck_opt: "INPUT_GUARD option") (ir_stateBefore_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | SignedFloatingIntegerDivNode (ir_x: "INPUT") (ir_y: "INPUT")
  | SignedFloatingIntegerRemNode (ir_x: "INPUT") (ir_y: "INPUT")
  | SignedRemNode (ir_nid: ID) (ir_x: "INPUT") (ir_y: "INPUT") (ir_zeroCheck_opt: "INPUT_GUARD option") (ir_stateBefore_opt: "INPUT_STATE option") (ir_next: "SUCC")
  | StartNode (ir_stateAfter_opt: "INPUT_STATE option") (ir_next: "SUCC") 
  | StoreFieldNode (ir_nid: ID) (ir_field: string) (ir_value: "INPUT") (ir_stateAfter_opt: "INPUT_STATE option") (ir_object_opt: "INPUT option") (ir_next: "SUCC") 
  | StoreIndexedNode (ir_storeCheck: "INPUT_GUARD option") (ir_value: ID) (ir_stateAfter_opt: "INPUT_STATE option") (ir_index: "INPUT") (ir_guard_opt: "INPUT_GUARD option") (ir_array: "INPUT") (ir_next: "SUCC")
  | SubNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | UnsignedRightShiftNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | UnwindNode (ir_exception: "INPUT") 
  | ValuePhiNode (ir_nid: ID) (ir_values: "INPUT list") (ir_merge: "INPUT_ASSOC") 
  | ValueProxyNode (ir_value: "INPUT") (ir_loopExit: "INPUT_ASSOC") 
  | XorNode (ir_x: "INPUT") (ir_y: "INPUT") 
  | ZeroExtendNode (ir_inputBits: nat) (ir_resultBits: nat) (ir_value: "INPUT") 
  | NoNode
(* nodeout *)

  (* Manually added *)
  | RefNode (ir_ref:ID)


(* Surely this must exist already?  I cannot find it in option or list theory. *)
fun opt_to_list :: "'a option \<Rightarrow> 'a list" where
  "opt_to_list None = []" |
  "opt_to_list (Some v) = [v]"

fun opt_list_to_list :: "'a list option \<Rightarrow> 'a list" where
  "opt_list_to_list None = []" |
  "opt_list_to_list (Some x) = x"

text \<open>
The following functions, inputs\_of and successors\_of, are automatically generated
from the GraalVM compiler.
Their purpose is to partition the node edges into input or successor edges.
\<close>
(* nodeout: isabelle-inputs *)
fun inputs_of :: "IRNode \<Rightarrow> ID list" where
  inputs_of_AbsNode:
  "inputs_of (AbsNode value) = [value]" |
  inputs_of_AddNode:
  "inputs_of (AddNode x y) = [x, y]" |
  inputs_of_AndNode:
  "inputs_of (AndNode x y) = [x, y]" |
  inputs_of_ArrayLengthNode:
  "inputs_of (ArrayLengthNode x next) = [x]" |
  inputs_of_BeginNode:
  "inputs_of (BeginNode next) = []" |
  inputs_of_BitCountNode:
  "inputs_of (BitCountNode value) = [value]" |
  inputs_of_BytecodeExceptionNode:
  "inputs_of (BytecodeExceptionNode arguments stateAfter next) = arguments @ (opt_to_list stateAfter)" |
  inputs_of_ConditionalNode:
  "inputs_of (ConditionalNode condition trueValue falseValue) = [condition, trueValue, falseValue]" |
  inputs_of_ConstantNode:
  "inputs_of (ConstantNode const) = []" |
  inputs_of_ControlFlowAnchorNode:
  "inputs_of (ControlFlowAnchorNode n) = []" |
  inputs_of_DynamicNewArrayNode:
  "inputs_of (DynamicNewArrayNode elementType length0 voidClass stateBefore next) = [elementType, length0] @ (opt_to_list voidClass) @ (opt_to_list stateBefore)" |
  inputs_of_EndNode:
  "inputs_of (EndNode) = []" |
  inputs_of_ExceptionObjectNode:
  "inputs_of (ExceptionObjectNode stateAfter next) = (opt_to_list stateAfter)" |
  inputs_of_FixedGuardNode:
  "inputs_of (FixedGuardNode condition stateBefore next) = [condition]" |
  inputs_of_FrameState:
  "inputs_of (FrameState monitorIds outerFrameState values virtualObjectMappings) = monitorIds @ (opt_to_list outerFrameState) @ (opt_list_to_list values) @ (opt_list_to_list virtualObjectMappings)" |
  inputs_of_IfNode:
  "inputs_of (IfNode condition trueSuccessor falseSuccessor) = [condition]" |
  inputs_of_IntegerBelowNode:
  "inputs_of (IntegerBelowNode x y) = [x, y]" |
  inputs_of_IntegerEqualsNode:
  "inputs_of (IntegerEqualsNode x y) = [x, y]" |
  inputs_of_IntegerLessThanNode:
  "inputs_of (IntegerLessThanNode x y) = [x, y]" |
  inputs_of_IntegerMulHighNode:
  "inputs_of (IntegerMulHighNode x y) = [x, y]" |
  inputs_of_IntegerNormalizeCompareNode:
  "inputs_of (IntegerNormalizeCompareNode x y) = [x, y]" |
  inputs_of_IntegerTestNode:
  "inputs_of (IntegerTestNode x y) = [x, y]" |
  inputs_of_InvokeNode:
  "inputs_of (InvokeNode nid0 callTarget classInit stateDuring stateAfter next) = callTarget # (opt_to_list classInit) @ (opt_to_list stateDuring) @ (opt_to_list stateAfter)" |
  inputs_of_InvokeWithExceptionNode:
  "inputs_of (InvokeWithExceptionNode nid0 callTarget classInit stateDuring stateAfter next exceptionEdge) = callTarget # (opt_to_list classInit) @ (opt_to_list stateDuring) @ (opt_to_list stateAfter)" |
  inputs_of_IsNullNode:
  "inputs_of (IsNullNode value) = [value]" |
  inputs_of_KillingBeginNode:
  "inputs_of (KillingBeginNode next) = []" |
  inputs_of_LeftShiftNode:
  "inputs_of (LeftShiftNode x y) = [x, y]" |
  inputs_of_LoadFieldNode:
  "inputs_of (LoadFieldNode nid0 field object next) = (opt_to_list object)" |
  inputs_of_LoadIndexedNode:
  "inputs_of (LoadIndexedNode index guard x next) = [x]" |
  inputs_of_LogicNegationNode:
  "inputs_of (LogicNegationNode value) = [value]" |
  inputs_of_LoopBeginNode:
  "inputs_of (LoopBeginNode ends overflowGuard stateAfter next) = ends @ (opt_to_list overflowGuard) @ (opt_to_list stateAfter)" |
  inputs_of_LoopEndNode:
  "inputs_of (LoopEndNode loopBegin) = [loopBegin]" |
  inputs_of_LoopExitNode:
  "inputs_of (LoopExitNode loopBegin stateAfter next) = loopBegin # (opt_to_list stateAfter)" |
  inputs_of_MergeNode:
  "inputs_of (MergeNode ends stateAfter next) = ends @ (opt_to_list stateAfter)" |
  inputs_of_MethodCallTargetNode:
  "inputs_of (MethodCallTargetNode targetMethod arguments invoke_kind) = arguments" |
  inputs_of_MulNode:
  "inputs_of (MulNode x y) = [x, y]" |
  inputs_of_NarrowNode:
  "inputs_of (NarrowNode inputBits resultBits value) = [value]" |
  inputs_of_NegateNode:
  "inputs_of (NegateNode value) = [value]" |
  inputs_of_NewArrayNode:
  "inputs_of (NewArrayNode length0 stateBefore next) = length0 # (opt_to_list stateBefore)" |
  inputs_of_NewInstanceNode:
  "inputs_of (NewInstanceNode nid0 instanceClass stateBefore next) = (opt_to_list stateBefore)" |
  inputs_of_NotNode:
  "inputs_of (NotNode value) = [value]" |
  inputs_of_OrNode:
  "inputs_of (OrNode x y) = [x, y]" |
  inputs_of_ParameterNode:
  "inputs_of (ParameterNode index) = []" |
  inputs_of_PiNode:
  "inputs_of (PiNode object guard) = object # (opt_to_list guard)" |
  inputs_of_ReturnNode:
  "inputs_of (ReturnNode result memoryMap) = (opt_to_list result) @ (opt_to_list memoryMap)" |
  inputs_of_ReverseBytesNode:
  "inputs_of (ReverseBytesNode value) = [value]" |
  inputs_of_RightShiftNode:
  "inputs_of (RightShiftNode x y) = [x, y]" |
  inputs_of_ShortCircuitOrNode:
  "inputs_of (ShortCircuitOrNode x y) = [x, y]" |
  inputs_of_SignExtendNode:
  "inputs_of (SignExtendNode inputBits resultBits value) = [value]" |
  inputs_of_SignedDivNode:
  "inputs_of (SignedDivNode nid0 x y zeroCheck stateBefore next) = [x, y] @ (opt_to_list zeroCheck) @ (opt_to_list stateBefore)" |
  inputs_of_SignedFloatingIntegerDivNode:
  "inputs_of (SignedFloatingIntegerDivNode x y) = [x, y]" |
  inputs_of_SignedFloatingIntegerRemNode:
  "inputs_of (SignedFloatingIntegerRemNode x y) = [x, y]" |
  inputs_of_SignedRemNode:
  "inputs_of (SignedRemNode nid0 x y zeroCheck stateBefore next) = [x, y] @ (opt_to_list zeroCheck) @ (opt_to_list stateBefore)" |
  inputs_of_StartNode:
  "inputs_of (StartNode stateAfter next) = (opt_to_list stateAfter)" |
  inputs_of_StoreFieldNode:
  "inputs_of (StoreFieldNode nid0 field value stateAfter object next) = value # (opt_to_list stateAfter) @ (opt_to_list object)" |
  inputs_of_StoreIndexedNode:
  "inputs_of (StoreIndexedNode check val st index guard array nid') = [val, array]" |
  inputs_of_SubNode:
  "inputs_of (SubNode x y) = [x, y]" |
  inputs_of_UnsignedRightShiftNode:
  "inputs_of (UnsignedRightShiftNode x y) = [x, y]" |
  inputs_of_UnwindNode:
  "inputs_of (UnwindNode exception) = [exception]" |
  inputs_of_ValuePhiNode:
  "inputs_of (ValuePhiNode nid0 values merge) = merge # values" |
  inputs_of_ValueProxyNode:
  "inputs_of (ValueProxyNode value loopExit) = [value, loopExit]" |
  inputs_of_XorNode:
  "inputs_of (XorNode x y) = [x, y]" |
  inputs_of_ZeroExtendNode:
  "inputs_of (ZeroExtendNode inputBits resultBits value) = [value]" |
  inputs_of_NoNode: "inputs_of (NoNode) = []" |
(* nodeout *)

  inputs_of_RefNode: "inputs_of (RefNode ref) = [ref]"

(* nodeout: isabelle-succs *)
fun successors_of :: "IRNode \<Rightarrow> ID list" where
  successors_of_AbsNode:
  "successors_of (AbsNode value) = []" |
  successors_of_AddNode:
  "successors_of (AddNode x y) = []" |
  successors_of_AndNode:
  "successors_of (AndNode x y) = []" |
  successors_of_ArrayLengthNode:
  "successors_of (ArrayLengthNode x next) = [next]" |
  successors_of_BeginNode:
  "successors_of (BeginNode next) = [next]" |
  successors_of_BitCountNode:
  "successors_of (BitCountNode value) = []" |
  successors_of_BytecodeExceptionNode:
  "successors_of (BytecodeExceptionNode arguments stateAfter next) = [next]" |
  successors_of_ConditionalNode:
  "successors_of (ConditionalNode condition trueValue falseValue) = []" |
  successors_of_ConstantNode:
  "successors_of (ConstantNode const) = []" |
  successors_of_ControlFlowAnchorNode:
  "successors_of (ControlFlowAnchorNode next) = [next]" |
  successors_of_DynamicNewArrayNode:
  "successors_of (DynamicNewArrayNode elementType length0 voidClass stateBefore next) = [next]" |
  successors_of_EndNode:
  "successors_of (EndNode) = []" |
  successors_of_ExceptionObjectNode:
  "successors_of (ExceptionObjectNode stateAfter next) = [next]" |
  successors_of_FixedGuardNode:
  "successors_of (FixedGuardNode condition stateBefore next) = [next]" |
  successors_of_FrameState:
  "successors_of (FrameState monitorIds outerFrameState values virtualObjectMappings) = []" |
  successors_of_IfNode:
  "successors_of (IfNode condition trueSuccessor falseSuccessor) = [trueSuccessor, falseSuccessor]" |
  successors_of_IntegerBelowNode:
  "successors_of (IntegerBelowNode x y) = []" |
  successors_of_IntegerEqualsNode:
  "successors_of (IntegerEqualsNode x y) = []" |
  successors_of_IntegerLessThanNode:
  "successors_of (IntegerLessThanNode x y) = []" |
  successors_of_IntegerMulHighNode:
  "successors_of (IntegerMulHighNode x y) = []" |
  successors_of_IntegerNormalizeCompareNode:
  "successors_of (IntegerNormalizeCompareNode x y) = []" |
  successors_of_IntegerTestNode:
  "successors_of (IntegerTestNode x y) = []" |
  successors_of_InvokeNode:
  "successors_of (InvokeNode nid0 callTarget classInit stateDuring stateAfter next) = [next]" |
  successors_of_InvokeWithExceptionNode:
  "successors_of (InvokeWithExceptionNode nid0 callTarget classInit stateDuring stateAfter next exceptionEdge) = [next, exceptionEdge]" |
  successors_of_IsNullNode:
  "successors_of (IsNullNode value) = []" |
  successors_of_KillingBeginNode:
  "successors_of (KillingBeginNode next) = [next]" |
  successors_of_LeftShiftNode:
  "successors_of (LeftShiftNode x y) = []" |
  successors_of_LoadFieldNode:
  "successors_of (LoadFieldNode nid0 field object next) = [next]" |
  successors_of_LoadIndexedNode:
  "successors_of (LoadIndexedNode index guard x next) = [next]" |
  successors_of_LogicNegationNode:
  "successors_of (LogicNegationNode value) = []" |
  successors_of_LoopBeginNode:
  "successors_of (LoopBeginNode ends overflowGuard stateAfter next) = [next]" |
  successors_of_LoopEndNode:
  "successors_of (LoopEndNode loopBegin) = []" |
  successors_of_LoopExitNode:
  "successors_of (LoopExitNode loopBegin stateAfter next) = [next]" |
  successors_of_MergeNode:
  "successors_of (MergeNode ends stateAfter next) = [next]" |
  successors_of_MethodCallTargetNode:
  "successors_of (MethodCallTargetNode targetMethod arguments invoke_kind) = []" |
  successors_of_MulNode:
  "successors_of (MulNode x y) = []" |
  successors_of_NarrowNode:
  "successors_of (NarrowNode inputBits resultBits value) = []" |
  successors_of_NegateNode:
  "successors_of (NegateNode value) = []" |
  successors_of_NewArrayNode:
  "successors_of (NewArrayNode length0 stateBefore next) = [next]" |
  successors_of_NewInstanceNode:
  "successors_of (NewInstanceNode nid0 instanceClass stateBefore next) = [next]" |
  successors_of_NotNode:
  "successors_of (NotNode value) = []" |
  successors_of_OrNode:
  "successors_of (OrNode x y) = []" |
  successors_of_ParameterNode:
  "successors_of (ParameterNode index) = []" |
  successors_of_PiNode:
  "successors_of (PiNode object guard) = []" |
  successors_of_ReturnNode:
  "successors_of (ReturnNode result memoryMap) = []" |
  successors_of_ReverseBytesNode:
  "successors_of (ReverseBytesNode value) = []" |
  successors_of_RightShiftNode:
  "successors_of (RightShiftNode x y) = []" |
  successors_of_ShortCircuitOrNode:
  "successors_of (ShortCircuitOrNode x y) = []" |
  successors_of_SignExtendNode:
  "successors_of (SignExtendNode inputBits resultBits value) = []" |
  successors_of_SignedDivNode:
  "successors_of (SignedDivNode nid0 x y zeroCheck stateBefore next) = [next]" |
  successors_of_SignedFloatingIntegerDivNode:
  "successors_of (SignedFloatingIntegerDivNode x y) = []" |
  successors_of_SignedFloatingIntegerRemNode:
  "successors_of (SignedFloatingIntegerRemNode x y) = []" |
  successors_of_SignedRemNode:
  "successors_of (SignedRemNode nid0 x y zeroCheck stateBefore next) = [next]" |
  successors_of_StartNode:
  "successors_of (StartNode stateAfter next) = [next]" |
  successors_of_StoreFieldNode:
  "successors_of (StoreFieldNode nid0 field value stateAfter object next) = [next]" |
  successors_of_StoreIndexedNode:
  "successors_of (StoreIndexedNode check val st index guard array next) = [next]" |
  successors_of_SubNode:
  "successors_of (SubNode x y) = []" |
  successors_of_UnsignedRightShiftNode:
  "successors_of (UnsignedRightShiftNode x y) = []" |
  successors_of_UnwindNode:
  "successors_of (UnwindNode exception) = []" |
  successors_of_ValuePhiNode:
  "successors_of (ValuePhiNode nid0 values merge) = []" |
  successors_of_ValueProxyNode:
  "successors_of (ValueProxyNode value loopExit) = []" |
  successors_of_XorNode:
  "successors_of (XorNode x y) = []" |
  successors_of_ZeroExtendNode:
  "successors_of (ZeroExtendNode inputBits resultBits value) = []" |
  successors_of_NoNode: "successors_of (NoNode) = []" |
(* nodeout *)

  successors_of_RefNode: "successors_of (RefNode ref) = [ref]"

lemma "inputs_of (FrameState x (Some y) (Some z) None) = x @ [y] @ z"
  by simp

lemma "successors_of (FrameState x (Some y) (Some z) None) = []"
  by simp

lemma "inputs_of (IfNode c t f) = [c]"
  by simp

lemma "successors_of (IfNode c t f) = [t, f]"
  by simp

lemma "inputs_of (EndNode) = [] \<and> successors_of (EndNode) = []"
  by simp

end

