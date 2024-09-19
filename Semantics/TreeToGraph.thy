section \<open>Tree to Graph\<close>

theory TreeToGraph
  imports 
    Semantics.IRTreeEval
    Graph.IRGraph
begin

subsection \<open>Subgraph to Data-flow Tree\<close>

fun find_node_and_stamp :: "IRGraph \<Rightarrow> (IRNode \<times> Stamp) \<Rightarrow> ID option" where
  "find_node_and_stamp g (n,s) =
     find (\<lambda>i. kind g i = n \<and> stamp g i = s) (sorted_list_of_set(ids g))"

export_code find_node_and_stamp

(* These kinds of nodes are evaluated during the control flow, so are already in MapState. *)
fun is_preevaluated :: "IRNode \<Rightarrow> bool" where
  "is_preevaluated (InvokeNode n _ _ _ _ _) = True" |
  "is_preevaluated (InvokeWithExceptionNode n _ _ _ _ _ _) = True" |
  "is_preevaluated (NewInstanceNode n _ _ _) = True" |
  "is_preevaluated (LoadFieldNode n _ _ _) = True" |
  "is_preevaluated (SignedDivNode n _ _ _ _ _) = True" |
  "is_preevaluated (SignedRemNode n _ _ _ _ _) = True" |
  "is_preevaluated (ValuePhiNode n _ _) = True" |
  "is_preevaluated (BytecodeExceptionNode n _ _) = True" |
  "is_preevaluated (NewArrayNode n _ _) = True" |
  "is_preevaluated (ArrayLengthNode n _) = True" |
  "is_preevaluated (LoadIndexedNode n _ _ _) = True" |
  "is_preevaluated (StoreIndexedNode n _ _ _ _ _ _) = True" |
  "is_preevaluated _ = False"

inductive
  rep :: "IRGraph \<Rightarrow> ID \<Rightarrow> IRExpr \<Rightarrow> bool" ("_ \<turnstile> _ \<simeq> _" 55)
  for g where

  ConstantNode:
  "\<lbrakk>kind g n = ConstantNode c\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> (ConstantExpr c)" |

  ParameterNode:
  "\<lbrakk>kind g n = ParameterNode i;
    stamp g n = s\<rbrakk>
    \<Longrightarrow> g  \<turnstile> n \<simeq> (ParameterExpr i s)" |

  ConditionalNode:
  "\<lbrakk>kind g n = ConditionalNode c t f;
    g \<turnstile> c \<simeq> ce;
    g \<turnstile> t \<simeq> te;
    g \<turnstile> f \<simeq> fe\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> (ConditionalExpr ce te fe)" |

(* Unary nodes *)
  AbsNode:
  "\<lbrakk>kind g n = AbsNode x;
    g \<turnstile> x \<simeq> xe\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> (UnaryExpr UnaryAbs xe)" |

  ReverseBytesNode:
  "\<lbrakk>kind g n = ReverseBytesNode x;
    g \<turnstile> x \<simeq> xe\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> (UnaryExpr UnaryReverseBytes xe)" |

  BitCountNode:
  "\<lbrakk>kind g n = BitCountNode x;
    g \<turnstile> x \<simeq> xe\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> (UnaryExpr UnaryBitCount xe)" |

  NotNode:
  "\<lbrakk>kind g n = NotNode x;
    g \<turnstile> x \<simeq> xe\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> (UnaryExpr UnaryNot xe)" |

  NegateNode:
  "\<lbrakk>kind g n = NegateNode x;
    g \<turnstile> x \<simeq> xe\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> (UnaryExpr UnaryNeg xe)" |

  LogicNegationNode:
  "\<lbrakk>kind g n = LogicNegationNode x;
    g \<turnstile> x \<simeq> xe\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> (UnaryExpr UnaryLogicNegation xe)" |

(* Binary nodes *)
  AddNode:
  "\<lbrakk>kind g n = AddNode x y;
    g \<turnstile> x \<simeq> xe;
    g \<turnstile> y \<simeq> ye\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> (BinaryExpr BinAdd xe ye)" |

  MulNode:
  "\<lbrakk>kind g n = MulNode x y;
    g \<turnstile> x \<simeq> xe;
    g \<turnstile> y \<simeq> ye\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> (BinaryExpr BinMul xe ye)" |

  DivNode:
  "\<lbrakk>kind g n = SignedFloatingIntegerDivNode x y;
    g \<turnstile> x \<simeq> xe;
    g \<turnstile> y \<simeq> ye\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> (BinaryExpr BinDiv xe ye)" |

  ModNode:
  "\<lbrakk>kind g n = SignedFloatingIntegerRemNode x y;
    g \<turnstile> x \<simeq> xe;
    g \<turnstile> y \<simeq> ye\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> (BinaryExpr BinMod xe ye)" |

  SubNode:
  "\<lbrakk>kind g n = SubNode x y;
    g \<turnstile> x \<simeq> xe;
    g \<turnstile> y \<simeq> ye\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> (BinaryExpr BinSub xe ye)" |

  AndNode:
  "\<lbrakk>kind g n = AndNode x y;
    g \<turnstile> x \<simeq> xe;
    g \<turnstile> y \<simeq> ye\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> (BinaryExpr BinAnd xe ye)" |

  OrNode:
  "\<lbrakk>kind g n = OrNode x y;
    g \<turnstile> x \<simeq> xe;
    g \<turnstile> y \<simeq> ye\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> (BinaryExpr BinOr xe ye)" |

  XorNode:
  "\<lbrakk>kind g n = XorNode x y;
    g \<turnstile> x \<simeq> xe;
    g \<turnstile> y \<simeq> ye\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> (BinaryExpr BinXor xe ye)" |

  ShortCircuitOrNode:
  "\<lbrakk>kind g n = ShortCircuitOrNode x y;
    g \<turnstile> x \<simeq> xe;
    g \<turnstile> y \<simeq> ye\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> (BinaryExpr BinShortCircuitOr xe ye)" |

  LeftShiftNode:
  "\<lbrakk>kind g n = LeftShiftNode x y;
    g \<turnstile> x \<simeq> xe;
    g \<turnstile> y \<simeq> ye\<rbrakk>
   \<Longrightarrow> g \<turnstile> n \<simeq> (BinaryExpr BinLeftShift xe ye)" |

  RightShiftNode:
  "\<lbrakk>kind g n = RightShiftNode x y;
    g \<turnstile> x \<simeq> xe;
    g \<turnstile> y \<simeq> ye\<rbrakk>
   \<Longrightarrow> g \<turnstile> n \<simeq> (BinaryExpr BinRightShift xe ye)" |

  UnsignedRightShiftNode:
  "\<lbrakk>kind g n = UnsignedRightShiftNode x y;
    g \<turnstile> x \<simeq> xe;
    g \<turnstile> y \<simeq> ye\<rbrakk>
   \<Longrightarrow> g \<turnstile> n \<simeq> (BinaryExpr BinURightShift xe ye)" |

  IntegerBelowNode:
  "\<lbrakk>kind g n = IntegerBelowNode x y;
    g \<turnstile> x \<simeq> xe;
    g \<turnstile> y \<simeq> ye\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> (BinaryExpr BinIntegerBelow xe ye)" |

  IntegerEqualsNode:
  "\<lbrakk>kind g n = IntegerEqualsNode x y;
    g \<turnstile> x \<simeq> xe;
    g \<turnstile> y \<simeq> ye\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> (BinaryExpr BinIntegerEquals xe ye)" |

  IntegerLessThanNode:
  "\<lbrakk>kind g n = IntegerLessThanNode x y;
    g \<turnstile> x \<simeq> xe;
    g \<turnstile> y \<simeq> ye\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> (BinaryExpr BinIntegerLessThan xe ye)" |

  IntegerTestNode:
  "\<lbrakk>kind g n = IntegerTestNode x y;
    g \<turnstile> x \<simeq> xe;
    g \<turnstile> y \<simeq> ye\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> (BinaryExpr BinIntegerTest xe ye)" |

  IntegerNormalizeCompareNode:
  "\<lbrakk>kind g n = IntegerNormalizeCompareNode x y;
    g \<turnstile> x \<simeq> xe;
    g \<turnstile> y \<simeq> ye\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> (BinaryExpr BinIntegerNormalizeCompare xe ye)" |

  IntegerMulHighNode:
  "\<lbrakk>kind g n = IntegerMulHighNode x y;
    g \<turnstile> x \<simeq> xe;
    g \<turnstile> y \<simeq> ye\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> (BinaryExpr BinIntegerMulHigh xe ye)" |

(* Convert Nodes *)
  NarrowNode:
  "\<lbrakk>kind g n = NarrowNode inputBits resultBits x;
    g \<turnstile> x \<simeq> xe\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> (UnaryExpr (UnaryNarrow inputBits resultBits) xe)" |

  SignExtendNode:
  "\<lbrakk>kind g n = SignExtendNode inputBits resultBits x;
    g \<turnstile> x \<simeq> xe\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> (UnaryExpr (UnarySignExtend inputBits resultBits) xe)" |

  ZeroExtendNode:
  "\<lbrakk>kind g n = ZeroExtendNode inputBits resultBits x;
    g \<turnstile> x \<simeq> xe\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> (UnaryExpr (UnaryZeroExtend inputBits resultBits) xe)" |

(* Leaf Node
    TODO: For now, BytecodeExceptionNode is treated as a LeafNode.
*)
  LeafNode:
  "\<lbrakk>is_preevaluated (kind g n);
    stamp g n = s\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> (LeafExpr n s)" |

(* TODO: For now, ignore narrowing. *)
  PiNode:
  "\<lbrakk>kind g n = PiNode n' guard;
    g \<turnstile> n' \<simeq> e\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> e" |

(* Ref Node *)
  RefNode:
  "\<lbrakk>kind g n = RefNode n';
    g \<turnstile> n' \<simeq> e\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> e" |

(* IsNull Node *)
  IsNullNode:
  "\<lbrakk>kind g n = IsNullNode v;
    g \<turnstile> v \<simeq> lfn\<rbrakk>
    \<Longrightarrow> g \<turnstile> n \<simeq> (UnaryExpr UnaryIsNull lfn)"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as exprE) rep .

inductive
  replist :: "IRGraph \<Rightarrow> ID list \<Rightarrow> IRExpr list \<Rightarrow> bool" ("_ \<turnstile> _ \<simeq>\<^sub>L _" 55)
  for g where

  RepNil:
  "g \<turnstile> [] \<simeq>\<^sub>L []" |

  RepCons:
  "\<lbrakk>g \<turnstile> x \<simeq> xe;
    g \<turnstile> xs \<simeq>\<^sub>L xse\<rbrakk>
    \<Longrightarrow> g \<turnstile> x#xs \<simeq>\<^sub>L xe#xse"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as exprListE) replist .

definition wf_term_graph :: "MapState \<Rightarrow> Params \<Rightarrow> IRGraph \<Rightarrow> ID \<Rightarrow> bool" where
  "wf_term_graph m p g n = (\<exists> e. (g \<turnstile> n \<simeq> e) \<and> (\<exists> v. ([m, p] \<turnstile> e \<mapsto> v)))"

values "{t. eg2_sq \<turnstile> 4 \<simeq> t}"

inductive_cases ConstantNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (ConstantExpr c)"
inductive_cases ParameterNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (ParameterExpr i s)"
inductive_cases ConditionalNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (ConditionalExpr ce te fe)"
inductive_cases AbsNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (UnaryExpr UnaryAbs xe)"
inductive_cases ReverseBytesNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (UnaryExpr UnaryReverseBytes xe)"
inductive_cases BitCountNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (UnaryExpr UnaryBitCount xe)"
inductive_cases NotNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (UnaryExpr UnaryNot xe)"
inductive_cases NegateNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (UnaryExpr UnaryNeg xe)"
inductive_cases LogicNegationNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (UnaryExpr UnaryLogicNegation xe)"
inductive_cases AddNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (BinaryExpr BinAdd xe ye)"
inductive_cases MulNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (BinaryExpr BinMul xe ye)"
inductive_cases DivNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (BinaryExpr BinDiv xe ye)"
inductive_cases ModNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (BinaryExpr BinMod xe ye)"
inductive_cases SubNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (BinaryExpr BinSub xe ye)"
inductive_cases AndNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (BinaryExpr BinAnd xe ye)"
inductive_cases OrNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (BinaryExpr BinOr xe ye)"
inductive_cases XorNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (BinaryExpr BinXor xe ye)"
inductive_cases ShortCircuitOrE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (BinaryExpr BinShortCircuitOr xe ye)"
inductive_cases LeftShiftNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (BinaryExpr BinLeftShift xe ye)"
inductive_cases RightShiftNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (BinaryExpr BinRightShift xe ye)"
inductive_cases UnsignedRightShiftNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (BinaryExpr BinURightShift xe ye)"
inductive_cases IntegerBelowNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (BinaryExpr BinIntegerBelow xe ye)"
inductive_cases IntegerEqualsNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (BinaryExpr BinIntegerEquals xe ye)"
inductive_cases IntegerLessThanNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (BinaryExpr BinIntegerLessThan xe ye)"
inductive_cases IntegerMulHighNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (BinaryExpr BinIntegerMulHigh xe ye)"
inductive_cases IntegerTestNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (BinaryExpr BinIntegerTest xe ye)"
inductive_cases IntegerNormalizeCompareNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (BinaryExpr BinIntegerNormalizeCompare xe ye)"
inductive_cases NarrowNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (UnaryExpr (UnaryNarrow ib rb) xe)"
inductive_cases SignExtendNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (UnaryExpr (UnarySignExtend ib rb) xe)"
inductive_cases ZeroExtendNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (UnaryExpr (UnaryZeroExtend ib rb) xe)"
inductive_cases LeafNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (LeafExpr n s)"
inductive_cases IsNullNodeE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (UnaryExpr UnaryIsNull lfn)"

(* group those forward rules into a named set *)
lemmas RepE\<^marker>\<open>tag invisible\<close> = 
  ConstantNodeE
  ParameterNodeE
  ConditionalNodeE
  AbsNodeE
  ReverseBytesNodeE
  BitCountNodeE
  NotNodeE
  NegateNodeE
  LogicNegationNodeE
  AddNodeE
  MulNodeE
  DivNodeE
  ModNodeE
  SubNodeE
  AndNodeE
  OrNodeE
  XorNodeE
  ShortCircuitOrE
  LeftShiftNodeE
  RightShiftNodeE
  UnsignedRightShiftNodeE
  IntegerBelowNodeE
  IntegerEqualsNodeE
  IntegerLessThanNodeE
  IntegerMulHighNodeE
  IntegerTestNodeE
  IntegerNormalizeCompareNodeE
  NarrowNodeE
  SignExtendNodeE
  ZeroExtendNodeE
  LeafNodeE
  IsNullNodeE 

subsection \<open>Data-flow Tree to Subgraph\<close>

fun unary_node :: "IRUnaryOp \<Rightarrow> ID \<Rightarrow> IRNode" where
  "unary_node UnaryAbs v = AbsNode v" |
  "unary_node UnaryNot v = NotNode v" |
  "unary_node UnaryNeg v = NegateNode v" |
  "unary_node UnaryLogicNegation v = LogicNegationNode v" |
  "unary_node (UnaryNarrow ib rb) v = NarrowNode ib rb v" |
  "unary_node (UnarySignExtend ib rb) v = SignExtendNode ib rb v" |
  "unary_node (UnaryZeroExtend ib rb) v = ZeroExtendNode ib rb v" |
  "unary_node UnaryIsNull v = IsNullNode v" |
  "unary_node UnaryReverseBytes v = ReverseBytesNode v" |
  "unary_node UnaryBitCount v = BitCountNode v"

(* Creates the appropriate IRNode for a given binary operator. *)
fun bin_node :: "IRBinaryOp \<Rightarrow> ID \<Rightarrow> ID \<Rightarrow> IRNode" where
  "bin_node BinAdd x y = AddNode x y" |
  "bin_node BinMul x y = MulNode x y" |
  "bin_node BinDiv x y = SignedFloatingIntegerDivNode x y" |
  "bin_node BinMod x y = SignedFloatingIntegerRemNode x y" |
  "bin_node BinSub x y = SubNode x y" |
  "bin_node BinAnd x y = AndNode x y" |
  "bin_node BinOr  x y = OrNode x y" |
  "bin_node BinXor x y = XorNode x y" |
  "bin_node BinShortCircuitOr x y = ShortCircuitOrNode x y" |
  "bin_node BinLeftShift x y = LeftShiftNode x y" |
  "bin_node BinRightShift x y = RightShiftNode x y" |
  "bin_node BinURightShift x y = UnsignedRightShiftNode x y" |
  "bin_node BinIntegerEquals x y = IntegerEqualsNode x y" |
  "bin_node BinIntegerLessThan x y = IntegerLessThanNode x y" |
  "bin_node BinIntegerBelow x y = IntegerBelowNode x y" |
  "bin_node BinIntegerTest x y = IntegerTestNode x y" |
  "bin_node BinIntegerNormalizeCompare x y = IntegerNormalizeCompareNode x y" |
  "bin_node BinIntegerMulHigh x y = IntegerMulHighNode x y"

inductive fresh_id :: "IRGraph \<Rightarrow> ID \<Rightarrow> bool" where
  "n \<notin> ids g \<Longrightarrow> fresh_id g n"

code_pred fresh_id .

(* This generates a specific fresh ID (max+1), in a code-friendly way. *)
fun get_fresh_id :: "IRGraph \<Rightarrow> ID" where
(* Previous attempts - cannot generate code due to nat not Enum. 
  "get_fresh_id g = 100"
  "get_fresh_id g = (ffold max (0::nat) (f_ids g))"
  "get_fresh_id g = fst(last(as_list g))"
  "get_fresh_id g = last(sorted_list_of_set (dom (Rep_IRGraph g)))"
*)
  "get_fresh_id g = last(sorted_list_of_set(ids g)) + 1"

export_code get_fresh_id
(* these examples return 6 and 7 respectively *)
value "get_fresh_id eg2_sq"
value "get_fresh_id (add_node 6 (ParameterNode 2, default_stamp) eg2_sq)"

(* Second version of tree insertion into graph:

      g \<triangleleft> expr \<leadsto> (g',n) re-inserts expr into g and returns the new root n.

   This means that we can try to re-use existing nodes by finding node IDs bottom-up.
*)
inductive
  unrep :: "IRGraph \<Rightarrow> IRExpr \<Rightarrow> (IRGraph \<times> ID) \<Rightarrow> bool" ("_ \<oplus> _ \<leadsto> _" 55)
   where

  ConstantNodeSame:
  "\<lbrakk>find_node_and_stamp g (ConstantNode c, constantAsStamp c) = Some n\<rbrakk>
    \<Longrightarrow> g \<oplus> (ConstantExpr c) \<leadsto> (g, n)" |

  ConstantNodeNew:
  "\<lbrakk>find_node_and_stamp g (ConstantNode c, constantAsStamp c) = None;
    n = get_fresh_id g;
    g' = add_node n (ConstantNode c, constantAsStamp c) g \<rbrakk>
    \<Longrightarrow> g \<oplus> (ConstantExpr c) \<leadsto> (g', n)" |

  ParameterNodeSame:
  "\<lbrakk>find_node_and_stamp g (ParameterNode i, s) = Some n\<rbrakk>
    \<Longrightarrow> g \<oplus> (ParameterExpr i s) \<leadsto> (g, n)" |

  ParameterNodeNew:
  "\<lbrakk>find_node_and_stamp g (ParameterNode i, s) = None;
    n = get_fresh_id g;
    g' = add_node n (ParameterNode i, s) g\<rbrakk>
    \<Longrightarrow> g \<oplus> (ParameterExpr i s) \<leadsto> (g', n)" |

  ConditionalNodeSame:
  "\<lbrakk>find_node_and_stamp g4 (ConditionalNode c t f, s') = Some n;
    g \<oplus> ce \<leadsto> (g2, c);
    g2 \<oplus> te \<leadsto> (g3, t);
    g3 \<oplus> fe \<leadsto> (g4, f);
    s' = meet (stamp g4 t) (stamp g4 f)\<rbrakk>
    \<Longrightarrow> g \<oplus> (ConditionalExpr ce te fe) \<leadsto> (g4, n)" |

  ConditionalNodeNew:
  "\<lbrakk>find_node_and_stamp g4 (ConditionalNode c t f, s') = None;
    g \<oplus> ce \<leadsto> (g2, c);
    g2 \<oplus> te \<leadsto> (g3, t);
    g3 \<oplus> fe \<leadsto> (g4, f);
    s' = meet (stamp g4 t) (stamp g4 f);
    n = get_fresh_id g4;
    g' = add_node n (ConditionalNode c t f, s') g4\<rbrakk>
    \<Longrightarrow> g \<oplus> (ConditionalExpr ce te fe) \<leadsto> (g', n)" |

  UnaryNodeSame:
  "\<lbrakk>find_node_and_stamp g2 (unary_node op x, s') = Some n;
    g \<oplus> xe \<leadsto> (g2, x);
    s' = stamp_unary op (stamp g2 x)\<rbrakk>
    \<Longrightarrow> g \<oplus> (UnaryExpr op xe) \<leadsto> (g2, n)" |

  UnaryNodeNew:
  "\<lbrakk>find_node_and_stamp g2 (unary_node op x, s') = None;
    g \<oplus> xe \<leadsto> (g2, x);
    s' = stamp_unary op (stamp g2 x);
    n = get_fresh_id g2;
    g' = add_node n (unary_node op x, s') g2\<rbrakk>
    \<Longrightarrow> g \<oplus> (UnaryExpr op xe) \<leadsto> (g', n)" |

  BinaryNodeSame:
  "\<lbrakk>find_node_and_stamp g3 (bin_node op x y, s') = Some n;
    g \<oplus> xe \<leadsto> (g2, x);
    g2 \<oplus> ye \<leadsto> (g3, y);
    s' = stamp_binary op (stamp g3 x) (stamp g3 y)\<rbrakk>
    \<Longrightarrow> g \<oplus> (BinaryExpr op xe ye) \<leadsto> (g3, n)" |

  BinaryNodeNew:
  "\<lbrakk>find_node_and_stamp g3 (bin_node op x y, s') = None;
    g \<oplus> xe \<leadsto> (g2, x);
    g2 \<oplus> ye \<leadsto> (g3, y);
    s' = stamp_binary op (stamp g3 x) (stamp g3 y);
    n = get_fresh_id g3;
    g' = add_node n (bin_node op x y, s') g3\<rbrakk>
    \<Longrightarrow> g \<oplus> (BinaryExpr op xe ye) \<leadsto> (g', n)" |

  AllLeafNodes:
  "\<lbrakk>stamp g n = s;
    is_preevaluated (kind g n)\<rbrakk>
    \<Longrightarrow> g \<oplus> (LeafExpr n s) \<leadsto> (g, n)"

(*  UnrepNil:
  "g \<triangleleft>\<^sub>L [] \<leadsto> (g, [])" |

(* TODO: this will fail for [xe,ye] where they are not equal.
         Figure out how to generate code for this?
*)
  UnrepCons:
  "\<lbrakk>g \<triangleleft> xe \<leadsto> (g2, x);
    g2 \<triangleleft>\<^sub>L xes \<leadsto> (g3, xs)\<rbrakk>
    \<Longrightarrow> g \<triangleleft>\<^sub>L (xe#xes) \<leadsto> (g3, x#xs)"*)

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as unrepE)
(*
  [show_steps,show_mode_inference,show_intermediate_results] 
*)  unrep .

text_raw \<open>\Snip{unrepRules}%
\begin{center}
@{thm[mode=Rule] unrep.ConstantNodeSame [no_vars]}\\[8px]
@{thm[mode=Rule] unrep.ConstantNodeNew [no_vars]}\\[8px]
@{thm[mode=Rule] unrep.ParameterNodeSame [no_vars]}\\[8px]
@{thm[mode=Rule] unrep.ParameterNodeNew [no_vars]}\\[8px]
@{thm[mode=Rule] unrep.ConditionalNodeSame [no_vars]}\\[8px]
@{thm[mode=Rule] unrep.ConditionalNodeNew [no_vars]}\\[8px]
@{thm[mode=Rule] unrep.BinaryNodeSame [no_vars]}\\[8px]
@{thm[mode=Rule] unrep.BinaryNodeNew [no_vars]}\\[8px]
@{thm[mode=Rule] unrep.UnaryNodeSame [no_vars]}\\[8px]
@{thm[mode=Rule] unrep.UnaryNodeNew [no_vars]}\\[8px]
@{thm[mode=Rule] unrep.AllLeafNodes [no_vars]}\\[8px]
\end{center}
\EndSnip\<close>

(*
instantiation IRGraph :: equal begin

definition "(g1 = g2) \<longleftrightarrow> 
              (f_ids g1 = f_ids g2 \<and>
               (\<forall>n. (n \<in> ids g1 \<Longrightarrow> (Rep_IRGraph g1 n = Rep_IRGraph g2 n))))"
instance proof 
  fix x y :: IRGraph
  show "x = y \<longleftrightarrow> x \<le> y \<and> \<not> (y \<le> x)" by (simp add: equiv_exprs_def; auto)
  show "x \<le> x" by simp
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by simp 
qed
end
*)

values "{(n, g) . (eg2_sq \<oplus> sq_param0 \<leadsto> (g, n))}"

subsection \<open>Lift Data-flow Tree Semantics\<close>

definition encodeeval :: "IRGraph \<Rightarrow> MapState \<Rightarrow> Params \<Rightarrow> ID \<Rightarrow> Value \<Rightarrow> bool" 
  ("[_,_,_] \<turnstile> _ \<mapsto> _" 50)
  where
  "encodeeval g m p n v = (\<exists> e. (g \<turnstile> n \<simeq> e) \<and> ([m,p] \<turnstile> e \<mapsto> v))"

subsection \<open>Graph Refinement\<close>

definition graph_represents_expression :: "IRGraph \<Rightarrow> ID \<Rightarrow> IRExpr \<Rightarrow> bool" 
  ("_ \<turnstile> _ \<unlhd> _" 50)
  where
  "(g \<turnstile> n \<unlhd> e) = (\<exists>e' . (g \<turnstile> n \<simeq> e') \<and> (e' \<le> e))"

definition graph_refinement :: "IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool" where
  "graph_refinement g\<^sub>1 g\<^sub>2 = 
        ((ids g\<^sub>1 \<subseteq> ids g\<^sub>2) \<and>
        (\<forall> n . n \<in> ids g\<^sub>1 \<longrightarrow> (\<forall>e. (g\<^sub>1 \<turnstile> n \<simeq> e) \<longrightarrow> (g\<^sub>2 \<turnstile> n \<unlhd> e))))"

lemma graph_refinement:
  "graph_refinement g1 g2 \<Longrightarrow> 
   (\<forall>n m p v. n \<in> ids g1 \<longrightarrow> ([g1, m, p] \<turnstile> n \<mapsto> v) \<longrightarrow> ([g2, m, p] \<turnstile> n \<mapsto> v))"
  by (meson encodeeval_def graph_refinement_def graph_represents_expression_def le_expr_def)

subsection \<open>Maximal Sharing\<close>

definition maximal_sharing:
  "maximal_sharing g = (\<forall> n\<^sub>1 n\<^sub>2 . n\<^sub>1 \<in> true_ids g \<and> n\<^sub>2 \<in> true_ids g \<longrightarrow> 
      (\<forall> e. (g \<turnstile> n\<^sub>1 \<simeq> e) \<and> (g \<turnstile> n\<^sub>2 \<simeq> e) \<and> (stamp g n\<^sub>1 = stamp g n\<^sub>2) \<longrightarrow> n\<^sub>1 = n\<^sub>2))"

end