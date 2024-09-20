section \<open>Conditional Elimination Tests\<close>

theory ConditionalEliminationTests
imports
  ConditionalElimination.ConditionalElimination
  Graph.Comparison
  IRGraphSort
begin

text \<open>
We assert the validity of the definition of conditional elimination optimizations through
the following suite of test cases.

GraalVM has existing infrastructure to perform unit tests of conditional elimination
optimizations, wherein an input method graph is run through the conditional elimination phase
to produce an optimized graph. The optimized graph is then structurally compared with a handwritten
optimized method.

We interject into this workflow to generate the Isabelle representation of both the input
unoptimized graph and the expected optimized graph. We then perform our conditional elimination
phase on the unoptimized graph and assert that the optimized graph expected by GraalVM is equivalent
to that which our Isabelle phase generates.
\<close>

definition ConditionalEliminationPhaseAnalysisStart where
  "ConditionalEliminationPhaseAnalysisStart = ([], [])"

(* initial: ConditionalEliminationTest13_testSnippet12*)
definition ConditionalEliminationTest13_testSnippet12_initial :: IRGraph where  "ConditionalEliminationTest13_testSnippet12_initial = irgraph [
  (0, (StartNode (Some 2) 13), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ConstantNode (IntVal 32 (-2147483648))), IntegerStamp 32 (-2147483648) (-2147483648)),
  (6, (AddNode 1 5), IntegerStamp 32 (-2147483648) (2147483647)),
  (7, (ConstantNode (IntVal 32 (2147483647))), IntegerStamp 32 (2147483647) (2147483647)),
  (8, (FrameState [] None None None), IllegalStamp),
  (9, (FrameState [] (Some 8) None None), IllegalStamp),
  (10, (IntegerEqualsNode 6 7), VoidStamp),
  (11, (BeginNode 18), VoidStamp),
  (12, (BeginNode 20), VoidStamp),
  (13, (IfNode 10 12 11), VoidStamp),
  (14, (IntegerEqualsNode 1 3), VoidStamp),
  (15, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (16, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (17, (ConditionalNode 14 15 16), IntegerStamp 32 (0) (1)),
  (18, (EndNode), VoidStamp),
  (19, (MergeNode  [18, 20] (Some 23) 27), VoidStamp),
  (20, (EndNode), VoidStamp),
  (21, (ValuePhiNode 21  [3, 17] 19), IntegerStamp 32 (-1) (1)),
  (22, (FrameState [] (Some 8) None None), IllegalStamp),
  (23, (FrameState [] (Some 22) None None), IllegalStamp),
  (24, (IntegerEqualsNode 21 3), VoidStamp),
  (25, (BeginNode 33), VoidStamp),
  (26, (BeginNode 28), VoidStamp),
  (27, (IfNode 24 26 25), VoidStamp),
  (28, (EndNode), VoidStamp),
  (29, (MergeNode  [28, 30] (Some 36) 37), VoidStamp),
  (30, (EndNode), VoidStamp),
  (31, (BeginNode 34), VoidStamp),
  (32, (BeginNode 30), VoidStamp),
  (33, (IfNode 14 31 32), VoidStamp),
  (34, (StoreFieldNode 34 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 15 (Some 35) None 39), VoidStamp),
  (35, (FrameState [] None None None), IllegalStamp),
  (36, (FrameState [] None None None), IllegalStamp),
  (37, (StoreFieldNode 37 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 3 (Some 38) None 41), VoidStamp),
  (38, (FrameState [] None None None), IllegalStamp),
  (39, (EndNode), VoidStamp),
  (40, (MergeNode  [39, 41] (Some 42) 43), VoidStamp),
  (41, (EndNode), VoidStamp),
  (42, (FrameState [] None None None), IllegalStamp),
  (43, (ReturnNode None None), VoidStamp)
  ]"

(* final: ConditionalEliminationTest13_testSnippet12*)
definition ConditionalEliminationTest13_testSnippet12_final :: IRGraph where  "ConditionalEliminationTest13_testSnippet12_final = irgraph [
  (0, (StartNode (Some 2) 13), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (4, (FrameState [] None None None), IllegalStamp),
  (5, (ConstantNode (IntVal 32 (-2147483648))), IntegerStamp 32 (-2147483648) (-2147483648)),
  (6, (AddNode 1 5), IntegerStamp 32 (-2147483648) (2147483647)),
  (7, (ConstantNode (IntVal 32 (2147483647))), IntegerStamp 32 (2147483647) (2147483647)),
  (8, (FrameState [] None None None), IllegalStamp),
  (9, (FrameState [] (Some 8) None None), IllegalStamp),
  (10, (IntegerEqualsNode 6 7), VoidStamp),
  (11, (BeginNode 18), VoidStamp),
  (12, (BeginNode 20), VoidStamp),
  (13, (IfNode 10 12 11), VoidStamp),
  (14, (IntegerEqualsNode 1 3), VoidStamp),
  (15, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (16, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (17, (ConditionalNode 14 15 16), IntegerStamp 32 (0) (1)),
  (18, (EndNode), VoidStamp),
  (19, (MergeNode  [18, 20] (Some 23) 27), VoidStamp),
  (20, (EndNode), VoidStamp),
  (21, (ValuePhiNode 21  [3, 17] 19), IntegerStamp 32 (-1) (1)),
  (22, (FrameState [] (Some 8) None None), IllegalStamp),
  (23, (FrameState [] (Some 22) None None), IllegalStamp),
  (24, (IntegerEqualsNode 21 3), VoidStamp),
  (25, (BeginNode 33), VoidStamp),
  (26, (BeginNode 28), VoidStamp),
  (27, (IfNode 24 26 25), VoidStamp),
  (28, (EndNode), VoidStamp),
  (29, (MergeNode  [28, 30] (Some 36) 37), VoidStamp),
  (30, (EndNode), VoidStamp),
  (31, (BeginNode 34), VoidStamp),
  (32, (BeginNode 30), VoidStamp),
  (33, (IfNode 14 31 32), VoidStamp),
  (34, (StoreFieldNode 34 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 15 (Some 35) None 39), VoidStamp),
  (35, (FrameState [] None None None), IllegalStamp),
  (36, (FrameState [] None None None), IllegalStamp),
  (37, (StoreFieldNode 37 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 3 (Some 38) None 41), VoidStamp),
  (38, (FrameState [] None None None), IllegalStamp),
  (39, (EndNode), VoidStamp),
  (40, (MergeNode  [39, 41] (Some 42) 43), VoidStamp),
  (41, (EndNode), VoidStamp),
  (42, (FrameState [] None None None), IllegalStamp),
  (43, (ReturnNode None None), VoidStamp)
  ]"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool) tryFold .

value "(runConditionalElimination
      ConditionalEliminationTest13_testSnippet12_initial)"

value "
  eqGraph
  (runConditionalElimination
      ConditionalEliminationTest13_testSnippet12_initial)
  ConditionalEliminationTest13_testSnippet12_final
"

value "
  diffNodesGraph
  (runConditionalElimination
      ConditionalEliminationTest13_testSnippet12_initial)
  ConditionalEliminationTest13_testSnippet12_final
"

value "
  diffNodesInfo
  (runConditionalElimination
      ConditionalEliminationTest13_testSnippet12_initial)
  ConditionalEliminationTest13_testSnippet12_final
"


(* initial: ConditionalEliminationTest13_testSnippet13*)
definition ConditionalEliminationTest13_testSnippet13_initial :: IRGraph where  "ConditionalEliminationTest13_testSnippet13_initial = irgraph [
  (0, (StartNode (Some 2) 6), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (LoadFieldNode 6 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' None 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (7, (LoadFieldNode 7 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' None 9), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (AddNode 6 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (LoadFieldNode 9 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' None 14), IntegerStamp 32 (-2147483648) (2147483647)),
  (10, (AddNode 8 9), IntegerStamp 32 (-2147483648) (2147483647)),
  (11, (IntegerEqualsNode 10 3), VoidStamp),
  (12, (BeginNode 17), VoidStamp),
  (13, (BeginNode 15), VoidStamp),
  (14, (IfNode 11 13 12), VoidStamp),
  (15, (EndNode), VoidStamp),
  (16, (MergeNode  [15, 17] (Some 20) 25), VoidStamp),
  (17, (EndNode), VoidStamp),
  (18, (ValuePhiNode 18  [3, 4] 16), IntegerStamp 32 (0) (1)),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (FrameState [] (Some 19) None None), IllegalStamp),
  (21, (AddNode 1 18), IntegerStamp 32 (-2147483648) (2147483647)),
  (22, (IntegerLessThanNode 21 1), VoidStamp),
  (23, (BeginNode 30), VoidStamp),
  (24, (BeginNode 41), VoidStamp),
  (25, (IfNode 22 24 23), VoidStamp),
  (26, (ConstantNode (IntVal 32 (2147483647))), IntegerStamp 32 (2147483647) (2147483647)),
  (27, (IntegerEqualsNode 1 26), VoidStamp),
  (28, (BeginNode 34), VoidStamp),
  (29, (BeginNode 32), VoidStamp),
  (30, (IfNode 27 29 28), VoidStamp),
  (31, (ConstantNode (IntVal 32 (-2))), IntegerStamp 32 (-2) (-2)),
  (32, (StoreFieldNode 32 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' 31 (Some 33) None 36), VoidStamp),
  (33, (FrameState [] None None None), IllegalStamp),
  (34, (EndNode), VoidStamp),
  (35, (MergeNode  [34, 36] (Some 37) 38), VoidStamp),
  (36, (EndNode), VoidStamp),
  (37, (FrameState [] None None None), IllegalStamp),
  (38, (StoreFieldNode 38 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 3 (Some 39) None 43), VoidStamp),
  (39, (FrameState [] None None None), IllegalStamp),
  (40, (ConstantNode (IntVal 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (41, (StoreFieldNode 41 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 40 (Some 42) None 45), VoidStamp),
  (42, (FrameState [] None None None), IllegalStamp),
  (43, (EndNode), VoidStamp),
  (44, (MergeNode  [43, 45] (Some 46) 47), VoidStamp),
  (45, (EndNode), VoidStamp),
  (46, (FrameState [] None None None), IllegalStamp),
  (47, (ReturnNode None None), VoidStamp)
  ]"

(* final: ConditionalEliminationTest13_testSnippet13*)
definition ConditionalEliminationTest13_testSnippet13_final :: IRGraph where  "ConditionalEliminationTest13_testSnippet13_final = irgraph [
  (0, (StartNode (Some 2) 6), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (LoadFieldNode 6 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' None 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (7, (LoadFieldNode 7 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' None 9), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (AddNode 6 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (LoadFieldNode 9 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' None 14), IntegerStamp 32 (-2147483648) (2147483647)),
  (10, (AddNode 8 9), IntegerStamp 32 (-2147483648) (2147483647)),
  (11, (IntegerEqualsNode 10 3), VoidStamp),
  (12, (BeginNode 17), VoidStamp),
  (13, (BeginNode 15), VoidStamp),
  (14, (IfNode 11 13 12), VoidStamp),
  (15, (EndNode), VoidStamp),
  (16, (MergeNode  [15, 17] (Some 20) 25), VoidStamp),
  (17, (EndNode), VoidStamp),
  (18, (ValuePhiNode 18  [3, 4] 16), IntegerStamp 32 (0) (1)),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (FrameState [] (Some 19) None None), IllegalStamp),
  (21, (AddNode 1 18), IntegerStamp 32 (-2147483648) (2147483647)),
  (22, (IntegerLessThanNode 21 1), VoidStamp),
  (23, (BeginNode 30), VoidStamp),
  (24, (BeginNode 41), VoidStamp),
  (25, (IfNode 22 24 23), VoidStamp),
  (26, (ConstantNode (IntVal 32 (2147483647))), IntegerStamp 32 (2147483647) (2147483647)),
  (27, (IntegerEqualsNode 1 26), VoidStamp),
  (28, (BeginNode 34), VoidStamp),
  (29, (BeginNode 32), VoidStamp),
  (30, (IfNode 27 29 28), VoidStamp),
  (31, (ConstantNode (IntVal 32 (-2))), IntegerStamp 32 (-2) (-2)),
  (32, (StoreFieldNode 32 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' 31 (Some 33) None 36), VoidStamp),
  (33, (FrameState [] None None None), IllegalStamp),
  (34, (EndNode), VoidStamp),
  (35, (MergeNode  [34, 36] (Some 37) 38), VoidStamp),
  (36, (EndNode), VoidStamp),
  (37, (FrameState [] None None None), IllegalStamp),
  (38, (StoreFieldNode 38 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 3 (Some 39) None 43), VoidStamp),
  (39, (FrameState [] None None None), IllegalStamp),
  (40, (ConstantNode (IntVal 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (41, (StoreFieldNode 41 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 40 (Some 42) None 45), VoidStamp),
  (42, (FrameState [] None None None), IllegalStamp),
  (43, (EndNode), VoidStamp),
  (44, (MergeNode  [43, 45] (Some 46) 47), VoidStamp),
  (45, (EndNode), VoidStamp),
  (46, (FrameState [] None None None), IllegalStamp),
  (47, (ReturnNode None None), VoidStamp)
  ]"

value "
  eqGraph
  (runConditionalElimination
      ConditionalEliminationTest13_testSnippet13_initial)
  ConditionalEliminationTest13_testSnippet13_final
"

value "
  diffNodesGraph
  (runConditionalElimination
      ConditionalEliminationTest13_testSnippet13_initial)
  ConditionalEliminationTest13_testSnippet13_final
"

value "
  diffNodesInfo
  (runConditionalElimination
      ConditionalEliminationTest13_testSnippet13_initial)
  ConditionalEliminationTest13_testSnippet13_final
"


(* initial: ConditionalEliminationTest13_testSnippet14*)
definition ConditionalEliminationTest13_testSnippet14_initial :: IRGraph where  "ConditionalEliminationTest13_testSnippet14_initial = irgraph [
  (0, (StartNode (Some 2) 6), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (LoadFieldNode 6 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' None 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (7, (LoadFieldNode 7 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' None 9), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (AddNode 6 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (LoadFieldNode 9 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' None 14), IntegerStamp 32 (-2147483648) (2147483647)),
  (10, (AddNode 8 9), IntegerStamp 32 (-2147483648) (2147483647)),
  (11, (IntegerEqualsNode 10 3), VoidStamp),
  (12, (BeginNode 17), VoidStamp),
  (13, (BeginNode 15), VoidStamp),
  (14, (IfNode 11 13 12), VoidStamp),
  (15, (EndNode), VoidStamp),
  (16, (MergeNode  [15, 17] (Some 20) 25), VoidStamp),
  (17, (EndNode), VoidStamp),
  (18, (ValuePhiNode 18  [3, 4] 16), IntegerStamp 32 (0) (1)),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (FrameState [] (Some 19) None None), IllegalStamp),
  (21, (AddNode 1 18), IntegerStamp 32 (-2147483648) (2147483647)),
  (22, (IntegerLessThanNode 1 21), VoidStamp),
  (23, (BeginNode 41), VoidStamp),
  (24, (BeginNode 30), VoidStamp),
  (25, (IfNode 22 24 23), VoidStamp),
  (26, (ConstantNode (IntVal 32 (2147483647))), IntegerStamp 32 (2147483647) (2147483647)),
  (27, (IntegerEqualsNode 1 26), VoidStamp),
  (28, (BeginNode 34), VoidStamp),
  (29, (BeginNode 32), VoidStamp),
  (30, (IfNode 27 29 28), VoidStamp),
  (31, (ConstantNode (IntVal 32 (-2))), IntegerStamp 32 (-2) (-2)),
  (32, (StoreFieldNode 32 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' 31 (Some 33) None 36), VoidStamp),
  (33, (FrameState [] None None None), IllegalStamp),
  (34, (EndNode), VoidStamp),
  (35, (MergeNode  [34, 36] (Some 37) 38), VoidStamp),
  (36, (EndNode), VoidStamp),
  (37, (FrameState [] None None None), IllegalStamp),
  (38, (StoreFieldNode 38 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 3 (Some 39) None 43), VoidStamp),
  (39, (FrameState [] None None None), IllegalStamp),
  (40, (ConstantNode (IntVal 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (41, (StoreFieldNode 41 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 40 (Some 42) None 45), VoidStamp),
  (42, (FrameState [] None None None), IllegalStamp),
  (43, (EndNode), VoidStamp),
  (44, (MergeNode  [43, 45] (Some 46) 47), VoidStamp),
  (45, (EndNode), VoidStamp),
  (46, (FrameState [] None None None), IllegalStamp),
  (47, (ReturnNode None None), VoidStamp)
  ]"

(* final: ConditionalEliminationTest13_testSnippet14*)
definition ConditionalEliminationTest13_testSnippet14_final :: IRGraph where  "ConditionalEliminationTest13_testSnippet14_final = irgraph [
  (0, (StartNode (Some 2) 6), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (FrameState [] None None None), IllegalStamp),
  (6, (LoadFieldNode 6 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' None 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (7, (LoadFieldNode 7 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' None 9), IntegerStamp 32 (-2147483648) (2147483647)),
  (8, (AddNode 6 7), IntegerStamp 32 (-2147483648) (2147483647)),
  (9, (LoadFieldNode 9 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' None 14), IntegerStamp 32 (-2147483648) (2147483647)),
  (10, (AddNode 8 9), IntegerStamp 32 (-2147483648) (2147483647)),
  (11, (IntegerEqualsNode 10 3), VoidStamp),
  (12, (BeginNode 17), VoidStamp),
  (13, (BeginNode 15), VoidStamp),
  (14, (IfNode 11 13 12), VoidStamp),
  (15, (EndNode), VoidStamp),
  (16, (MergeNode  [15, 17] (Some 20) 25), VoidStamp),
  (17, (EndNode), VoidStamp),
  (18, (ValuePhiNode 18  [3, 4] 16), IntegerStamp 32 (0) (1)),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (FrameState [] (Some 19) None None), IllegalStamp),
  (21, (AddNode 1 18), IntegerStamp 32 (-2147483648) (2147483647)),
  (22, (IntegerLessThanNode 1 21), VoidStamp),
  (23, (BeginNode 41), VoidStamp),
  (24, (BeginNode 30), VoidStamp),
  (25, (IfNode 22 24 23), VoidStamp),
  (26, (ConstantNode (IntVal 32 (2147483647))), IntegerStamp 32 (2147483647) (2147483647)),
  (27, (IntegerEqualsNode 1 26), VoidStamp),
  (28, (BeginNode 34), VoidStamp),
  (29, (BeginNode 32), VoidStamp),
  (30, (IfNode 48 29 28), VoidStamp),
  (31, (ConstantNode (IntVal 32 (-2))), IntegerStamp 32 (-2) (-2)),
  (32, (StoreFieldNode 32 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' 31 (Some 33) None 36), VoidStamp),
  (33, (FrameState [] None None None), IllegalStamp),
  (34, (EndNode), VoidStamp),
  (35, (MergeNode  [34, 36] (Some 37) 38), VoidStamp),
  (36, (EndNode), VoidStamp),
  (37, (FrameState [] None None None), IllegalStamp),
  (38, (StoreFieldNode 38 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 3 (Some 39) None 43), VoidStamp),
  (39, (FrameState [] None None None), IllegalStamp),
  (40, (ConstantNode (IntVal 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (41, (StoreFieldNode 41 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 40 (Some 42) None 45), VoidStamp),
  (42, (FrameState [] None None None), IllegalStamp),
  (43, (EndNode), VoidStamp),
  (44, (MergeNode  [43, 45] (Some 46) 47), VoidStamp),
  (45, (EndNode), VoidStamp),
  (46, (FrameState [] None None None), IllegalStamp),
  (47, (ReturnNode None None), VoidStamp),
  (48, (ConstantNode (IntVal 1 (0))), VoidStamp)
  ]"

value "
  eqGraph
  (runConditionalElimination
    ConditionalEliminationTest13_testSnippet14_initial)
  ConditionalEliminationTest13_testSnippet14_final
"

value "
  diffNodesGraph
  (runConditionalElimination
    ConditionalEliminationTest13_testSnippet14_initial)
  ConditionalEliminationTest13_testSnippet14_final
"

value "
  diffNodesInfo
  (runConditionalElimination
    ConditionalEliminationTest13_testSnippet14_initial)
  ConditionalEliminationTest13_testSnippet14_final
"


(* initial: ConditionalEliminationTest13_testSnippet2*)
definition ConditionalEliminationTest13_testSnippet2_initial :: IRGraph where  "ConditionalEliminationTest13_testSnippet2_initial = irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (IntegerLessThanNode 1 4), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (BeginNode 23), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (ConstantNode (IntVal 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (10, (IntegerEqualsNode 1 9), VoidStamp),
  (11, (BeginNode 17), VoidStamp),
  (12, (BeginNode 15), VoidStamp),
  (13, (IfNode 10 12 11), VoidStamp),
  (14, (ConstantNode (IntVal 32 (-2))), IntegerStamp 32 (-2) (-2)),
  (15, (StoreFieldNode 15 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' 14 (Some 16) None 19), VoidStamp),
  (16, (FrameState [] None None None), IllegalStamp),
  (17, (EndNode), VoidStamp),
  (18, (MergeNode  [17, 19] (Some 20) 21), VoidStamp),
  (19, (EndNode), VoidStamp),
  (20, (FrameState [] None None None), IllegalStamp),
  (21, (StoreFieldNode 21 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 3 (Some 22) None 25), VoidStamp),
  (22, (FrameState [] None None None), IllegalStamp),
  (23, (EndNode), VoidStamp),
  (24, (MergeNode  [23, 25] (Some 26) 27), VoidStamp),
  (25, (EndNode), VoidStamp),
  (26, (FrameState [] None None None), IllegalStamp),
  (27, (StoreFieldNode 27 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 9 (Some 28) None 29), VoidStamp),
  (28, (FrameState [] None None None), IllegalStamp),
  (29, (ReturnNode None None), VoidStamp)
  ]"

(* final: ConditionalEliminationTest13_testSnippet2*)
definition ConditionalEliminationTest13_testSnippet2_final :: IRGraph where  "ConditionalEliminationTest13_testSnippet2_final = irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (IntegerLessThanNode 1 4), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (BeginNode 23), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (ConstantNode (IntVal 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (10, (IntegerEqualsNode 1 9), VoidStamp),
  (11, (BeginNode 17), VoidStamp),
  (12, (BeginNode 15), VoidStamp),
  (13, (IfNode 30 12 11), VoidStamp),
  (14, (ConstantNode (IntVal 32 (-2))), IntegerStamp 32 (-2) (-2)),
  (15, (StoreFieldNode 15 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' 14 (Some 16) None 19), VoidStamp),
  (16, (FrameState [] None None None), IllegalStamp),
  (17, (EndNode), VoidStamp),
  (18, (MergeNode  [17, 19] (Some 20) 21), VoidStamp),
  (19, (EndNode), VoidStamp),
  (20, (FrameState [] None None None), IllegalStamp),
  (21, (StoreFieldNode 21 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 3 (Some 22) None 25), VoidStamp),
  (22, (FrameState [] None None None), IllegalStamp),
  (23, (EndNode), VoidStamp),
  (24, (MergeNode  [23, 25] (Some 26) 27), VoidStamp),
  (25, (EndNode), VoidStamp),
  (26, (FrameState [] None None None), IllegalStamp),
  (27, (StoreFieldNode 27 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 9 (Some 28) None 29), VoidStamp),
  (28, (FrameState [] None None None), IllegalStamp),
  (29, (ReturnNode None None), VoidStamp),
  (30, (ConstantNode (IntVal 1 (0))), VoidStamp)
  ]"

value "
  eqGraph
  (runConditionalElimination
    ConditionalEliminationTest13_testSnippet2_initial)
  ConditionalEliminationTest13_testSnippet2_final
"

value "
  diffNodesGraph
  (runConditionalElimination
    ConditionalEliminationTest13_testSnippet2_initial)
  ConditionalEliminationTest13_testSnippet2_final
"

value "
  diffNodesInfo
  (runConditionalElimination
    ConditionalEliminationTest13_testSnippet2_initial)
  ConditionalEliminationTest13_testSnippet2_final
"


(* initial: ConditionalEliminationTest13_testSnippet3*)
definition ConditionalEliminationTest13_testSnippet3_initial :: IRGraph where  "ConditionalEliminationTest13_testSnippet3_initial = irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (IntegerLessThanNode 1 4), VoidStamp),
  (6, (BeginNode 12), VoidStamp),
  (7, (BeginNode 22), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (IntegerEqualsNode 1 4), VoidStamp),
  (10, (BeginNode 16), VoidStamp),
  (11, (BeginNode 14), VoidStamp),
  (12, (IfNode 9 11 10), VoidStamp),
  (13, (ConstantNode (IntVal 32 (-2))), IntegerStamp 32 (-2) (-2)),
  (14, (StoreFieldNode 14 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' 13 (Some 15) None 18), VoidStamp),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode  [16, 18] (Some 19) 20), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (StoreFieldNode 20 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 3 (Some 21) None 24), VoidStamp),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (EndNode), VoidStamp),
  (23, (MergeNode  [22, 24] (Some 25) 27), VoidStamp),
  (24, (EndNode), VoidStamp),
  (25, (FrameState [] None None None), IllegalStamp),
  (26, (ConstantNode (IntVal 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (27, (StoreFieldNode 27 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 26 (Some 28) None 29), VoidStamp),
  (28, (FrameState [] None None None), IllegalStamp),
  (29, (ReturnNode None None), VoidStamp)
  ]"

(* final: ConditionalEliminationTest13_testSnippet3*)
definition ConditionalEliminationTest13_testSnippet3_final :: IRGraph where  "ConditionalEliminationTest13_testSnippet3_final = irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (IntegerLessThanNode 1 4), VoidStamp),
  (6, (BeginNode 12), VoidStamp),
  (7, (BeginNode 22), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (IntegerEqualsNode 1 4), VoidStamp),
  (10, (BeginNode 16), VoidStamp),
  (11, (BeginNode 14), VoidStamp),
  (12, (IfNode 9 11 10), VoidStamp),
  (13, (ConstantNode (IntVal 32 (-2))), IntegerStamp 32 (-2) (-2)),
  (14, (StoreFieldNode 14 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' 13 (Some 15) None 18), VoidStamp),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode  [16, 18] (Some 19) 20), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (StoreFieldNode 20 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 3 (Some 21) None 24), VoidStamp),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (EndNode), VoidStamp),
  (23, (MergeNode  [22, 24] (Some 25) 27), VoidStamp),
  (24, (EndNode), VoidStamp),
  (25, (FrameState [] None None None), IllegalStamp),
  (26, (ConstantNode (IntVal 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (27, (StoreFieldNode 27 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 26 (Some 28) None 29), VoidStamp),
  (28, (FrameState [] None None None), IllegalStamp),
  (29, (ReturnNode None None), VoidStamp)
  ]"

value "
  eqGraph
  (runConditionalElimination
    ConditionalEliminationTest13_testSnippet3_initial)
  ConditionalEliminationTest13_testSnippet3_final
"

value "
  diffNodesGraph
  (runConditionalElimination
    ConditionalEliminationTest13_testSnippet3_initial)
  ConditionalEliminationTest13_testSnippet3_final
"

value "
  diffNodesInfo
  (runConditionalElimination
    ConditionalEliminationTest13_testSnippet3_initial)
  ConditionalEliminationTest13_testSnippet3_final
"


(* initial: ConditionalEliminationTest13_testSnippet5*)
definition ConditionalEliminationTest13_testSnippet5_initial :: IRGraph where  "ConditionalEliminationTest13_testSnippet5_initial = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerLessThanNode 1 3), VoidStamp),
  (5, (BeginNode 22), VoidStamp),
  (6, (BeginNode 12), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (IntVal 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (9, (IntegerEqualsNode 1 8), VoidStamp),
  (10, (BeginNode 16), VoidStamp),
  (11, (BeginNode 14), VoidStamp),
  (12, (IfNode 9 11 10), VoidStamp),
  (13, (ConstantNode (IntVal 32 (-2))), IntegerStamp 32 (-2) (-2)),
  (14, (StoreFieldNode 14 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' 13 (Some 15) None 18), VoidStamp),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode  [16, 18] (Some 19) 20), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (StoreFieldNode 20 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 3 (Some 21) None 24), VoidStamp),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (EndNode), VoidStamp),
  (23, (MergeNode  [22, 24] (Some 25) 26), VoidStamp),
  (24, (EndNode), VoidStamp),
  (25, (FrameState [] None None None), IllegalStamp),
  (26, (StoreFieldNode 26 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 8 (Some 27) None 28), VoidStamp),
  (27, (FrameState [] None None None), IllegalStamp),
  (28, (ReturnNode None None), VoidStamp)
  ]"

(* final: ConditionalEliminationTest13_testSnippet5*)
definition ConditionalEliminationTest13_testSnippet5_final :: IRGraph where  "ConditionalEliminationTest13_testSnippet5_final = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerLessThanNode 1 3), VoidStamp),
  (5, (BeginNode 22), VoidStamp),
  (6, (BeginNode 12), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (IntVal 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (9, (IntegerEqualsNode 1 8), VoidStamp),
  (10, (BeginNode 16), VoidStamp),
  (11, (BeginNode 14), VoidStamp),
  (12, (IfNode 9 11 10), VoidStamp),
  (13, (ConstantNode (IntVal 32 (-2))), IntegerStamp 32 (-2) (-2)),
  (14, (StoreFieldNode 14 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' 13 (Some 15) None 18), VoidStamp),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode  [16, 18] (Some 19) 20), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (StoreFieldNode 20 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 3 (Some 21) None 24), VoidStamp),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (EndNode), VoidStamp),
  (23, (MergeNode  [22, 24] (Some 25) 26), VoidStamp),
  (24, (EndNode), VoidStamp),
  (25, (FrameState [] None None None), IllegalStamp),
  (26, (StoreFieldNode 26 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 8 (Some 27) None 28), VoidStamp),
  (27, (FrameState [] None None None), IllegalStamp),
  (28, (ReturnNode None None), VoidStamp)
  ]"

value "
  eqGraph
  (runConditionalElimination
    ConditionalEliminationTest13_testSnippet5_initial)
  ConditionalEliminationTest13_testSnippet5_final
"

value "
  diffNodesGraph
  (runConditionalElimination
    ConditionalEliminationTest13_testSnippet5_initial)
  ConditionalEliminationTest13_testSnippet5_final
"

value "
  diffNodesInfo
  (runConditionalElimination
    ConditionalEliminationTest13_testSnippet5_initial)
  ConditionalEliminationTest13_testSnippet5_final
"


(* initial: ConditionalEliminationTest13_testSnippet6*)
definition ConditionalEliminationTest13_testSnippet6_initial :: IRGraph where  "ConditionalEliminationTest13_testSnippet6_initial = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerLessThanNode 1 3), VoidStamp),
  (5, (BeginNode 21), VoidStamp),
  (6, (BeginNode 11), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (IntegerEqualsNode 1 3), VoidStamp),
  (9, (BeginNode 15), VoidStamp),
  (10, (BeginNode 13), VoidStamp),
  (11, (IfNode 8 10 9), VoidStamp),
  (12, (ConstantNode (IntVal 32 (-2))), IntegerStamp 32 (-2) (-2)),
  (13, (StoreFieldNode 13 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' 12 (Some 14) None 17), VoidStamp),
  (14, (FrameState [] None None None), IllegalStamp),
  (15, (EndNode), VoidStamp),
  (16, (MergeNode  [15, 17] (Some 18) 19), VoidStamp),
  (17, (EndNode), VoidStamp),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (StoreFieldNode 19 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 3 (Some 20) None 23), VoidStamp),
  (20, (FrameState [] None None None), IllegalStamp),
  (21, (EndNode), VoidStamp),
  (22, (MergeNode  [21, 23] (Some 24) 26), VoidStamp),
  (23, (EndNode), VoidStamp),
  (24, (FrameState [] None None None), IllegalStamp),
  (25, (ConstantNode (IntVal 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (26, (StoreFieldNode 26 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 25 (Some 27) None 28), VoidStamp),
  (27, (FrameState [] None None None), IllegalStamp),
  (28, (ReturnNode None None), VoidStamp)
  ]"

(* final: ConditionalEliminationTest13_testSnippet6*)
definition ConditionalEliminationTest13_testSnippet6_final :: IRGraph where  "ConditionalEliminationTest13_testSnippet6_final = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerLessThanNode 1 3), VoidStamp),
  (5, (BeginNode 21), VoidStamp),
  (6, (BeginNode 11), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (IntegerEqualsNode 1 3), VoidStamp),
  (9, (BeginNode 15), VoidStamp),
  (10, (BeginNode 13), VoidStamp),
  (11, (IfNode 29 10 9), VoidStamp),
  (12, (ConstantNode (IntVal 32 (-2))), IntegerStamp 32 (-2) (-2)),
  (13, (StoreFieldNode 13 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' 12 (Some 14) None 17), VoidStamp),
  (14, (FrameState [] None None None), IllegalStamp),
  (15, (EndNode), VoidStamp),
  (16, (MergeNode  [15, 17] (Some 18) 19), VoidStamp),
  (17, (EndNode), VoidStamp),
  (18, (FrameState [] None None None), IllegalStamp),
  (19, (StoreFieldNode 19 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 3 (Some 20) None 23), VoidStamp),
  (20, (FrameState [] None None None), IllegalStamp),
  (21, (EndNode), VoidStamp),
  (22, (MergeNode  [21, 23] (Some 24) 26), VoidStamp),
  (23, (EndNode), VoidStamp),
  (24, (FrameState [] None None None), IllegalStamp),
  (25, (ConstantNode (IntVal 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (26, (StoreFieldNode 26 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 25 (Some 27) None 28), VoidStamp),
  (27, (FrameState [] None None None), IllegalStamp),
  (28, (ReturnNode None None), VoidStamp),
  (29, (ConstantNode (IntVal 1 (0))), VoidStamp)
  ]"

value "
  eqGraph
  (runConditionalElimination
    ConditionalEliminationTest13_testSnippet6_initial)
  ConditionalEliminationTest13_testSnippet6_final
"

value "
  diffNodesGraph
  (runConditionalElimination
    ConditionalEliminationTest13_testSnippet6_initial)
  ConditionalEliminationTest13_testSnippet6_final
"

value "
  diffNodesInfo
  (runConditionalElimination
    ConditionalEliminationTest13_testSnippet6_initial)
  ConditionalEliminationTest13_testSnippet6_final
"


(* initial: ConditionalEliminationTest13_testSnippet7*)
definition ConditionalEliminationTest13_testSnippet7_initial :: IRGraph where  "ConditionalEliminationTest13_testSnippet7_initial = irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (IntegerLessThanNode 1 4), VoidStamp),
  (6, (BeginNode 12), VoidStamp),
  (7, (BeginNode 22), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (IntegerEqualsNode 1 3), VoidStamp),
  (10, (BeginNode 16), VoidStamp),
  (11, (BeginNode 14), VoidStamp),
  (12, (IfNode 9 11 10), VoidStamp),
  (13, (ConstantNode (IntVal 32 (-2))), IntegerStamp 32 (-2) (-2)),
  (14, (StoreFieldNode 14 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' 13 (Some 15) None 18), VoidStamp),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode  [16, 18] (Some 19) 20), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (StoreFieldNode 20 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 3 (Some 21) None 24), VoidStamp),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (EndNode), VoidStamp),
  (23, (MergeNode  [22, 24] (Some 25) 27), VoidStamp),
  (24, (EndNode), VoidStamp),
  (25, (FrameState [] None None None), IllegalStamp),
  (26, (ConstantNode (IntVal 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (27, (StoreFieldNode 27 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 26 (Some 28) None 29), VoidStamp),
  (28, (FrameState [] None None None), IllegalStamp),
  (29, (ReturnNode None None), VoidStamp)
  ]"

(* final: ConditionalEliminationTest13_testSnippet7*)
definition ConditionalEliminationTest13_testSnippet7_final :: IRGraph where  "ConditionalEliminationTest13_testSnippet7_final = irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (IntegerLessThanNode 1 4), VoidStamp),
  (6, (BeginNode 12), VoidStamp),
  (7, (BeginNode 22), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (IntegerEqualsNode 1 3), VoidStamp),
  (10, (BeginNode 16), VoidStamp),
  (11, (BeginNode 14), VoidStamp),
  (12, (IfNode 30 11 10), VoidStamp),
  (13, (ConstantNode (IntVal 32 (-2))), IntegerStamp 32 (-2) (-2)),
  (14, (StoreFieldNode 14 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' 13 (Some 15) None 18), VoidStamp),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode  [16, 18] (Some 19) 20), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (StoreFieldNode 20 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 3 (Some 21) None 24), VoidStamp),
  (21, (FrameState [] None None None), IllegalStamp),
  (22, (EndNode), VoidStamp),
  (23, (MergeNode  [22, 24] (Some 25) 27), VoidStamp),
  (24, (EndNode), VoidStamp),
  (25, (FrameState [] None None None), IllegalStamp),
  (26, (ConstantNode (IntVal 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (27, (StoreFieldNode 27 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 26 (Some 28) None 29), VoidStamp),
  (28, (FrameState [] None None None), IllegalStamp),
  (29, (ReturnNode None None), VoidStamp),
  (30, (ConstantNode (IntVal 1 (0))), VoidStamp)
  ]"

value "
  eqGraph
  (runConditionalElimination
    ConditionalEliminationTest13_testSnippet7_initial)
  ConditionalEliminationTest13_testSnippet7_final
"

value "
  diffNodesGraph
  (runConditionalElimination
    ConditionalEliminationTest13_testSnippet7_initial)
  ConditionalEliminationTest13_testSnippet7_final
"

value "
  diffNodesInfo
  (runConditionalElimination
    ConditionalEliminationTest13_testSnippet7_initial)
  ConditionalEliminationTest13_testSnippet7_final
"


(* initial: ConditionalEliminationTest1_test1Snippet*)
definition ConditionalEliminationTest1_test1Snippet_initial :: IRGraph where  "ConditionalEliminationTest1_test1Snippet_initial = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 39), VoidStamp),
  (6, (BeginNode 12), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (IntVal 32 (5))), IntegerStamp 32 (5) (5)),
  (9, (IntegerEqualsNode 1 8), VoidStamp),
  (10, (BeginNode 16), VoidStamp),
  (11, (BeginNode 14), VoidStamp),
  (12, (IfNode 9 11 10), VoidStamp),
  (13, (ConstantNode (IntVal 32 (100))), IntegerStamp 32 (100) (100)),
  (14, (StoreFieldNode 14 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' 13 (Some 15) None 18), VoidStamp),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode  [16, 18] (Some 19) 24), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (ConstantNode (IntVal 32 (101))), IntegerStamp 32 (101) (101)),
  (21, (IntegerLessThanNode 1 20), VoidStamp),
  (22, (BeginNode 30), VoidStamp),
  (23, (BeginNode 25), VoidStamp),
  (24, (IfNode 21 23 22), VoidStamp),
  (25, (EndNode), VoidStamp),
  (26, (MergeNode  [25, 27, 34] (Some 35) 43), VoidStamp),
  (27, (EndNode), VoidStamp),
  (28, (BeginNode 32), VoidStamp),
  (29, (BeginNode 27), VoidStamp),
  (30, (IfNode 4 28 29), VoidStamp),
  (31, (ConstantNode (IntVal 32 (200))), IntegerStamp 32 (200) (200)),
  (32, (StoreFieldNode 32 ''org.graalvm.compiler.core.test.ConditionalEliminationTest1::sink3'' 31 (Some 33) None 34), VoidStamp),
  (33, (FrameState [] None None None), IllegalStamp),
  (34, (EndNode), VoidStamp),
  (35, (FrameState [] None None None), IllegalStamp),
  (36, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
  (37, (IntegerEqualsNode 1 36), VoidStamp),
  (38, (BeginNode 45), VoidStamp),
  (39, (EndNode), VoidStamp),
  (40, (MergeNode  [39, 41, 47] (Some 48) 49), VoidStamp),
  (41, (EndNode), VoidStamp),
  (42, (BeginNode 41), VoidStamp),
  (43, (IfNode 37 42 38), VoidStamp),
  (44, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (45, (StoreFieldNode 45 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 44 (Some 46) None 47), VoidStamp),
  (46, (FrameState [] None None None), IllegalStamp),
  (47, (EndNode), VoidStamp),
  (48, (FrameState [] None None None), IllegalStamp),
  (49, (StoreFieldNode 49 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 3 (Some 50) None 51), VoidStamp),
  (50, (FrameState [] None None None), IllegalStamp),
  (51, (ReturnNode None None), VoidStamp)
  ]"

(* final: ConditionalEliminationTest1_test1Snippet*)
definition ConditionalEliminationTest1_test1Snippet_final :: IRGraph where  "ConditionalEliminationTest1_test1Snippet_final = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 39), VoidStamp),
  (6, (BeginNode 12), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (IntVal 32 (5))), IntegerStamp 32 (5) (5)),
  (9, (IntegerEqualsNode 1 8), VoidStamp),
  (10, (BeginNode 16), VoidStamp),
  (11, (BeginNode 14), VoidStamp),
  (12, (IfNode 52 11 10), VoidStamp),
  (13, (ConstantNode (IntVal 32 (100))), IntegerStamp 32 (100) (100)),
  (14, (StoreFieldNode 14 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' 13 (Some 15) None 18), VoidStamp),
  (15, (FrameState [] None None None), IllegalStamp),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode  [16, 18] (Some 19) 24), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (FrameState [] None None None), IllegalStamp),
  (20, (ConstantNode (IntVal 32 (101))), IntegerStamp 32 (101) (101)),
  (21, (IntegerLessThanNode 1 20), VoidStamp),
  (22, (BeginNode 30), VoidStamp),
  (23, (BeginNode 25), VoidStamp),
  (24, (IfNode 53 23 22), VoidStamp),
  (25, (EndNode), VoidStamp),
  (26, (MergeNode  [25, 27, 34] (Some 35) 43), VoidStamp),
  (27, (EndNode), VoidStamp),
  (28, (BeginNode 32), VoidStamp),
  (29, (BeginNode 27), VoidStamp),
  (30, (IfNode 53 28 29), VoidStamp),
  (31, (ConstantNode (IntVal 32 (200))), IntegerStamp 32 (200) (200)),
  (32, (StoreFieldNode 32 ''org.graalvm.compiler.core.test.ConditionalEliminationTest1::sink3'' 31 (Some 33) None 34), VoidStamp),
  (33, (FrameState [] None None None), IllegalStamp),
  (34, (EndNode), VoidStamp),
  (35, (FrameState [] None None None), IllegalStamp),
  (36, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
  (37, (IntegerEqualsNode 1 36), VoidStamp),
  (38, (BeginNode 45), VoidStamp),
  (39, (EndNode), VoidStamp),
  (40, (MergeNode  [39, 41, 47] (Some 48) 49), VoidStamp),
  (41, (EndNode), VoidStamp),
  (42, (BeginNode 41), VoidStamp),
  (43, (IfNode 52 42 38), VoidStamp),
  (44, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (45, (StoreFieldNode 45 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 44 (Some 46) None 47), VoidStamp),
  (46, (FrameState [] None None None), IllegalStamp),
  (47, (EndNode), VoidStamp),
  (48, (FrameState [] None None None), IllegalStamp),
  (49, (StoreFieldNode 49 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 3 (Some 50) None 51), VoidStamp),
  (50, (FrameState [] None None None), IllegalStamp),
  (51, (ReturnNode None None), VoidStamp),
  (52, (ConstantNode (IntVal 1 (0))), VoidStamp),
  (53, (ConstantNode (IntVal 1 (1))), VoidStamp)
  ]"

value "
  eqGraph
  (runConditionalElimination
    ConditionalEliminationTest1_test1Snippet_initial)
  ConditionalEliminationTest1_test1Snippet_final
"

value "
  diffNodesGraph
  (runConditionalElimination
    ConditionalEliminationTest1_test1Snippet_initial)
  ConditionalEliminationTest1_test1Snippet_final
"

value "
  diffNodesInfo
  (runConditionalElimination
    ConditionalEliminationTest1_test1Snippet_initial)
  ConditionalEliminationTest1_test1Snippet_final
"


(* initial: ConditionalEliminationTest1_test2Snippet*)
definition ConditionalEliminationTest1_test2Snippet_initial :: IRGraph where  "ConditionalEliminationTest1_test2Snippet_initial = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 28), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (IntVal 32 (100))), IntegerStamp 32 (100) (100)),
  (9, (ConstantNode (IntVal 32 (101))), IntegerStamp 32 (101) (101)),
  (10, (IntegerLessThanNode 1 9), VoidStamp),
  (11, (BeginNode 19), VoidStamp),
  (12, (BeginNode 14), VoidStamp),
  (13, (IfNode 10 12 11), VoidStamp),
  (14, (EndNode), VoidStamp),
  (15, (MergeNode  [14, 16, 23] (Some 24) 32), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (BeginNode 21), VoidStamp),
  (18, (BeginNode 16), VoidStamp),
  (19, (IfNode 4 17 18), VoidStamp),
  (20, (ConstantNode (IntVal 32 (200))), IntegerStamp 32 (200) (200)),
  (21, (StoreFieldNode 21 ''org.graalvm.compiler.core.test.ConditionalEliminationTest1::sink3'' 20 (Some 22) None 23), VoidStamp),
  (22, (FrameState [] None None None), IllegalStamp),
  (23, (EndNode), VoidStamp),
  (24, (FrameState [] None None None), IllegalStamp),
  (25, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
  (26, (IntegerEqualsNode 1 25), VoidStamp),
  (27, (BeginNode 34), VoidStamp),
  (28, (EndNode), VoidStamp),
  (29, (MergeNode  [28, 30, 36] (Some 37) 38), VoidStamp),
  (30, (EndNode), VoidStamp),
  (31, (BeginNode 30), VoidStamp),
  (32, (IfNode 26 31 27), VoidStamp),
  (33, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (34, (StoreFieldNode 34 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 33 (Some 35) None 36), VoidStamp),
  (35, (FrameState [] None None None), IllegalStamp),
  (36, (EndNode), VoidStamp),
  (37, (FrameState [] None None None), IllegalStamp),
  (38, (StoreFieldNode 38 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 3 (Some 39) None 40), VoidStamp),
  (39, (FrameState [] None None None), IllegalStamp),
  (40, (ReturnNode None None), VoidStamp)
  ]"

(* final: ConditionalEliminationTest1_test2Snippet*)
definition ConditionalEliminationTest1_test2Snippet_final :: IRGraph where  "ConditionalEliminationTest1_test2Snippet_final = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 28), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (IntVal 32 (100))), IntegerStamp 32 (100) (100)),
  (9, (ConstantNode (IntVal 32 (101))), IntegerStamp 32 (101) (101)),
  (10, (IntegerLessThanNode 1 9), VoidStamp),
  (11, (BeginNode 19), VoidStamp),
  (12, (BeginNode 14), VoidStamp),
  (13, (IfNode 41 12 11), VoidStamp),
  (14, (EndNode), VoidStamp),
  (15, (MergeNode  [14, 16, 23] (Some 24) 32), VoidStamp),
  (16, (EndNode), VoidStamp),
  (17, (BeginNode 21), VoidStamp),
  (18, (BeginNode 16), VoidStamp),
  (19, (IfNode 41 17 18), VoidStamp),
  (20, (ConstantNode (IntVal 32 (200))), IntegerStamp 32 (200) (200)),
  (21, (StoreFieldNode 21 ''org.graalvm.compiler.core.test.ConditionalEliminationTest1::sink3'' 20 (Some 22) None 23), VoidStamp),
  (22, (FrameState [] None None None), IllegalStamp),
  (23, (EndNode), VoidStamp),
  (24, (FrameState [] None None None), IllegalStamp),
  (25, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
  (26, (IntegerEqualsNode 1 25), VoidStamp),
  (27, (BeginNode 34), VoidStamp),
  (28, (EndNode), VoidStamp),
  (29, (MergeNode  [28, 30, 36] (Some 37) 38), VoidStamp),
  (30, (EndNode), VoidStamp),
  (31, (BeginNode 30), VoidStamp),
  (32, (IfNode 42 31 27), VoidStamp),
  (33, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (34, (StoreFieldNode 34 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 33 (Some 35) None 36), VoidStamp),
  (35, (FrameState [] None None None), IllegalStamp),
  (36, (EndNode), VoidStamp),
  (37, (FrameState [] None None None), IllegalStamp),
  (38, (StoreFieldNode 38 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 3 (Some 39) None 40), VoidStamp),
  (39, (FrameState [] None None None), IllegalStamp),
  (40, (ReturnNode None None), VoidStamp),
  (41, (ConstantNode (IntVal 1 (1))), VoidStamp),
  (42, (ConstantNode (IntVal 1 (0))), VoidStamp)
  ]"

value "
  eqGraph
  (runConditionalElimination
    ConditionalEliminationTest1_test2Snippet_initial)
  ConditionalEliminationTest1_test2Snippet_final
"

value "
  diffNodesGraph
  (runConditionalElimination
    ConditionalEliminationTest1_test2Snippet_initial)
  ConditionalEliminationTest1_test2Snippet_final
"

value "
  diffNodesInfo
  (runConditionalElimination
    ConditionalEliminationTest1_test2Snippet_initial)
  ConditionalEliminationTest1_test2Snippet_final
"


(* initial: ConditionalEliminationTest1_test3Snippet*)
definition ConditionalEliminationTest1_test3Snippet_initial :: IRGraph where  "ConditionalEliminationTest1_test3Snippet_initial = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 10), VoidStamp),
  (6, (BeginNode 15), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (9, (IntegerLessThanNode 1 8), VoidStamp),
  (10, (EndNode), VoidStamp),
  (11, (MergeNode  [10, 12, 18, 24, 31, 37, 43, 53, 56] (Some 57) 58), VoidStamp),
  (12, (EndNode), VoidStamp),
  (13, (BeginNode 21), VoidStamp),
  (14, (BeginNode 12), VoidStamp),
  (15, (IfNode 9 13 14), VoidStamp),
  (16, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
  (17, (IntegerLessThanNode 1 16), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (BeginNode 27), VoidStamp),
  (20, (BeginNode 18), VoidStamp),
  (21, (IfNode 17 19 20), VoidStamp),
  (22, (ConstantNode (IntVal 32 (3))), IntegerStamp 32 (3) (3)),
  (23, (IntegerLessThanNode 1 22), VoidStamp),
  (24, (EndNode), VoidStamp),
  (25, (BeginNode 33), VoidStamp),
  (26, (BeginNode 24), VoidStamp),
  (27, (IfNode 23 25 26), VoidStamp),
  (28, (ConstantNode (IntVal 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (29, (IntegerLessThanNode 1 3), VoidStamp),
  (30, (BeginNode 39), VoidStamp),
  (31, (EndNode), VoidStamp),
  (32, (BeginNode 31), VoidStamp),
  (33, (IfNode 29 32 30), VoidStamp),
  (34, (ConstantNode (IntVal 32 (-2))), IntegerStamp 32 (-2) (-2)),
  (35, (IntegerLessThanNode 1 28), VoidStamp),
  (36, (BeginNode 45), VoidStamp),
  (37, (EndNode), VoidStamp),
  (38, (BeginNode 37), VoidStamp),
  (39, (IfNode 35 38 36), VoidStamp),
  (40, (ConstantNode (IntVal 32 (-3))), IntegerStamp 32 (-3) (-3)),
  (41, (IntegerLessThanNode 1 34), VoidStamp),
  (42, (BeginNode 49), VoidStamp),
  (43, (EndNode), VoidStamp),
  (44, (BeginNode 43), VoidStamp),
  (45, (IfNode 41 44 42), VoidStamp),
  (46, (IntegerEqualsNode 1 8), VoidStamp),
  (47, (BeginNode 54), VoidStamp),
  (48, (BeginNode 51), VoidStamp),
  (49, (IfNode 46 48 47), VoidStamp),
  (50, (ConstantNode (IntVal 32 (42))), IntegerStamp 32 (42) (42)),
  (51, (StoreFieldNode 51 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' 50 (Some 52) None 53), VoidStamp),
  (52, (FrameState [] None None None), IllegalStamp),
  (53, (EndNode), VoidStamp),
  (54, (StoreFieldNode 54 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 8 (Some 55) None 56), VoidStamp),
  (55, (FrameState [] None None None), IllegalStamp),
  (56, (EndNode), VoidStamp),
  (57, (FrameState [] None None None), IllegalStamp),
  (58, (StoreFieldNode 58 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 3 (Some 59) None 60), VoidStamp),
  (59, (FrameState [] None None None), IllegalStamp),
  (60, (ReturnNode None None), VoidStamp)
  ]"

(* final: ConditionalEliminationTest1_test3Snippet*)
definition ConditionalEliminationTest1_test3Snippet_final :: IRGraph where  "ConditionalEliminationTest1_test3Snippet_final = irgraph [
  (0, (StartNode (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (IntVal 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (IntegerEqualsNode 1 3), VoidStamp),
  (5, (BeginNode 10), VoidStamp),
  (6, (BeginNode 15), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (9, (IntegerLessThanNode 1 8), VoidStamp),
  (10, (EndNode), VoidStamp),
  (11, (MergeNode  [10, 12, 18, 24, 31, 37, 43, 53, 56] (Some 57) 58), VoidStamp),
  (12, (EndNode), VoidStamp),
  (13, (BeginNode 21), VoidStamp),
  (14, (BeginNode 12), VoidStamp),
  (15, (IfNode 61 13 14), VoidStamp),
  (16, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
  (17, (IntegerLessThanNode 1 16), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (BeginNode 27), VoidStamp),
  (20, (BeginNode 18), VoidStamp),
  (21, (IfNode 61 19 20), VoidStamp),
  (22, (ConstantNode (IntVal 32 (3))), IntegerStamp 32 (3) (3)),
  (23, (IntegerLessThanNode 1 22), VoidStamp),
  (24, (EndNode), VoidStamp),
  (25, (BeginNode 33), VoidStamp),
  (26, (BeginNode 24), VoidStamp),
  (27, (IfNode 61 25 26), VoidStamp),
  (28, (ConstantNode (IntVal 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (29, (IntegerLessThanNode 1 3), VoidStamp),
  (30, (BeginNode 39), VoidStamp),
  (31, (EndNode), VoidStamp),
  (32, (BeginNode 31), VoidStamp),
  (33, (IfNode 62 32 30), VoidStamp),
  (34, (ConstantNode (IntVal 32 (-2))), IntegerStamp 32 (-2) (-2)),
  (35, (IntegerLessThanNode 1 28), VoidStamp),
  (36, (BeginNode 45), VoidStamp),
  (37, (EndNode), VoidStamp),
  (38, (BeginNode 37), VoidStamp),
  (39, (IfNode 62 38 36), VoidStamp),
  (40, (ConstantNode (IntVal 32 (-3))), IntegerStamp 32 (-3) (-3)),
  (41, (IntegerLessThanNode 1 34), VoidStamp),
  (42, (BeginNode 49), VoidStamp),
  (43, (EndNode), VoidStamp),
  (44, (BeginNode 43), VoidStamp),
  (45, (IfNode 62 44 42), VoidStamp),
  (46, (IntegerEqualsNode 1 8), VoidStamp),
  (47, (BeginNode 54), VoidStamp),
  (48, (BeginNode 51), VoidStamp),
  (49, (IfNode 62 48 47), VoidStamp),
  (50, (ConstantNode (IntVal 32 (42))), IntegerStamp 32 (42) (42)),
  (51, (StoreFieldNode 51 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' 50 (Some 52) None 53), VoidStamp),
  (52, (FrameState [] None None None), IllegalStamp),
  (53, (EndNode), VoidStamp),
  (54, (StoreFieldNode 54 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 8 (Some 55) None 56), VoidStamp),
  (55, (FrameState [] None None None), IllegalStamp),
  (56, (EndNode), VoidStamp),
  (57, (FrameState [] None None None), IllegalStamp),
  (58, (StoreFieldNode 58 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 3 (Some 59) None 60), VoidStamp),
  (59, (FrameState [] None None None), IllegalStamp),
  (60, (ReturnNode None None), VoidStamp),
  (61, (ConstantNode (IntVal 1 (1))), VoidStamp),
  (62, (ConstantNode (IntVal 1 (0))), VoidStamp)
  ]"

value "
  eqGraph
  (runConditionalElimination
    ConditionalEliminationTest1_test3Snippet_initial)
  ConditionalEliminationTest1_test3Snippet_final
"

value "
  diffNodesGraph
  (runConditionalElimination
    ConditionalEliminationTest1_test3Snippet_initial)
  ConditionalEliminationTest1_test3Snippet_final
"

value "
  diffNodesInfo
  (runConditionalElimination
    ConditionalEliminationTest1_test3Snippet_initial)
  ConditionalEliminationTest1_test3Snippet_final
"


(* initial: ConditionalEliminationTest4_test1Snippet*)
definition ConditionalEliminationTest4_test1Snippet_initial :: IRGraph where  "ConditionalEliminationTest4_test1Snippet_initial = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 8), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (EndNode), VoidStamp),
  (9, (MergeNode  [8, 10] (Some 16) 18), VoidStamp),
  (10, (EndNode), VoidStamp),
  (11, (BeginNode 15), VoidStamp),
  (12, (BeginNode 10), VoidStamp),
  (13, (IfNode 4 11 12), VoidStamp),
  (14, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (15, (ReturnNode (Some 14) None), VoidStamp),
  (16, (FrameState [] None None None), IllegalStamp),
  (17, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
  (18, (ReturnNode (Some 17) None), VoidStamp)
  ]"

(* final: ConditionalEliminationTest4_test1Snippet*)
definition ConditionalEliminationTest4_test1Snippet_final :: IRGraph where  "ConditionalEliminationTest4_test1Snippet_final = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 2 1), VoidStamp),
  (5, (BeginNode 8), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (EndNode), VoidStamp),
  (9, (MergeNode  [8, 10] (Some 16) 18), VoidStamp),
  (10, (EndNode), VoidStamp),
  (11, (BeginNode 15), VoidStamp),
  (12, (BeginNode 10), VoidStamp),
  (13, (IfNode 19 11 12), VoidStamp),
  (14, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (15, (ReturnNode (Some 14) None), VoidStamp),
  (16, (FrameState [] None None None), IllegalStamp),
  (17, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
  (18, (ReturnNode (Some 17) None), VoidStamp),
  (19, (ConstantNode (IntVal 1 (1))), VoidStamp)
  ]"

value "
  eqGraph
  (runConditionalElimination
    ConditionalEliminationTest4_test1Snippet_initial)
  ConditionalEliminationTest4_test1Snippet_final
"

value "
  diffNodesGraph
  (runConditionalElimination
    ConditionalEliminationTest4_test1Snippet_initial)
  ConditionalEliminationTest4_test1Snippet_final
"

value "
  diffNodesInfo
  (runConditionalElimination
    ConditionalEliminationTest4_test1Snippet_initial)
  ConditionalEliminationTest4_test1Snippet_final
"


(* initial: ConditionalEliminationTest4_test2Snippet*)
definition ConditionalEliminationTest4_test2Snippet_initial :: IRGraph where  "ConditionalEliminationTest4_test2Snippet_initial = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 8), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (EndNode), VoidStamp),
  (9, (MergeNode  [8, 10] (Some 16) 18), VoidStamp),
  (10, (EndNode), VoidStamp),
  (11, (BeginNode 15), VoidStamp),
  (12, (BeginNode 10), VoidStamp),
  (13, (IfNode 4 11 12), VoidStamp),
  (14, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (15, (ReturnNode (Some 14) None), VoidStamp),
  (16, (FrameState [] None None None), IllegalStamp),
  (17, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
  (18, (ReturnNode (Some 17) None), VoidStamp)
  ]"

(* final: ConditionalEliminationTest4_test2Snippet*)
definition ConditionalEliminationTest4_test2Snippet_final :: IRGraph where  "ConditionalEliminationTest4_test2Snippet_final = irgraph [
  (0, (StartNode (Some 3) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (ParameterNode 1), IntegerStamp 32 (-2147483648) (2147483647)),
  (3, (FrameState [] None None None), IllegalStamp),
  (4, (IntegerLessThanNode 1 2), VoidStamp),
  (5, (BeginNode 8), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (IfNode 4 6 5), VoidStamp),
  (8, (EndNode), VoidStamp),
  (9, (MergeNode  [8, 10] (Some 16) 18), VoidStamp),
  (10, (EndNode), VoidStamp),
  (11, (BeginNode 15), VoidStamp),
  (12, (BeginNode 10), VoidStamp),
  (13, (IfNode 19 11 12), VoidStamp),
  (14, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (15, (ReturnNode (Some 14) None), VoidStamp),
  (16, (FrameState [] None None None), IllegalStamp),
  (17, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
  (18, (ReturnNode (Some 17) None), VoidStamp),
  (19, (ConstantNode (IntVal 1 (1))), VoidStamp)
  ]"

value "
  eqGraph
  (runConditionalElimination
    ConditionalEliminationTest4_test2Snippet_initial)
  ConditionalEliminationTest4_test2Snippet_final
"

value "
  diffNodesGraph
  (runConditionalElimination
    ConditionalEliminationTest4_test2Snippet_initial)
  ConditionalEliminationTest4_test2Snippet_final
"

value "
  diffNodesInfo
  (runConditionalElimination
    ConditionalEliminationTest4_test2Snippet_initial)
  ConditionalEliminationTest4_test2Snippet_final
"

values "{
condset_implies (set conds)
(BinaryExpr BinIntegerEquals (LeafExpr 0 default_stamp) (ConstantExpr (IntVal 32 0))) False
 | conds stamps c. 
analyse ConditionalEliminationTest13_testSnippet3_initial Map.empty 12 (conds, stamps, c)}"

values "{
tryFold (IntegerEqualsNode 1 4) (hd stamps) 
 False
 | conds stamps c. 
analyse ConditionalEliminationTest13_testSnippet3_initial Map.empty 12 (conds, stamps, c)}"

values "{
(hd stamps) 4
 | conds stamps c. 
analyse ConditionalEliminationTest13_testSnippet3_initial Map.empty 12 (conds, stamps, c)}"


values "{
tryFold (IntegerEqualsNode 1 3) (hd stamps) False
 | conds stamps c. 
analyse ConditionalEliminationTest1_test2Snippet_initial Map.empty 19 (conds, stamps, c)}"


values "{
conds_implies (set conds) (hd stamps) 
(IntegerLessThanNode 1 16)
(BinaryExpr BinIntegerLessThan (LeafExpr 1 default_stamp) (ConstantExpr (IntVal 32 2)))
 | conds stamps c. 
analyse ConditionalEliminationTest1_test3Snippet_initial Map.empty 21 (conds, stamps, c)}"

values "{(hd stamps) 1
|conds stamps c.
analyse ConditionalEliminationTest1_test3Snippet_initial Map.empty 21 (conds, stamps, c)}"


values "{(conds, stamps, c)|conds stamps c.
analyse ConditionalEliminationTest1_test3Snippet_initial Map.empty 21 (conds, stamps, c)}"

values "{g'.
  (ConditionalEliminationPhase
    ({}, Map.empty)
    ConditionalEliminationTest1_test3Snippet_initial
    g'
  )
}"

values "{g'.
  (ConditionalEliminationPhase
    ({}, Map.empty)
    ConditionalEliminationTest1_test2Snippet_initial
    g'
  )
}"

end