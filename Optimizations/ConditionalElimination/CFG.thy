theory CFG
  imports Graph.IRGraph
begin

(*
 * CFG based on the org.graalvm.compiler.nodes.cfg.ControlFlowGraph
 * Page 2 on //notes/CFGNotes.pdf contains notes on the construction
 *)

datatype Block =
  BasicBlock (start_node: ID) (end_node: ID) |
  NoBlock

(* TODO: prove termination *)
function findEnd :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID list \<Rightarrow> ID" where
  "findEnd g nid [next] = findEnd g next (successors_of (kind g next))" |
  "findEnd g nid succs = nid"
  sorry termination sorry

(* TODO: prove termination *)
function findStart :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID list \<Rightarrow> ID" where
  "findStart g nid [pred] =
    (if is_AbstractBeginNode (kind g nid) then
      nid
    else
      (findStart g pred (sorted_list_of_set (predecessors g nid))))" |
  "findStart g nid preds = nid"
  sorry termination sorry

fun blockOf :: "IRGraph \<Rightarrow> ID \<Rightarrow> Block" where
  "blockOf g nid = (
    let end = (findEnd g nid (sorted_list_of_set (succ g nid))) in
    let start = (findStart g nid (sorted_list_of_set (predecessors g nid))) in
    if (start = end \<and> start = nid) then NoBlock else
    BasicBlock start end
  )"

fun succ_from_end :: "IRGraph \<Rightarrow> ID \<Rightarrow> IRNode \<Rightarrow> Block set" where
  "succ_from_end g e EndNode = {blockOf g (any_usage g e)}" |
  "succ_from_end g e (IfNode c tb fb) = {blockOf g tb, blockOf g fb}" |
  "succ_from_end g e (LoopEndNode begin) = {blockOf g begin}" |
  "succ_from_end g e _ = (if (is_AbstractEndNode (kind g e))
    then (set (map (blockOf g) (successors_of (kind g e))))
    else {})"

fun succ :: "IRGraph \<Rightarrow> Block \<Rightarrow> Block set" where
  "succ g (BasicBlock start end) = succ_from_end g end (kind g end)" |
  "succ g _ = {}"

fun register_by_pred :: "IRGraph \<Rightarrow> ID \<Rightarrow> Block option" where
  "register_by_pred g nid = (
    case kind g (end_node (blockOf g nid)) of
    (IfNode c tb fb) \<Rightarrow> Some (blockOf g nid) |
    k \<Rightarrow> (if (is_AbstractEndNode k) then Some (blockOf g nid) else None)
  )"

fun pred_from_start :: "IRGraph \<Rightarrow> ID \<Rightarrow> IRNode \<Rightarrow> Block set" where
  "pred_from_start g s (MergeNode ends _ _) = set (map (blockOf g) ends)" |
  "pred_from_start g s (LoopBeginNode ends _ _ _) = set (map (blockOf g) ends)" |
  "pred_from_start g s (LoopEndNode begin) = {blockOf g begin}" |
  "pred_from_start g s _ = set (List.map_filter (register_by_pred g) (sorted_list_of_set (predecessors g s)))"

fun pred :: "IRGraph \<Rightarrow> Block \<Rightarrow> Block set" where
  "pred g (BasicBlock start end) = pred_from_start g start (kind g start)" |
  "pred g _ = {}"

inductive dominates :: "IRGraph \<Rightarrow> Block \<Rightarrow> Block \<Rightarrow> bool" ("_ \<turnstile> _ \<ge>\<ge> _" 20) where
  "\<lbrakk>(d = n) \<or> ((pred g n \<noteq> {}) \<and> (\<forall>p \<in> pred g n . (g \<turnstile> d \<ge>\<ge> p)))\<rbrakk> \<Longrightarrow> dominates g d n"
code_pred [show_modes] dominates .

inductive postdominates :: "IRGraph \<Rightarrow> Block \<Rightarrow> Block \<Rightarrow> bool" ("_ \<turnstile> _ \<le>\<le> _" 20) where
  "\<lbrakk>(z = n) \<or> ((succ g n \<noteq> {}) \<and> (\<forall>s \<in> succ g n . (g \<turnstile> z \<le>\<le> s)))\<rbrakk> \<Longrightarrow> postdominates g z n"
code_pred [show_modes] postdominates .

inductive strictly_dominates :: "IRGraph \<Rightarrow> Block \<Rightarrow> Block \<Rightarrow> bool" ("_ \<turnstile> _ >> _" 20) where
  "\<lbrakk>(g \<turnstile> d \<ge>\<ge> n); (d \<noteq> n)\<rbrakk> \<Longrightarrow> strictly_dominates g d n"
code_pred [show_modes] strictly_dominates .

inductive strictly_postdominates :: "IRGraph \<Rightarrow> Block \<Rightarrow> Block \<Rightarrow> bool" ("_ \<turnstile> _ << _" 20) where
  "\<lbrakk>(g \<turnstile> d \<le>\<le> n); (d \<noteq> n)\<rbrakk> \<Longrightarrow> strictly_postdominates g d n"
code_pred [show_modes] strictly_postdominates .

lemma "pred g nid = {} \<longrightarrow> \<not>(\<exists> d . (d \<noteq> nid) \<and> (g \<turnstile> d \<ge>\<ge> nid))"
  using dominates.cases by blast

lemma "succ g nid = {} \<longrightarrow> \<not>(\<exists> d . (d \<noteq> nid) \<and> (g \<turnstile> d \<le>\<le> nid))"
  using postdominates.cases by blast

lemma "pred g nid = {} \<longrightarrow> \<not>(\<exists> d . (g \<turnstile> d >> nid))"
  using dominates.simps strictly_dominates.simps by presburger

lemma "succ g nid = {} \<longrightarrow> \<not>(\<exists> d . (g \<turnstile> d << nid))"
  using postdominates.simps strictly_postdominates.simps by presburger

inductive wf_cfg :: "IRGraph \<Rightarrow> bool" where
  "\<lbrakk>\<forall> nid \<in> ids g . (blockOf g nid \<noteq> NoBlock) \<longrightarrow> (g \<turnstile> (blockOf g 0) \<ge>\<ge> (blockOf g nid))\<rbrakk>
  \<Longrightarrow> wf_cfg g"
code_pred [show_modes] wf_cfg .

inductive immediately_dominates :: "IRGraph \<Rightarrow> Block \<Rightarrow> Block \<Rightarrow> bool" ("_ \<turnstile> _ idom _" 20) where
  "\<lbrakk>(g \<turnstile> d >> n); (\<forall> w \<in> ids g . (g \<turnstile> (blockOf g w) >> n) \<longrightarrow> (g \<turnstile> (blockOf g w) \<ge>\<ge> d))\<rbrakk> \<Longrightarrow> immediately_dominates g d n"
code_pred [show_modes] immediately_dominates .

definition simple_if :: IRGraph where
  "simple_if = irgraph [
    (0, StartNode None 2, VoidStamp),
    (1, ParameterNode 0, default_stamp),
    (2, IfNode 1 3 4, VoidStamp),
    (3, BeginNode 5, VoidStamp),
    (4, BeginNode 6, VoidStamp),
    (5, EndNode, VoidStamp),
    (6, EndNode, VoidStamp),
    (7, ParameterNode 1, default_stamp),
    (8, ParameterNode 2, default_stamp),
    (9, AddNode 7 8, default_stamp),
    (10, MergeNode [5,6] None 12, VoidStamp),
    (11, ValuePhiNode 11 [9,7] 10, default_stamp),
    (12, ReturnNode (Some 11) None, default_stamp)
  ]"

(*
        Block 1:
        0 StartNode
        2 IfNode

  Block 2:        Block 3:
  3 BeginNode     4 BeginNode
  5 EndNode       6 EndNode

        Block 4:
        10 MergeNode
        12 ReturnNode
*)

value "wf_cfg simple_if"

(**** Dominator ****)
(* All true, Block 1 dominates everything *)
value "simple_if \<turnstile> blockOf simple_if 0 \<ge>\<ge> blockOf simple_if 0"
value "simple_if \<turnstile> blockOf simple_if 0 \<ge>\<ge> blockOf simple_if 3"
value "simple_if \<turnstile> blockOf simple_if 0 \<ge>\<ge> blockOf simple_if 4"
value "simple_if \<turnstile> blockOf simple_if 0 \<ge>\<ge> blockOf simple_if 12"

(* Block 2 only dominates itself *)
value "simple_if \<turnstile> blockOf simple_if 3 \<ge>\<ge> blockOf simple_if 0"
value "simple_if \<turnstile> blockOf simple_if 3 \<ge>\<ge> blockOf simple_if 3"
value "simple_if \<turnstile> blockOf simple_if 3 \<ge>\<ge> blockOf simple_if 4"
value "simple_if \<turnstile> blockOf simple_if 3 \<ge>\<ge> blockOf simple_if 12"

(* Block 3 only dominates itself *)
value "simple_if \<turnstile> blockOf simple_if 4 \<ge>\<ge> blockOf simple_if 0"
value "simple_if \<turnstile> blockOf simple_if 4 \<ge>\<ge> blockOf simple_if 3"
value "simple_if \<turnstile> blockOf simple_if 4 \<ge>\<ge> blockOf simple_if 4"
value "simple_if \<turnstile> blockOf simple_if 4 \<ge>\<ge> blockOf simple_if 12"

(* Block 4 only dominates itself *)
value "simple_if \<turnstile> blockOf simple_if 12 \<ge>\<ge> blockOf simple_if 0"
value "simple_if \<turnstile> blockOf simple_if 12 \<ge>\<ge> blockOf simple_if 3"
value "simple_if \<turnstile> blockOf simple_if 12 \<ge>\<ge> blockOf simple_if 4"
value "simple_if \<turnstile> blockOf simple_if 12 \<ge>\<ge> blockOf simple_if 12"

(**** Postdominates ****)
(* Block 1 only postdominates itself *)
value "simple_if \<turnstile> blockOf simple_if 0 \<le>\<le> blockOf simple_if 0"
value "simple_if \<turnstile> blockOf simple_if 0 \<le>\<le> blockOf simple_if 3"
value "simple_if \<turnstile> blockOf simple_if 0 \<le>\<le> blockOf simple_if 4"
value "simple_if \<turnstile> blockOf simple_if 0 \<le>\<le> blockOf simple_if 12"

(* Block 2 only postdominates itself *)
value "simple_if \<turnstile> blockOf simple_if 3 \<le>\<le> blockOf simple_if 0"
value "simple_if \<turnstile> blockOf simple_if 3 \<le>\<le> blockOf simple_if 3"
value "simple_if \<turnstile> blockOf simple_if 3 \<le>\<le> blockOf simple_if 4"
value "simple_if \<turnstile> blockOf simple_if 3 \<le>\<le> blockOf simple_if 12"

(* Block 3 only postdominates itself *)
value "simple_if \<turnstile> blockOf simple_if 4 \<le>\<le> blockOf simple_if 0"
value "simple_if \<turnstile> blockOf simple_if 4 \<le>\<le> blockOf simple_if 3"
value "simple_if \<turnstile> blockOf simple_if 4 \<le>\<le> blockOf simple_if 4"
value "simple_if \<turnstile> blockOf simple_if 4 \<le>\<le> blockOf simple_if 12"

(* Block 4 postdominates every other block *)
value "simple_if \<turnstile> blockOf simple_if 12 \<le>\<le> blockOf simple_if 0"
value "simple_if \<turnstile> blockOf simple_if 12 \<le>\<le> blockOf simple_if 3"
value "simple_if \<turnstile> blockOf simple_if 12 \<le>\<le> blockOf simple_if 4"
value "simple_if \<turnstile> blockOf simple_if 12 \<le>\<le> blockOf simple_if 12"

value "blockOf simple_if 0" (* Block 1 *)
value "blockOf simple_if 1" (* No Block *)
value "blockOf simple_if 2" (* Block 1 *)
value "blockOf simple_if 3" (* Block 2 *)
value "blockOf simple_if 4" (* Block 3 *)
value "blockOf simple_if 5" (* Block 2 *)
value "blockOf simple_if 6" (* Block 3 *)
value "blockOf simple_if 7" (* No Block *)
value "blockOf simple_if 8" (* No Block *)
value "blockOf simple_if 9" (* No Block *)
value "blockOf simple_if 10" (* Block 4 *)
value "blockOf simple_if 11" (* No Block *)
value "blockOf simple_if 12" (* Block 4 *)

(* Block 1 *)
value "pred simple_if (blockOf simple_if 0)" (* {} *)
value "succ simple_if (blockOf simple_if 0)" (* {Block 2, Block 3} *)
(* Block 2 *)
value "pred simple_if (blockOf simple_if 3)" (* {Block 1} *)
value "succ simple_if (blockOf simple_if 3)" (* {Block 4} *)
(* Block 3 *)
value "pred simple_if (blockOf simple_if 4)" (* {Block 1} *)
value "succ simple_if (blockOf simple_if 4)" (* {Block 4} *)
(* Block 4 *)
value "pred simple_if (blockOf simple_if 10)" (* {Block 2, Block 3} *)
value "succ simple_if (blockOf simple_if 10)" (* {} *)

(*
definition loop :: IRGraph where
  "loop =
    (add_node 13 (ReturnNode (Some 7) None)
    (add_node 12 (LoopEndNode 3)
    (add_node 11 (BeginNode 12)
    (add_node 10 (IfNode 9 11 13)
    (add_node 9 (IntegerLessThanNode 7 6)
    (add_node 8 (AddNode 7 5)
    (add_node 7 (ValuePhiNode [4,8] 3)
    (add_node 6 (ParameterNode 0)
    (add_node 5 (ConstantNode 1)
    (add_node 4 (ConstantNode 0)
    (add_node 3 (LoopBeginNode [2,12] None None 10)
    (add_node 2 (EndNode)
    (add_node 1 (BeginNode 2)
    (add_node 0 (StartNode None 1)
    empty_graph))))))))))))))"

(*
            Block 1:
            1 BeginNode
            2 EndNode

            Block 2:
            3 LoopBeginNode
            10 IfNode

    Block 3:              Block 4:
    11 BeginNode          13 ReturnNode
    12 LoopEndNode
*)

value "blockOf loop 1" (* Block 1 *)
value "blockOf loop 2" (* Block 1 *)
value "blockOf loop 3" (* Block 2 *)
value "blockOf loop 10" (* Block 2 *)
value "blockOf loop 11" (* Block 3 *)
value "blockOf loop 12" (* Block 3 *)
value "blockOf loop 13" (* Block 4 *)

(* Block 1 *)
value "pred loop (blockOf loop 1)" (* {} *)
value "succ loop (blockOf loop 1)" (* {Block 2} *)
(* Block 2 *)
value "pred loop (blockOf loop 3)" (* {Block 1, Block 3} *)
value "succ loop (blockOf loop 3)" (* {Block 3, Block 4} *)
(* Block 3 *)
value "pred loop (blockOf loop 11)" (* {Block 2} *)
value "succ loop (blockOf loop 11)" (* {Block 2} *)
(* Block 4 *)
value "pred loop (blockOf loop 13)" (* {Block 2} *)
value "succ loop (blockOf loop 13)" (* {} *)
*)

definition ConditionalEliminationTest1_test1Snippet_initial :: IRGraph where
  "ConditionalEliminationTest1_test1Snippet_initial = irgraph [
  (0, (StartNode  (Some 2) 7), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState []  None None None), IllegalStamp),
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
  (14, (StoreFieldNode 14 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' 13  (Some 15)  None 18), VoidStamp),
  (15, (FrameState []  None None None), IllegalStamp),
  (16, (EndNode), VoidStamp),
  (17, (MergeNode  [16, 18]  (Some 19) 24), VoidStamp),
  (18, (EndNode), VoidStamp),
  (19, (FrameState []  None None None), IllegalStamp),
  (20, (ConstantNode (IntVal 32 (101))), IntegerStamp 32 (101) (101)),
  (21, (IntegerLessThanNode 1 20), VoidStamp),
  (22, (BeginNode 30), VoidStamp),
  (23, (BeginNode 25), VoidStamp),
  (24, (IfNode 21 23 22), VoidStamp),
  (25, (EndNode), VoidStamp),
  (26, (MergeNode  [25, 27, 34]  (Some 35) 43), VoidStamp),
  (27, (EndNode), VoidStamp),
  (28, (BeginNode 32), VoidStamp),
  (29, (BeginNode 27), VoidStamp),
  (30, (IfNode 4 28 29), VoidStamp),
  (31, (ConstantNode (IntVal 32 (200))), IntegerStamp 32 (200) (200)),
  (32, (StoreFieldNode 32 ''org.graalvm.compiler.core.test.ConditionalEliminationTest1::sink3'' 31  (Some 33)  None 34), VoidStamp),
  (33, (FrameState []  None None None), IllegalStamp),
  (34, (EndNode), VoidStamp),
  (35, (FrameState []  None None None), IllegalStamp),
  (36, (ConstantNode (IntVal 32 (2))), IntegerStamp 32 (2) (2)),
  (37, (IntegerEqualsNode 1 36), VoidStamp),
  (38, (BeginNode 45), VoidStamp),
  (39, (EndNode), VoidStamp),
  (40, (MergeNode  [39, 41, 47]  (Some 48) 49), VoidStamp),
  (41, (EndNode), VoidStamp),
  (42, (BeginNode 41), VoidStamp),
  (43, (IfNode 37 42 38), VoidStamp),
  (44, (ConstantNode (IntVal 32 (1))), IntegerStamp 32 (1) (1)),
  (45, (StoreFieldNode 45 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 44  (Some 46)  None 47), VoidStamp),
  (46, (FrameState []  None None None), IllegalStamp),
  (47, (EndNode), VoidStamp),
  (48, (FrameState []  None None None), IllegalStamp),
  (49, (StoreFieldNode 49 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 3  (Some 50)  None 51), VoidStamp),
  (50, (FrameState []  None None None), IllegalStamp),
  (51, (ReturnNode  None  None), VoidStamp)
  ]"

value "blockOf ConditionalEliminationTest1_test1Snippet_initial 0" (* Block 0 *)
value "blockOf ConditionalEliminationTest1_test1Snippet_initial 7" (* Block 0 *)

value "blockOf ConditionalEliminationTest1_test1Snippet_initial 6" (* Block 1 *)
value "blockOf ConditionalEliminationTest1_test1Snippet_initial 12" (* Block 1 *)

value "blockOf ConditionalEliminationTest1_test1Snippet_initial 11" (* Block 2 *)
value "blockOf ConditionalEliminationTest1_test1Snippet_initial 14" (* Block 2 *)
value "blockOf ConditionalEliminationTest1_test1Snippet_initial 18" (* Block 2 *)

value "blockOf ConditionalEliminationTest1_test1Snippet_initial 10" (* Block 3 *)
value "blockOf ConditionalEliminationTest1_test1Snippet_initial 16" (* Block 3 *)

value "blockOf ConditionalEliminationTest1_test1Snippet_initial 17" (* Block 4 *)
value "blockOf ConditionalEliminationTest1_test1Snippet_initial 24" (* Block 4 *)

value "blockOf ConditionalEliminationTest1_test1Snippet_initial 23" (* Block 5 *)
value "blockOf ConditionalEliminationTest1_test1Snippet_initial 25" (* Block 5 *)

value "blockOf ConditionalEliminationTest1_test1Snippet_initial 22" (* Block 6*)
value "blockOf ConditionalEliminationTest1_test1Snippet_initial 30" (* Block 6 *)

value "blockOf ConditionalEliminationTest1_test1Snippet_initial 28" (* Block 7 *)
value "blockOf ConditionalEliminationTest1_test1Snippet_initial 32" (* Block 7 *)
value "blockOf ConditionalEliminationTest1_test1Snippet_initial 34" (* Block 7 *)

value "blockOf ConditionalEliminationTest1_test1Snippet_initial 29" (* Block 8 *)
value "blockOf ConditionalEliminationTest1_test1Snippet_initial 27" (* Block 8 *)

value "blockOf ConditionalEliminationTest1_test1Snippet_initial 26" (* Block 9 *)
value "blockOf ConditionalEliminationTest1_test1Snippet_initial 43" (* Block 9 *)

value "blockOf ConditionalEliminationTest1_test1Snippet_initial 42" (* Block 10 *)
value "blockOf ConditionalEliminationTest1_test1Snippet_initial 41" (* Block 10 *)

value "blockOf ConditionalEliminationTest1_test1Snippet_initial 38" (* Block 11 *)
value "blockOf ConditionalEliminationTest1_test1Snippet_initial 45" (* Block 11 *)
value "blockOf ConditionalEliminationTest1_test1Snippet_initial 47" (* Block 11 *)

value "blockOf ConditionalEliminationTest1_test1Snippet_initial 5" (* Block 12 *)
value "blockOf ConditionalEliminationTest1_test1Snippet_initial 39" (* Block 12 *)

value "blockOf ConditionalEliminationTest1_test1Snippet_initial 40" (* Block 13 *)
value "blockOf ConditionalEliminationTest1_test1Snippet_initial 49" (* Block 13 *)
value "blockOf ConditionalEliminationTest1_test1Snippet_initial 51" (* Block 13 *)

(* Block 0 *)
value "pred ConditionalEliminationTest1_test1Snippet_initial
  (blockOf ConditionalEliminationTest1_test1Snippet_initial 0)" (* {} *)
value "succ ConditionalEliminationTest1_test1Snippet_initial
  (blockOf ConditionalEliminationTest1_test1Snippet_initial 0)" (* {Block 1, Block 12} *)

(* Block 1 *)
value "pred ConditionalEliminationTest1_test1Snippet_initial
  (blockOf ConditionalEliminationTest1_test1Snippet_initial 6)" (* {Block 1} *)
value "succ ConditionalEliminationTest1_test1Snippet_initial
  (blockOf ConditionalEliminationTest1_test1Snippet_initial 6)" (* {Block 2, Block 3} *)

(* Block 2 *)
value "pred ConditionalEliminationTest1_test1Snippet_initial
  (blockOf ConditionalEliminationTest1_test1Snippet_initial 14)" (* {Block 1} *)
value "succ ConditionalEliminationTest1_test1Snippet_initial
  (blockOf ConditionalEliminationTest1_test1Snippet_initial 14)" (* {Block 4} *)

(* Block 3 *)
value "pred ConditionalEliminationTest1_test1Snippet_initial
  (blockOf ConditionalEliminationTest1_test1Snippet_initial 10)" (* {Block 1} *)
value "succ ConditionalEliminationTest1_test1Snippet_initial
  (blockOf ConditionalEliminationTest1_test1Snippet_initial 10)" (* {Block 4} *)

(* Block 4 *)
value "pred ConditionalEliminationTest1_test1Snippet_initial
  (blockOf ConditionalEliminationTest1_test1Snippet_initial 24)" (* {Block 2, Block 3} *)
value "succ ConditionalEliminationTest1_test1Snippet_initial
  (blockOf ConditionalEliminationTest1_test1Snippet_initial 24)" (* {Block 5, Block 6} *)

(* Block 5 *)
value "pred ConditionalEliminationTest1_test1Snippet_initial
  (blockOf ConditionalEliminationTest1_test1Snippet_initial 23)" (* {Block 4} *)
value "succ ConditionalEliminationTest1_test1Snippet_initial
  (blockOf ConditionalEliminationTest1_test1Snippet_initial 23)" (* {Block 9} *)

(* Block 6 *)
value "pred ConditionalEliminationTest1_test1Snippet_initial
  (blockOf ConditionalEliminationTest1_test1Snippet_initial 22)" (* {Block 4} *)
value "succ ConditionalEliminationTest1_test1Snippet_initial
  (blockOf ConditionalEliminationTest1_test1Snippet_initial 22)" (* {Block 7, Block 8} *)

(* Block 7 *)
value "pred ConditionalEliminationTest1_test1Snippet_initial
  (blockOf ConditionalEliminationTest1_test1Snippet_initial 32)" (* {Block 6} *)
value "succ ConditionalEliminationTest1_test1Snippet_initial
  (blockOf ConditionalEliminationTest1_test1Snippet_initial 32)" (* {Block 9} *)

(* Block 8 *)
value "pred ConditionalEliminationTest1_test1Snippet_initial
  (blockOf ConditionalEliminationTest1_test1Snippet_initial 29)" (* {Block 6} *)
value "succ ConditionalEliminationTest1_test1Snippet_initial
  (blockOf ConditionalEliminationTest1_test1Snippet_initial 29)" (* {Block 9} *)

(* Block 9 *)
value "pred ConditionalEliminationTest1_test1Snippet_initial
  (blockOf ConditionalEliminationTest1_test1Snippet_initial 43)" (* {Block 5, Block 7, Block 8} *)
value "succ ConditionalEliminationTest1_test1Snippet_initial
  (blockOf ConditionalEliminationTest1_test1Snippet_initial 43)" (* {Block 10, Block 11} *)

(* Block 10 *)
value "pred ConditionalEliminationTest1_test1Snippet_initial
  (blockOf ConditionalEliminationTest1_test1Snippet_initial 42)" (* {Block 9} *)
value "succ ConditionalEliminationTest1_test1Snippet_initial
  (blockOf ConditionalEliminationTest1_test1Snippet_initial 42)" (* {Block 13} *)

(* Block 11 *)
value "pred ConditionalEliminationTest1_test1Snippet_initial
  (blockOf ConditionalEliminationTest1_test1Snippet_initial 45)" (* {Block 9} *)
value "succ ConditionalEliminationTest1_test1Snippet_initial
  (blockOf ConditionalEliminationTest1_test1Snippet_initial 45)" (* {Block 13} *)

(* Block 12 *)
value "pred ConditionalEliminationTest1_test1Snippet_initial
  (blockOf ConditionalEliminationTest1_test1Snippet_initial 5)" (* {Block 0} *)
value "succ ConditionalEliminationTest1_test1Snippet_initial
  (blockOf ConditionalEliminationTest1_test1Snippet_initial 5)" (* {Block 13} *)

(* Block 13 *)
value "pred ConditionalEliminationTest1_test1Snippet_initial
  (blockOf ConditionalEliminationTest1_test1Snippet_initial 49)" (* {Block 10, Block 11, Block 12} *)
value "succ ConditionalEliminationTest1_test1Snippet_initial
  (blockOf ConditionalEliminationTest1_test1Snippet_initial 49)" (* {} *)

end