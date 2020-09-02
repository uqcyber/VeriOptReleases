theory InductiveSemantics 
  imports
    "AbsGraph"
    "HOL-Library.Datatype_Records"
    "HOL-Library.LaTeXsugar"
    (*"HOL-Library.OptionalSugar"*)
begin

type_synonym field_name = string

datatype Value =
  UndefVal |
  IntVal int

datatype EvalState = 
  EvalState 
    (s_graph: "IRGraph")
    (s_phi: "ID \<Rightarrow> Value")
    (s_params: "Value list")
    (s_scope: "string \<Rightarrow> Value")
    (s_heap: "ID \<rightharpoonup> (field_name \<rightharpoonup> Value)")
    (s_flow: "ID \<Rightarrow> nat")

type_synonym EvalNode = "ID \<times> IRNode \<times> EvalState"

(* Adds the ability to update fields of datatype without making it a record *)
local_setup \<open>Datatype_Records.mk_update_defs \<^type_name>\<open>EvalState\<close>\<close>

(* Get the type of node for a node id in an eval state *)
fun get_node :: "ID \<Rightarrow> EvalState \<Rightarrow> IRNode" where
  "get_node n state = ((g_nodes (s_graph state)) n)"

fun get_input :: "ID \<Rightarrow> EvalState \<Rightarrow> nat \<Rightarrow> ID" where 
  "get_input n state i = (nth (g_inputs (s_graph state) n) i)"

(* Get the nth input edge of a node id in an eval state *)
fun input :: "ID \<Rightarrow> EvalState \<Rightarrow> nat \<Rightarrow> EvalNode" where
  "input nid state i = 
    (let next_id = (get_input nid state i) in
    (next_id, (get_node next_id state), state))"

fun get_successor :: "ID \<Rightarrow> EvalState \<Rightarrow> nat \<Rightarrow> ID" where
  "get_successor n state i = (nth (g_successors (s_graph state) n) i)"

(* Get the nth successor edge of a node id in an eval state *)
fun successor :: "ID \<Rightarrow> EvalState \<Rightarrow> nat \<Rightarrow> EvalNode" where
  "successor nid state i =
    (let next_id = (get_successor nid state 0) in
    (next_id, (get_node next_id state), state))"

fun get_usage :: "ID \<Rightarrow> EvalState \<Rightarrow> nat \<Rightarrow> ID" where
  "get_usage nid state i =
    (nth (sorted_list_of_set (g_usages (s_graph state) nid)) i)"

(* Get the nth usage edge of a node id in an eval state *)
fun usage :: "ID \<Rightarrow> EvalState \<Rightarrow> nat \<Rightarrow> EvalNode"  where
  "usage nid state i =
    (let use = (get_usage nid state i) in 
    (use, (get_node use state), state))"

(*
   ====
   Functions to aid evaluating expressions
   ====
*)
fun val_to_bool :: "Value \<Rightarrow> bool" where
  "val_to_bool (IntVal x) = (if x = 0 then False else True)" |
  "val_to_bool (UndefVal) = False"

fun bool_to_val :: "bool \<Rightarrow> Value" where
  "bool_to_val True = (IntVal 1)" |
  "bool_to_val False = (IntVal 0)"

fun unary_expr :: "IRNode \<Rightarrow> Value \<Rightarrow> Value" where
  "unary_expr AbsNode (IntVal x) = (IntVal (if (x < 0) then -x else x))" |
  "unary_expr NegateNode x = (bool_to_val (\<not>(val_to_bool x)))" |
  "unary_expr _ _ = UndefVal"

fun binary_bool_expr :: "IRNode \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> Value" where
  "binary_bool_expr AndNode x y = (bool_to_val (x \<and> y))" |
  "binary_bool_expr OrNode x y = (bool_to_val (x \<or> y))" |
  "binary_bool_expr XorNode x y = (bool_to_val ((x \<or> y) \<and> \<not>(x \<and> y)))" |
  "binary_bool_expr _ _ _ = UndefVal"

fun binary_expr :: "IRNode \<Rightarrow> Value \<Rightarrow> Value \<Rightarrow> Value" where
  "binary_expr AddNode (IntVal x) (IntVal y) = (IntVal (x + y))" |
  "binary_expr SubNode (IntVal x) (IntVal y) = (IntVal (x - y))" |
  "binary_expr MulNode (IntVal x) (IntVal y) = (IntVal (x * y))" |
  "binary_expr AndNode x y = (binary_bool_expr AddNode (val_to_bool x) (val_to_bool y))" |
  "binary_expr OrNode x y = (binary_bool_expr OrNode (val_to_bool x) (val_to_bool y))" |
  "binary_expr XorNode x y = (binary_bool_expr XorNode (val_to_bool x) (val_to_bool y))" |
  "binary_expr IntegerLessThanNode (IntVal x) (IntVal y) = (bool_to_val (x < y))" |
  "binary_expr IntegerEqualsNode (IntVal x) (IntVal y) = (bool_to_val (x = y))" |
  "binary_expr _ _ _ = UndefVal"

(*
  ====
  Funtions to filter different types of nodes
  ====
*)
fun is_unary_node :: "IRNode \<Rightarrow> bool" where
  "is_unary_node AbsNode = True" |
  "is_unary_node NegateNode = True" |
  "is_unary_node _ = False"

fun is_binary_node :: "IRNode \<Rightarrow> bool" where
  "is_binary_node AddNode = True" |
  "is_binary_node SubNode = True" |
  "is_binary_node MulNode = True" |
  "is_binary_node AndNode = True" |
  "is_binary_node OrNode = True" |
  "is_binary_node XorNode = True" |
  "is_binary_node _ = False"

fun is_merge_node :: "IRNode \<Rightarrow> bool" where
  "is_merge_node MergeNode = True" |
  "is_merge_node LoopBeginNode = True" |
  "is_merge_node _ = False"

fun is_end_node :: "IRNode \<Rightarrow> bool" where
  "is_end_node EndNode = True" |
  "is_end_node LoopEndNode = True" |
  "is_end_node _ = False"

fun is_phi_node :: "IRNode \<Rightarrow> bool" where
  "is_phi_node PhiNode = True" |
  "is_phi_node _ = False"

(* 
update_state f a b = f'
in the function f', passing a results in b, passing
any other parameter, x, results in f(x)
*)
fun update_state :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b)" where
  "update_state scope ident val = (\<lambda> x. (if x = ident then val else (scope x)))"

(* Update the scope to map a new string to a value *)
fun add_value :: "EvalState \<Rightarrow> string \<Rightarrow> Value \<Rightarrow> EvalState" 
  ("_[[_\<rightarrow>_]]" 55)
  where
  "add_value state ident val = 
    (let scope = (s_scope state) in
    update_s_scope (\<lambda>_. (update_state scope ident val)) state)"

(* Update the heap to map a new id to an empty map *)
fun add_instance :: "EvalState \<Rightarrow> ID \<Rightarrow> EvalState"
where
  "add_instance state node =
    (let heap = (s_heap state) in
    update_s_heap (\<lambda>_. (heap(node\<mapsto>Map.empty))) state)"

(* Lookup a field_name in a node id *)
fun lookup_field :: "EvalState \<Rightarrow> ID \<Rightarrow> field_name \<Rightarrow> Value" where
  "lookup_field state n field = (case ((s_heap state) n) of 
    None \<Rightarrow> UndefVal |
    Some class \<Rightarrow> (case (class field) of
      None \<Rightarrow> UndefVal |
      Some val \<Rightarrow> val))"

(*
fun store_field :: "EvalState \<Rightarrow> ID \<Rightarrow> field_name \<Rightarrow> Value \<Rightarrow> EvalState" where
  "store_field state n field val = (case ((s_heap state) n) of
    None \<Rightarrow> state |
    Some class \<Rightarrow> 
*)

(*
(* Yoinked from https://www.isa-afp.org/browser_info/Isabelle2012/HOL/List-Index/List_Index.html*)
primrec find_index :: "('a => bool) => 'a list => nat" where
"find_index _ [] = 0" |
"find_index P (x#xs) = (if P x then 0 else find_index P xs + 1)"

definition index_list :: "'a list => 'a => nat" where
"index_list xs = (\<lambda>a. find_index (\<lambda>x. x=a) xs)"
*)

fun philist :: "EvalNode \<Rightarrow> EvalNode list" where
  "philist (n, node, s) = (if (is_merge_node node)
      then 
        (map (\<lambda>x. (x, (get_node x s), s))
          (filter (\<lambda>x.(is_phi_node (get_node x s)))
            (sorted_list_of_set (g_usages (s_graph s) n))))
      else [])"

(*
fun ntharg :: "EvalNode \<Rightarrow> nat \<Rightarrow> EvalNode" where
  "ntharg (n, node, s) k = input n s k"

fun index :: "EvalNode \<Rightarrow> EvalNode \<Rightarrow> nat" where
  "index (n, node, s) (n', node', s') = index_list (g_inputs (s_graph s) n) n'"
*)

fun set_pred :: "EvalNode \<Rightarrow> nat \<Rightarrow> EvalState" where
  "set_pred (p, node, s) i = (let preds = (s_flow s) in
    (update_s_flow (\<lambda>_. (update_state preds i p)) s))"

fun find_pred :: "EvalNode \<Rightarrow> EvalNode" where
  "find_pred (n, node, s) = (let p = ((s_flow s) n) in
    (p, (get_node p s), s))"

fun phi_input :: "EvalNode \<Rightarrow> EvalNode" where
  "phi_input (n, node, s) = (
    let merge = (get_input n s 0) in (
    let i = ((s_flow s) merge) in
    let input = (get_input n s (i + 1)) in
    (input, (get_node input s), s)))"

inductive
  eval :: "EvalNode \<Rightarrow> EvalState \<times> Value \<Rightarrow> bool" ("_\<mapsto>_" 55)
  where

  StartNode: "\<lbrakk>(successor num s 0) \<mapsto> succ\<rbrakk> 
              \<Longrightarrow> (num, StartNode, s) \<mapsto> succ" |

  ParameterNode: "(num, (ParameterNode i), s) \<mapsto> (s, (IntVal i))" |

  ConstantNode: "(num, (ConstantNode c), s) \<mapsto> (s, (IntVal c))" |

  UnaryNode: "\<lbrakk>is_unary_node node;
              (input num s 0) \<mapsto> (s1, v1)\<rbrakk> 
              \<Longrightarrow> (num, node, s) \<mapsto> (s1, (unary_expr node v1))" |

  BinaryNode: "\<lbrakk>is_binary_node node;
                (input num s 0) \<mapsto> (s1, v1);
                (input num s1 1) \<mapsto> (s2, v2)\<rbrakk> 
                \<Longrightarrow> (num, node, s) \<mapsto> (s2, (binary_expr node v1 v2))" |

  IfNodeTrue: "\<lbrakk>(input num s 0) \<mapsto> (s1, v1);
                (val_to_bool v1);
                (successor num s1 0) \<mapsto> s2\<rbrakk> 
                \<Longrightarrow> (num, IfNode, s) \<mapsto> s2" |

  IfNodeFalse: "\<lbrakk>(input num s 0) \<mapsto> (s1, v1);
                 (\<not>(val_to_bool v1));
                 (successor num s1 1) \<mapsto> s2\<rbrakk> 
                 \<Longrightarrow> (num, IfNode, s) \<mapsto> s2" |

  ReturnNode: "\<lbrakk>(input n s 0) \<mapsto> (s1, v1)\<rbrakk> 
              \<Longrightarrow> (n, ReturnNode, s) \<mapsto> (s1[[''RETURN''\<rightarrow>v1]], v1)" |

(* WIP *)

  NewInstanceNode: "(n, NewInstanceNode cname, s) \<mapsto> ((add_instance s n), UndefVal)" |

  LoadFieldNode: "\<lbrakk>(input n s 0) \<mapsto> (s1, v1)\<rbrakk>
                  \<Longrightarrow> (n, LoadFieldNode field, s) 
                      \<mapsto> (s1, (lookup_field s1 (get_input n s 0) field))" |

(*
  StoreFieldNode: "(n, StoreFieldNode field, s) \<mapsto> (s, UndefVal)" |
*)

(* Inductive is very unhappy about this, can longer prove
  MergeNodes: "\<lbrakk>is_merge_node node;
                phis = (philist (n, node, s));
                phi' = {p \<in> (set phis) . ((phi_input p) \<mapsto> (_, v))}\<rbrakk> 
                \<Longrightarrow> (n, node, s) \<mapsto> (s, UndefVal)" |
*)

(* I _think_ the (successor n s i) = whatever makes the set 
  comprehension of eval understandably unhappy
  EndNodes: "\<lbrakk>is_end_node node;
              merge = (usage n s 0);
              (successor n s i) = merge\<rbrakk> 
              \<Longrightarrow> (n, node, s) \<mapsto> 
    ((set_pred merge i), UndefVal)" |
*)

  PhiNode: "(n, PhiNode, s) \<mapsto> (s, (s_phi s) n)"


(* Format as inference rules *)
text \<open>@{thm[mode=Rule] (sub, prem 2) eval.induct} {\sc StartNode}\<close>

text \<open>@{thm[mode=Axiom] (sub, prem 3) eval.induct} {\sc ParameterNode}\<close>
text \<open>@{thm[mode=Axiom] (sub, prem 4) eval.induct} {\sc ConstantNode}\<close>

text \<open>@{thm[mode=Rule] (sub, prem 5) eval.induct} {\sc UnaryNode}\<close>
text \<open>@{thm[mode=Rule] (sub, prem 6) eval.induct} {\sc BinaryNode}\<close>

text \<open>@{thm[mode=Rule] (sub, prem 7) eval.induct} {\sc IfNodeTrue}\<close>
text \<open>@{thm[mode=Rule] (sub, prem 8) eval.induct} {\sc IfNodeFalse}\<close>

text \<open>@{thm[mode=Rule] (sub, prem 9) eval.induct} {\sc ReturnNode}\<close>

(* Example graph evaluation *)
fun new_state :: "IRGraph \<Rightarrow> EvalState" where
  "new_state graph = (EvalState graph (\<lambda> x. UndefVal) [] (\<lambda> x. UndefVal) Map.empty (\<lambda> x. 0))"

definition ex_graph :: IRGraph where
  "ex_graph =
    (add_node 3 ReturnNode [2] []
    (add_node 2 AddNode [1, 1] []
    (add_node 1 (ParameterNode 5) [] []
    (add_node 0 StartNode [] [2]
    empty_graph))))"
lemma "wff_graph ex_graph"
  unfolding ex_graph_def by simp

definition ex_graph2 :: IRGraph where
  "ex_graph2 =
    (add_node 5 ReturnNode [1] []
    (add_node 4 ReturnNode [2] []
    (add_node 3 IfNode [1] [4, 5]
    (add_node 2 (ConstantNode 30) [] []
    (add_node 1 (ConstantNode 1) [] []
    (add_node 0 StartNode [] [3]
    empty_graph))))))"
lemma "wff_graph ex_graph2"
  unfolding ex_graph2_def by simp

datatype GraphBuilder = 
  GraphBuilder |
  AddNode (gb_node_id: "nat") (gb_graph: "IRGraph")

fun build :: "GraphBuilder \<Rightarrow> IRNode \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> GraphBuilder" ("_ _ _ _;")
  where
  "build GraphBuilder n i s = AddNode 0 (add_node 0 n i s empty_graph)" |
  "build (AddNode nid graph) n i s = (AddNode (nid + 1) (add_node (nid + 1) n i s graph))"

fun unpack :: "GraphBuilder \<Rightarrow> IRGraph" where
  "unpack GraphBuilder = empty_graph" |
  "unpack (AddNode nid graph) = graph"

definition ex_graph3 :: IRGraph where
  "ex_graph3 =            
  unpack
  (GraphBuilder
    StartNode [] [3];
    (ConstantNode 1) [] [];
    (ConstantNode 30) [] [];
    IfNode [1] [4, 5];
    ReturnNode [2] [];
    ReturnNode [1] [];)
  "

code_pred eval .

(* Currently causes a wellsortedness error which is resolved by removing
 * all IRNode constructors which have parameters e.g (ParameterNode i)
 * Specifically it is unhappy as nat \<Rightarrow> IRNode is not a sort equal
 * cause nat is not of sort enum
 * 
 * export_code eval in Scala module_name Compiler
 *
 * Code generated when removing the offending IRNode constructors is
 * available in the code_gen folder.
 * 
 * Note: "code_pred eval ." is required to generate code equations from
 * inductive rules
 *)


values "{(s, v). (0, StartNode, (new_state ex_graph)) \<mapsto> (s, v)}"

values "{(s, v). (0, StartNode, (new_state ex_graph2)) \<mapsto> (s, v)}"

values "{(s, v). (0, StartNode, (new_state ex_graph3)) \<mapsto> (s, v)}"

end