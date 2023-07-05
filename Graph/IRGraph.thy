subsection \<open>IR Graph Type\<close>

theory IRGraph
  imports 
    IRNodeHierarchy
    Stamp
    "HOL-Library.FSet"
    "HOL.Relation"
begin

text \<open>This theory defines the main Graal data structure - an entire IR Graph.\<close>

text \<open>
IRGraph is defined as a partial map with a finite domain.
The finite domain is required to be able to generate code and produce an interpreter.
\<close>
typedef IRGraph = "{g :: ID \<rightharpoonup> (IRNode \<times> Stamp) . finite (dom g)}"
proof -
  have "finite(dom(Map.empty)) \<and> ran Map.empty = {}" by auto
  then show ?thesis
    by fastforce
qed

setup_lifting type_definition_IRGraph

lift_definition ids :: "IRGraph \<Rightarrow> ID set"
  is "\<lambda>g. {nid \<in> dom g . \<nexists>s. g nid = (Some (NoNode, s))}" .

fun with_default :: "'c \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> (('a \<rightharpoonup> 'b) \<Rightarrow> 'a \<Rightarrow> 'c)" where
  "with_default def conv = (\<lambda>m k.
    (case m k of None \<Rightarrow> def | Some v \<Rightarrow> conv v))"

lift_definition kind :: "IRGraph \<Rightarrow> (ID \<Rightarrow> IRNode)"
  is "with_default NoNode fst" .

lift_definition stamp :: "IRGraph \<Rightarrow> ID \<Rightarrow> Stamp"
  is "with_default IllegalStamp snd" .

lift_definition add_node :: "ID \<Rightarrow> (IRNode \<times> Stamp) \<Rightarrow> IRGraph \<Rightarrow> IRGraph"
  is "\<lambda>nid k g. if fst k = NoNode then g else g(nid \<mapsto> k)" by simp

lift_definition remove_node :: "ID \<Rightarrow> IRGraph \<Rightarrow> IRGraph"
  is "\<lambda>nid g. g(nid := None)" by simp

lift_definition replace_node :: "ID \<Rightarrow> (IRNode \<times> Stamp) \<Rightarrow> IRGraph \<Rightarrow> IRGraph"
  is "\<lambda>nid k g. if fst k = NoNode then g else g(nid \<mapsto> k)" by simp

lift_definition as_list :: "IRGraph \<Rightarrow> (ID \<times> IRNode \<times> Stamp) list"
  is "\<lambda>g. map (\<lambda>k. (k, the (g k))) (sorted_list_of_set (dom g))" .

fun no_node :: "(ID \<times> (IRNode \<times> Stamp)) list \<Rightarrow> (ID \<times> (IRNode \<times> Stamp)) list" where
  "no_node g = filter (\<lambda>n. fst (snd n) \<noteq> NoNode) g"

lift_definition irgraph :: "(ID \<times> (IRNode \<times> Stamp)) list \<Rightarrow> IRGraph"
  is "map_of \<circ> no_node"
  by (simp add: finite_dom_map_of)

definition as_set :: "IRGraph \<Rightarrow> (ID \<times> (IRNode \<times> Stamp)) set" where
  "as_set g = {(n, kind g n, stamp g n) | n . n \<in> ids g}"

definition true_ids :: "IRGraph \<Rightarrow> ID set" where
  "true_ids g = ids g - {n \<in> ids g. \<exists>n' . kind g n = RefNode n'}"

definition domain_subtraction :: "'a set \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> ('a \<times> 'b) set"
  (infix "\<unlhd>" 30) where
  "domain_subtraction s r = {(x, y) . (x, y) \<in> r \<and> x \<notin> s}"

notation (latex)
  domain_subtraction ("_ \<^latex>\<open>$\\ndres$\<close> _")

(* Theories are required for code generation to work *)
code_datatype irgraph

fun filter_none where
  "filter_none g = {nid \<in> dom g . \<nexists>s. g nid = (Some (NoNode, s))}"

lemma no_node_clears:
  "res = no_node xs \<longrightarrow> (\<forall>x \<in> set res. fst (snd x) \<noteq> NoNode)"
  by simp

lemma dom_eq:
  assumes "\<forall>x \<in> set xs. fst (snd x) \<noteq> NoNode"
  shows "filter_none (map_of xs) = dom (map_of xs)"
  using assms map_of_SomeD by fastforce

lemma fil_eq:
  "filter_none (map_of (no_node xs)) = set (map fst (no_node xs))"
  by (metis no_node_clears dom_eq dom_map_of_conv_image_fst list.set_map)

lemma irgraph[code]: "ids (irgraph m) = set (map fst (no_node m))"
  by (metis fil_eq Rep_IRGraph eq_onp_same_args filter_none.simps ids.abs_eq irgraph.abs_eq
      irgraph.rep_eq mem_Collect_eq)

lemma [code]: "Rep_IRGraph (irgraph m) = map_of (no_node m)"
  by (simp add: irgraph.rep_eq)

\<comment> \<open>Get the inputs set of a given node ID\<close>
fun inputs :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID set" where
  "inputs g nid = set (inputs_of (kind g nid))"
\<comment> \<open>Get the successor set of a given node ID\<close>
fun succ :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID set" where
  "succ g nid = set (successors_of (kind g nid))"
\<comment> \<open>Gives a relation between node IDs - between a node and its input nodes\<close>
fun input_edges :: "IRGraph \<Rightarrow> ID rel" where
  "input_edges g = (\<Union> i \<in> ids g. {(i,j)|j. j \<in> (inputs g i)})"
\<comment> \<open>Find all the nodes in the graph that have nid as an input - the usages of nid\<close>
fun usages :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID set" where
  "usages g nid = {i. i \<in> ids g \<and> nid \<in> inputs g i}"
fun successor_edges :: "IRGraph \<Rightarrow> ID rel" where
  "successor_edges g = (\<Union> i \<in> ids g. {(i,j)|j . j \<in> (succ  g i)})"
fun predecessors :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID set" where
  "predecessors g nid = {i. i \<in> ids g \<and> nid \<in> succ g i}"
fun nodes_of :: "IRGraph \<Rightarrow> (IRNode \<Rightarrow> bool) \<Rightarrow> ID set" where
  "nodes_of g sel = {nid \<in> ids g . sel (kind g nid)}"
fun edge :: "(IRNode \<Rightarrow> 'a) \<Rightarrow> ID \<Rightarrow> IRGraph \<Rightarrow> 'a" where
  "edge sel nid g = sel (kind g nid)"

fun filtered_inputs :: "IRGraph \<Rightarrow> ID \<Rightarrow> (IRNode \<Rightarrow> bool) \<Rightarrow> ID list" where
  "filtered_inputs g nid f = filter (f \<circ> (kind g)) (inputs_of (kind g nid))"
fun filtered_successors :: "IRGraph \<Rightarrow> ID \<Rightarrow> (IRNode \<Rightarrow> bool) \<Rightarrow> ID list" where
  "filtered_successors g nid f = filter (f \<circ> (kind g)) (successors_of (kind g nid))"
fun filtered_usages :: "IRGraph \<Rightarrow> ID \<Rightarrow> (IRNode \<Rightarrow> bool) \<Rightarrow> ID set" where
  "filtered_usages g nid f = {n \<in> (usages g nid). f (kind g n)}"

fun is_empty :: "IRGraph \<Rightarrow> bool" where
  "is_empty g = (ids g = {})"

fun any_usage :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID" where
  "any_usage g nid = hd (sorted_list_of_set (usages g nid))"

lemma ids_some[simp]: "x \<in> ids g \<longleftrightarrow> kind g x \<noteq> NoNode" 
proof -
  have that: "x \<in> ids g \<longrightarrow> kind g x \<noteq> NoNode"
    by (auto simp add: kind.rep_eq ids.rep_eq)
  have "kind g x \<noteq> NoNode \<longrightarrow> x \<in> ids g"
    by (cases "Rep_IRGraph g x = None"; auto simp add: ids_def kind_def)
  from this that show ?thesis 
    by auto
qed

lemma not_in_g: 
  assumes "nid \<notin> ids g"
  shows "kind g nid = NoNode"
  using assms by simp

lemma valid_creation[simp]:
  "finite (dom g) \<longleftrightarrow> Rep_IRGraph (Abs_IRGraph g) = g"
  by (metis Abs_IRGraph_inverse Rep_IRGraph mem_Collect_eq)

lemma [simp]: "finite (ids g)" 
  using Rep_IRGraph by (simp add: ids.rep_eq)

lemma [simp]: "finite (ids (irgraph g))" 
  by (simp add: finite_dom_map_of)

lemma [simp]: "finite (dom g) \<longrightarrow> ids (Abs_IRGraph g) = {nid \<in> dom g . \<nexists>s. g nid = Some (NoNode, s)}"
  by (simp add: ids.rep_eq)

lemma [simp]: "finite (dom g) \<longrightarrow> kind (Abs_IRGraph g) = (\<lambda>x . (case g x of None \<Rightarrow> NoNode | Some n \<Rightarrow> fst n))"
  by (simp add: kind.rep_eq)

lemma [simp]: "finite (dom g) \<longrightarrow> stamp (Abs_IRGraph g) = (\<lambda>x . (case g x of None \<Rightarrow> IllegalStamp | Some n \<Rightarrow> snd n))"
  by (simp add: stamp.rep_eq)

lemma [simp]: "ids (irgraph g) = set (map fst (no_node g))" 
  by (simp add: irgraph)

lemma [simp]: "kind (irgraph g) = (\<lambda>nid. (case (map_of (no_node g)) nid of None \<Rightarrow> NoNode | Some n \<Rightarrow> fst n))" 
  by (simp add: kind.rep_eq irgraph.rep_eq)

lemma [simp]: "stamp (irgraph g) = (\<lambda>nid. (case (map_of (no_node g)) nid of None \<Rightarrow> IllegalStamp | Some n \<Rightarrow> snd n))" 
  by (simp add: stamp.rep_eq irgraph.rep_eq)

lemma map_of_upd: "(map_of g)(k \<mapsto> v) = (map_of ((k, v) # g))"
  by simp

(* this proof should be simplier *)
lemma [code]: "replace_node nid k (irgraph g) = (irgraph ( ((nid, k) # g)))"
proof (cases "fst k = NoNode")
  case True
  then show ?thesis
    by (metis (mono_tags, lifting) Rep_IRGraph_inject filter.simps(2) irgraph.abs_eq no_node.simps 
        replace_node.rep_eq snd_conv)
next
  case False
  then show ?thesis
    by (smt (verit, ccfv_SIG) irgraph_def Rep_IRGraph comp_apply eq_onp_same_args filter.simps(2)
        id_def irgraph.rep_eq map_fun_apply map_of_upd mem_Collect_eq no_node.elims replace_node_def
        replace_node.abs_eq snd_eqD)
qed

lemma [code]: "add_node nid k (irgraph g) = (irgraph (((nid, k) # g)))"
  by (smt (verit) Rep_IRGraph_inject add_node.rep_eq filter.simps(2) irgraph.rep_eq map_of_upd
      snd_conv no_node.simps)

lemma add_node_lookup:
  "gup = add_node nid (k, s) g \<longrightarrow> 
    (if k \<noteq> NoNode then kind gup nid = k \<and> stamp gup nid = s else kind gup nid = kind g nid)"
proof (cases "k = NoNode")
  case True
  then show ?thesis
    by (simp add: add_node.rep_eq kind.rep_eq)
next
  case False
  then show ?thesis
    by (simp add: kind.rep_eq add_node.rep_eq stamp.rep_eq)
qed

lemma remove_node_lookup:
  "gup = remove_node nid g \<longrightarrow> kind gup nid = NoNode \<and> stamp gup nid = IllegalStamp"
  by (simp add: kind.rep_eq remove_node.rep_eq stamp.rep_eq)

lemma replace_node_lookup[simp]:
  "gup = replace_node nid (k, s) g \<and> k \<noteq> NoNode \<longrightarrow> kind gup nid = k \<and> stamp gup nid = s"
  by (simp add: replace_node.rep_eq kind.rep_eq stamp.rep_eq)

lemma replace_node_unchanged:
  "gup = replace_node nid (k, s) g \<longrightarrow> (\<forall> n \<in> (ids g - {nid}) . n \<in> ids g \<and> n \<in> ids gup \<and> kind g n = kind gup n)" 
  by (simp add: kind.rep_eq replace_node.rep_eq)

subsubsection "Example Graphs"
text "Example 1: empty graph (just a start and end node)"
definition start_end_graph:: IRGraph where
  "start_end_graph = irgraph [(0, StartNode None 1, VoidStamp), (1, ReturnNode None None, VoidStamp)]"

text \<open>Example 2:
  public static int sq(int x) { return x * x; }

             [1 P(0)]
               \ /
  [0 Start]   [4 *]
       |      /
       V     /
      [5 Return]
\<close>
definition eg2_sq :: "IRGraph" where
  "eg2_sq = irgraph [
    (0, StartNode None 5, VoidStamp),
    (1, ParameterNode 0, default_stamp),
    (4, MulNode 1 1, default_stamp),
    (5, ReturnNode (Some 4) None, default_stamp)
   ]"

(* TODO: to include the float type (used by stamps) we need
         a code equation for float_of but it is not clear how
         to implement this correctly
lemma[code]: "float_of n = 0"
*)

(* Test the code generation. *)
value "input_edges eg2_sq"
value "usages eg2_sq 1"

end

