theory SemanticsSnippets
  imports
    Semantics.IRStepObj Semantics.Form Proofs.Stuttering Snippets.Snipping
begin

declare [[show_types=false]]

(*notation (latex)
  NoNode ("\<epsilon>")
*)
notation (latex)
  kind ("_\<llangle>_\<rrangle>")

notation (latex)
  stamp_expr ("\<^latex>\<open>\\pitchfork\<close> _")

notation (latex)
  val_to_bool ("_\<^latex>\<open>\\ensuremath{_{\\mathit{\<close>bool\<^latex>\<open>}}}\<close>")


syntax (spaced_type_def output)
  "_constrain" :: "logic => type => logic" ("_ :: _" [4, 0] 3)

snipbegin \<open>isbinary\<close>
text \<open>\begin{center}
@{term_type[mode=spaced_type_def] is_BinaryArithmeticNode}
\end{center}\<close>
snipend -

(* figure out how to export a subset of IRNode!!! *)

snipbegin \<open>inputsof\<close>
text_raw \<open>
@{term_type[mode=spaced_type_def] inputs_of}

@{thm inputs_of_ConstantNode}

@{thm inputs_of_ParameterNode}

@{thm inputs_of_ValuePhiNode}

@{thm inputs_of_AddNode}

@{thm inputs_of_IfNode}\<close>
snipend -

snipbegin \<open>graphdefnostamp\<close>
text_raw \<open>
@{bold \<open>typedef\<close>} @{term[source] \<open>IRGraph = {g :: ID \<rightharpoonup> IRNode . finite (dom g)}\<close>}
\<close>
snipend -

fun ids_fake :: "(ID \<rightharpoonup> IRNode) \<Rightarrow> ID set" where
  "ids_fake g = {nid \<in> dom g . g nid \<noteq> (Some NoNode)}"

fun kind_fake :: "(ID \<rightharpoonup> IRNode) \<Rightarrow> (ID \<Rightarrow> IRNode)" where
  "kind_fake g = (\<lambda>nid. (case g nid of None \<Rightarrow> NoNode | Some v \<Rightarrow> v))"

snipbegin \<open>helpersdisplay\<close>
text_raw \<open>
@{term_type[mode=spaced_type_def] ids_fake}

@{thm ids_fake.simps}\\[0.75em]

@{term_type[mode=spaced_type_def] kind_fake}

@{thm kind_fake.simps}\\[0.75em]

@{term_type[mode=spaced_type_def] inputs}

@{thm inputs.simps}\\[0.75em]

@{term_type[mode=spaced_type_def] succ}

@{thm succ.simps}\\[0.75em]

@{term_type[mode=spaced_type_def] input_edges}

@{thm input_edges.simps}\\[0.75em]

@{term_type[mode=spaced_type_def] usages}

@{thm usages.simps}\\[0.75em]

@{term_type[mode=spaced_type_def] successor_edges}

@{thm successor_edges.simps}\\[0.75em]

@{term_type[mode=spaced_type_def] predecessors}

@{thm predecessors.simps}\\[0.75em]
\<close>
snipend -

snipbegin \<open>wf_start_def\<close>
text_raw \<open>
@{thm[display,margin=40] wf_start_def}
\<close>
snipend -
snipbegin \<open>wf_closed_def\<close>
text_raw \<open>
@{thm[display,margin=40] wf_closed_def}
\<close> 
snipend -
snipbegin \<open>wf_phis_def\<close>
text_raw \<open>
@{thm[display,margin=40] wf_phis_def}
\<close>
snipend -
snipbegin \<open>wf_ends_def\<close>
text_raw \<open>
@{thm[display,margin=40] wf_ends_def}
\<close>
snipend -

snipbegin \<open>wf_graph_def\<close>
text_raw \<open>
@{term_type[mode=spaced_type_def] wf_graph}

@{thm wf_graph.simps}
\<close>
snipend -

text_raw \<open>@{bold \<open>type-synonym\<close>} Signature = @{typ string}\<close>

snipbegin \<open>programdef\<close>
text_raw \<open>
@{bold \<open>type-synonym\<close>} Program = @{typ "Signature \<rightharpoonup> IRGraph"}
\<close>
snipend -

print_antiquotations

(*
type_synonym ('a, 'b) Heap = "'a \<Rightarrow> 'b \<Rightarrow> Value"
type_synonym Free = "nat"
type_synonym ('a, 'b) DynamicHeap = "('a, 'b) Heap \<times> Free"

fun h_load_field :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) DynamicHeap \<Rightarrow> Value" where
  "h_load_field f r (h, n) = h f r"

fun h_store_field :: "'a \<Rightarrow> 'b \<Rightarrow> Value \<Rightarrow> ('a, 'b) DynamicHeap \<Rightarrow> ('a, 'b) DynamicHeap" where
  "h_store_field f r v (h, n) = (h(f := ((h f)(r := v))), n)"

fun h_new_inst :: "('a, 'b) DynamicHeap \<Rightarrow> ('a, 'b) DynamicHeap \<times> Value" where
  "h_new_inst (h, n) = ((h,n+1), (ObjRef (Some n)))"

type_synonym FieldRefHeap = "(string, objref) DynamicHeap"
*)

(* TODO: add heap here *)
snipbegin \<open>heapdef\<close>
type_synonym Heap = "string \<Rightarrow> objref \<Rightarrow> Value"
type_synonym Free = "nat"
type_synonym DynamicHeap = "Heap \<times> Free"

text_raw \<open>
\\[0.75em]

@{text \<open>h_load_field :: \<close>} @{typ[source] "string \<Rightarrow> objref \<Rightarrow> DynamicHeap \<Rightarrow> Value"}

@{thm h_load_field.simps}\\[0.75em]

@{text \<open>h_store_field :: \<close>} @{typ[source] "string \<Rightarrow> objref \<Rightarrow> Value \<Rightarrow> DynamicHeap \<Rightarrow> DynamicHeap"}

@{thm h_store_field.simps}\\[0.75em]

@{text \<open>h_new_inst :: \<close>} @{typ[source] "DynamicHeap \<Rightarrow> (DynamicHeap \<times> Value)"}

@{thm h_new_inst.simps}
\<close>
snipend -

(* Deprecated expression semantics *)
(*
text_raw \<open>\Snip{ExpressionSemantics}%\<close>
text \<open>
\begin{center}
\induct{@{thm[mode=Rule] eval.ConstantNode [no_vars]}}{eval:const}
\induct{@{thm[mode=Rule] eval.AddNode [no_vars]}}{eval:add}
\induct{@{thm[mode=Rule] eval.ParameterNode [no_vars]}}{eval:param}
\induct{@{thm[mode=Rule] eval.ValuePhiNode [no_vars]}}{eval:phi}
\induct{@{thm[mode=Rule] eval.InvokeNodeEval [no_vars]}}{eval:invoke}
\induct{@{thm[mode=Rule] eval.NewInstanceNode [no_vars]}}{eval:invoke}
\induct{@{thm[mode=Rule] eval.LoadFieldNode [no_vars]}}{eval:load}
\end{center}
\<close>
text_raw \<open>\EndSnip\<close>

text_raw \<open>\Snip{EvalAll}%\<close>
text \<open>
\begin{center}
@{thm[mode=Rule] eval_all.Base [no_vars]}\\[8px]
@{thm[mode=Rule] eval_all.Transitive [no_vars]}
\end{center}
\<close>
text_raw \<open>\EndSnip\<close>
*)


snipbegin \<open>StepSemantics\<close>
text \<open>
\begin{center}
\induct{@{thm[mode=Rule] step.SequentialNode [no_vars]}}{step:seq}
\induct{@{thm[mode=Rule] step.IfNode [no_vars]}}{step:if}
\induct{@{thm[mode=Rule] step.EndNodes [no_vars]}}{step:end}
\induct{@{thm[mode=Rule] step.NewInstanceNode [no_vars]}}{step:newinst}
\induct{@{thm[mode=Rule] step.LoadFieldNode [no_vars]}}{step:load}
\induct{@{thm[mode=Rule] step.StoreFieldNode [no_vars]}}{step:store}
\induct{@{thm[mode=Rule] step.StaticLoadFieldNode [no_vars]}}{step:load-static}
\induct{@{thm[mode=Rule] step.StaticStoreFieldNode [no_vars]}}{step:store-static}
\end{center}
\<close>
snipend -

snipbegin \<open>TopStepSemantics\<close>
text \<open>
\begin{center}
\induct{@{thm[mode=Rule] step_top.Lift [no_vars]}}{top:lift}
\induct{@{thm[mode=Rule] step_top.InvokeNodeStep [no_vars]}}{top:invoke}
\induct{@{thm[mode=Rule] step_top.ReturnNode [no_vars]}}{top:return}
\induct{@{thm[mode=Rule] step_top.ReturnNodeVoid [no_vars]}}{top:return-void}
\induct{@{thm[mode=Rule] step_top.UnwindNode [no_vars]}}{top:unwind}
\end{center}
\<close>
snipend -

(* Deprecated canonicalization rules *)
(*
text_raw \<open>\Snip{AddNodeRules}%
\begin{center}
@{thm[mode=Rule] CanonicalizeAdd.add_both_const [no_vars]}\\[8px]
@{thm[mode=Rule] CanonicalizeAdd.add_xzero [no_vars]}\\[8px]
@{thm[mode=Rule] CanonicalizeAdd.add_yzero [no_vars]}
\end{center}
\EndSnip\<close>

text_raw \<open>\Snip{AddNodeProof}%
@{thm CanonicalizeAddProof}
\EndSnip\<close>
*)

snipbegin \<open>Stutter\<close>
text \<open>
\begin{center}
@{thm[mode=Rule] stutter.StutterStep [no_vars]}\\[8px]
@{thm[mode=Rule] stutter.Transitive [no_vars]}
\end{center}
\<close>
snipend -

(*
text_raw \<open>\Snip{CanonicalizeIfNodeRules}%
\begin{center}
@{thm[mode=Rule] CanonicalizeIf.trueConst}\\[8px]
@{thm[mode=Rule] CanonicalizeIf.falseConst}\\[8px]
@{thm[mode=Rule] CanonicalizeIf.eqBranch}
\end{center}
\EndSnip\<close>
definition replace_node_fake :: "ID \<Rightarrow> IRNode \<Rightarrow> IRGraph \<Rightarrow> IRGraph" where
  "replace_node_fake nid node g = replace_node nid (node,default_stamp) g"
lemma CanonicalizeIfProof_fake:
  fixes m::MapState and h::FieldRefHeap
  assumes "kind g nid = before"
  assumes "CanonicalizeIf g before after"
  assumes "g' = replace_node_fake nid after g"
  assumes "g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h)"
  shows "nid | g \<sim> g'"
  by (metis CanonicalizeIfProof assms(1) assms(2) assms(3) assms(4) replace_node_fake_def)

text_raw \<open>\Snip{CanonicalizeIfNodeProof}%
\begin{center}
@{thm[display] CanonicalizeIfProof_fake}
\end{center}
\EndSnip\<close>
*)

(* EXPERIMENTAL *)
notation (latex output)
  filtered_inputs ("inputs\<^latex>\<open>\\ensuremath{^{\\mathit{\<close>_\<llangle>_\<rrangle>\<^latex>\<open>}}}\<close>\<^latex>\<open>\\ensuremath{_{\\mathit{\<close>_\<^latex>\<open>}}}\<close>")
notation (latex output)
  filtered_successors ("succ\<^latex>\<open>\\ensuremath{^{\\mathit{\<close>_\<llangle>_\<rrangle>\<^latex>\<open>}}}\<close>\<^latex>\<open>\\ensuremath{_{\\mathit{\<close>_\<^latex>\<open>}}}\<close>")
notation (latex output)
  filtered_usages ("usages\<^latex>\<open>\\ensuremath{^{\\mathit{\<close>_\<llangle>_\<rrangle>\<^latex>\<open>}}}\<close>\<^latex>\<open>\\ensuremath{_{\\mathit{\<close>_\<^latex>\<open>}}}\<close>")

snipbegin \<open>example2\<close>
text_raw \<open>
@{term[display] \<open>filtered_inputs g nid f\<close>}
\<close>
snipend -

notation (latex output)
  Pure.dummy_pattern ("-")

(* take out bits from intvals - changes if we change to deal with bits *)
notation (latex output)
  IntVal ("IntVal (2 _)")

end
