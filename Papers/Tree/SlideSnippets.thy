theory SlideSnippets
  imports
    Semantics.TreeToGraphThms
    Snippets.Snipping
begin

notation (latex)
  kind ("_\<llangle>_\<rrangle>")

notation (latex)
  IRTreeEval.ord_IRExpr_inst.less_eq_IRExpr ("_ \<longmapsto> _")

snipbegin \<open>abstract-syntax-tree\<close>
text \<open>@{datatype[display,margin=40] IRExpr}\<close>
snipend -

snipbegin \<open>tree-semantics\<close>
text \<open>
\induct{@{thm[mode=Rule] evaltree.ConstantExpr [no_vars]}}{semantics:constant}
\induct{@{thm[mode=Rule] evaltree.ParameterExpr [no_vars]}}{semantics:parameter}
\induct{@{thm[mode=Rule] evaltree.UnaryExpr [no_vars]}}{semantics:unary}
\induct{@{thm[mode=Rule] evaltree.BinaryExpr [no_vars]}}{semantics:binary}
\induct{@{thm[mode=Rule] evaltree.LeafExpr [no_vars]}}{semantics:leaf}
\<close>
snipend -

snipbegin \<open>expression-refinement\<close>
text \<open>
\begin{center}
@{thm le_expr_def [no_vars]} 
\end{center}
\<close>
snipend -

snipbegin \<open>graph2tree\<close>
text \<open>
\induct{@{thm[mode=Rule] rep.ConstantNode [no_vars]}}{semantics:constant}
\induct{@{thm[mode=Rule] rep.AbsNode [no_vars]}}{semantics:unary}
\induct{@{thm[mode=Rule] rep.AddNode [no_vars]}}{semantics:binary}
\<close>
snipend -

snipbegin \<open>graph-semantics\<close>
text \<open>
\begin{center}
@{thm encodeeval.intros}
\end{center}
\<close>
snipend -

snipbegin \<open>graph-refinement\<close>
text \<open>
\begin{center}
@{thm[display, margin=60] graph_refinement_def [no_vars]}
\end{center}
\<close>
snipend -

(* hide as_set, should treat IRGraph as a set of pairs in paper *)
translations
  "n" <= "CONST as_set n"

snipbegin \<open>graph-semantics-preservation\<close>
text \<open>
\begin{center}
@{thm[display, margin=30] graph_semantics_preservation [no_vars]}
\end{center}
\<close>
snipend -

snipbegin \<open>maximal-sharing\<close>
text \<open>@{thm[display, margin=50] maximal_sharing [no_vars]}\<close>
snipend -

snipbegin \<open>tree-to-graph-rewriting\<close>
text \<open>
\begin{center}
@{thm[display, margin=40] tree_to_graph_rewriting [no_vars]}
\end{center}
\<close>
snipend -

snipbegin \<open>graph-represents-expression\<close>
text \<open>
\begin{center}
@{thm[display] graph_represents_expression_def [no_vars]}
\end{center}
\<close>
snipend -

snipbegin \<open>graph-construction\<close>
text \<open>
\begin{center}
@{thm[display, margin=40] graph_construction [no_vars]}
\end{center}
\<close>
snipend -

end