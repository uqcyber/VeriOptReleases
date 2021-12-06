theory TreeSnippets
  imports 
    Semantics.TreeToGraphThms
    Veriopt.Snipping
begin

notation (latex)
  kind ("_\<llangle>_\<rrangle>")

notation (latex)
  IRTreeEval.ord_IRExpr_inst.less_eq_IRExpr ("_ \<longmapsto> _")

snipbegin \<open>abstract-syntax-tree\<close>
text \<open>@{datatype[display,margin=45] IRExpr}\<close>
snipend -

snipbegin \<open>tree-semantics\<close>
text \<open>
\induct{@{thm[mode=Rule] evaltree.ConstantExpr [no_vars]}}{semantics:constant}
\induct{@{thm[mode=Rule] evaltree.ParameterExpr [no_vars]}}{semantics:parameter}
\induct{@{thm[mode=Rule] evaltree.ConditionalExpr [no_vars]}}{semantics:conditional}
\induct{@{thm[mode=Rule] evaltree.UnaryExpr [no_vars]}}{semantics:unary}
\induct{@{thm[mode=Rule] evaltree.BinaryExpr [no_vars]}}{semantics:binary}
\induct{@{thm[mode=Rule] evaltree.LeafExpr [no_vars]}}{semantics:leaf}
\<close>
snipend -
(*\induct{@{thm[mode=Rule] evaltree.ConvertExpr [no_vars]}}{semantics:convert}*)

snipbegin \<open>tree-evaluation-deterministic\<close>
text \<open>@{thm[display] evalDet [no_vars]}\<close>
snipend -

snipbegin \<open>expression-refinement\<close>
text \<open>
\begin{center}
@{thm le_expr_def [no_vars]} 
\end{center}
\<close>
snipend -

snipbegin \<open>expression-refinement-monotone\<close>
text \<open>
\begin{center}
@{thm mono_unary [no_vars]} \\
@{thm mono_binary [no_vars]} \\
@{thm mono_conditional [no_vars]}
\end{center}
\<close>
snipend -

(* skipping add node optimisations as they are currently very ugly *)

(* definition 5 (semantics-preserving) is there a distinction in Isabelle? *)

snipbegin \<open>graph-representation\<close>
text \<open>@{bold \<open>typedef\<close>} @{term[source] \<open>IRGraph = {g :: ID \<rightharpoonup> IRNode . finite (dom g)}\<close>}\<close>
snipend -

snipbegin \<open>graph2tree\<close>
text \<open>
\induct{@{thm[mode=Rule] rep.ConstantNode [no_vars]}}{semantics:constant}
\induct{@{thm[mode=Rule] rep.ParameterNode [no_vars]}}{semantics:parameter}
\induct{@{thm[mode=Rule] rep.ConditionalNode [no_vars]}}{semantics:conditional}
\induct{@{thm[mode=Rule] rep.AbsNode [no_vars]}}{semantics:unary}
\induct{@{thm[mode=Rule] rep.SignExtendNode [no_vars]}}{semantics:convert}
\induct{@{thm[mode=Rule] rep.AddNode [no_vars]}}{semantics:binary}
\induct{@{thm[mode=Rule] rep.LeafNode [no_vars]}}{semantics:leaf}
\<close>
snipend -

snipbegin \<open>preeval\<close>
text \<open>@{thm is_preevaluated.simps}\<close>
snipend -

snipbegin \<open>deterministic-representation\<close>
text \<open>
\begin{center}
@{thm repDet [no_vars]}
\end{center}
\<close>
snipend -

(* definition 9 (well-formed graph) no? *)

snipbegin \<open>graph-semantics\<close>
text \<open>
\begin{center}
@{thm encodeeval_def}
\end{center}
\<close>
snipend -

snipbegin \<open>graph-semantics-deterministic\<close>
text \<open>
\begin{center}
@{thm graphDet [no_vars]}
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



experiment begin
text \<open>Experimental embedding into a simplier but usable form for expression nodes in a graph\<close>

datatype ExprIRNode =
  ExprUnaryNode IRUnaryOp ID |
  ExprBinaryNode IRBinaryOp ID ID |
  ExprConditionalNode ID ID ID |
  ExprConstantNode Value |
  ExprParameterNode nat |
  ExprLeafNode ID |
  NotExpr

fun embed_expr :: "IRNode \<Rightarrow> ExprIRNode" where
  "embed_expr (ConstantNode v) = ExprConstantNode v" |
  "embed_expr (ParameterNode i) = ExprParameterNode i" |
  "embed_expr (ConditionalNode c t f) = ExprConditionalNode c t f" |
  "embed_expr (AbsNode x) = ExprUnaryNode UnaryAbs x" |
  "embed_expr (NotNode x) = ExprUnaryNode UnaryNot x" |
  "embed_expr (NegateNode x) = ExprUnaryNode UnaryNeg x" |
  "embed_expr (LogicNegationNode x) = ExprUnaryNode UnaryLogicNegation x" |
  "embed_expr (AddNode x y) = ExprBinaryNode BinAdd x y" |
  "embed_expr (MulNode x y) = ExprBinaryNode BinMul x y" |
  "embed_expr (SubNode x y) = ExprBinaryNode BinSub x y" |
  "embed_expr (AndNode x y) = ExprBinaryNode BinAnd x y" |
  "embed_expr (OrNode x y) = ExprBinaryNode BinOr x y" |
  "embed_expr (XorNode x y) = ExprBinaryNode BinXor x y" |
  "embed_expr (IntegerBelowNode x y) = ExprBinaryNode BinIntegerBelow x y" |
  "embed_expr (IntegerEqualsNode x y) = ExprBinaryNode BinIntegerEquals x y" |
  "embed_expr (IntegerLessThanNode x y) = ExprBinaryNode BinIntegerLessThan x y" |
  "embed_expr (NarrowNode ib rb x) = ExprUnaryNode (UnaryNarrow ib rb) x" |
  "embed_expr (SignExtendNode ib rb x) = ExprUnaryNode (UnarySignExtend ib rb) x" |
  "embed_expr (ZeroExtendNode ib rb x) = ExprUnaryNode (UnaryZeroExtend ib rb) x" |
  "embed_expr _ = NotExpr"

lemma unary_embed:
  assumes "g \<turnstile> n \<simeq> UnaryExpr op x"
  shows "\<exists> x' . embed_expr (kind g n) = ExprUnaryNode op x'"
  using assms by (induction "UnaryExpr op x" rule: rep.induct; simp)

lemma equal_embedded_x:
  assumes "g \<turnstile> n \<simeq> UnaryExpr op xe"
  assumes "embed_expr (kind g n) = ExprUnaryNode op' x"
  shows "g \<turnstile> x \<simeq> xe"
  using assms by (induction "UnaryExpr op xe" rule: rep.induct; simp)

lemma blah:
  assumes "embed_expr (kind g n) = ExprUnaryNode op n'"
  assumes "g \<turnstile> n' \<simeq> e"
  shows "(g \<turnstile> n \<simeq> UnaryExpr op e)"
  using assms(2,1) apply (cases "kind g n"; auto)
  using rep.AbsNode apply blast
  using rep.LogicNegationNode apply blast
  using NarrowNode apply presburger
  using rep.NegateNode apply blast
  using rep.NotNode apply blast
  using rep.SignExtendNode apply blast
  using rep.ZeroExtendNode by blast
end

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
