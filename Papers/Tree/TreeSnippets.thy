section \<open>Verifying term graph optimizations using Isabelle/HOL\<close>

theory TreeSnippets
  imports
    Canonicalizations.BinaryNode
    Canonicalizations.ConditionalPhase
    Canonicalizations.AddPhase
    Semantics.TreeToGraphThms
    Snippets.Snipping
    "HOL-Library.OptionalSugar"
begin

\<comment> \<open>First, we disable undesirable markup.\<close>
declare [[show_types=false,show_sorts=false]]
no_notation ConditionalExpr ("_ ? _ : _")

\<comment> \<open>We want to disable and reduce how aggressive automated tactics are as obligations are generated in the paper\<close>
method unfold_size = -
method unfold_optimization = 
  (unfold rewrite_preservation.simps, unfold rewrite_termination.simps,
    rule conjE, simp, simp del: le_expr_def)

subsection \<open>Markup syntax for common operations\<close>

notation (latex)
  kind ("_\<llangle>_\<rrangle>")

notation (latex)
  valid_value ("_ \<in> _")

notation (latex)
  val_to_bool ("\<^latex>\<open>bool-of\<close> _")

notation (latex)
  constantAsStamp ("\<^latex>\<open>stamp-from-value\<close> _")

notation (latex)
  find_node_and_stamp ("\<^latex>\<open>find-matching\<close> _")

notation (latex)
  add_node ("\<^latex>\<open>insert\<close> _")

notation (latex)
  get_fresh_id ("\<^latex>\<open>fresh-id\<close> _")



notation (latex)
  size ("\<^latex>\<open>trm(\<close>_\<^latex>\<open>)\<close>")


subsection \<open>Representing canonicalization optimizations\<close>

text \<open>
We wish to provide an example of the semantics layers 
at which optimizations can be expressed.
\<close>

\<comment> \<open>Algebraic laws\<close>
lemma diff_self:
  fixes x :: int
  shows "x - x = 0"
  by simp
lemma diff_diff_cancel:
  fixes x y :: int
  shows "x - (x - y) = y"
  by simp
thm diff_self
thm diff_diff_cancel
snipbegin \<open>algebraic-laws\<close>
text \<open>\begin{align}
@{thm diff_self[show_types=false]}\\
@{thm diff_diff_cancel[show_types=false]}
\end{align}\<close>
snipend -

\<comment> \<open>Values\<close>
lemma diff_self_value: "\<forall>x::'a::len word. x - x = 0"
  by simp
lemma diff_diff_cancel_value:
  "\<forall> x y::'a::len word . x - (x - y) = y"
  by simp

snipbegin \<open>algebraic-laws-values\<close>
text_raw \<open>\begin{align}
@{thm diff_self_value[show_types]} \label{prop-v-minus-v}\\
@{thm diff_diff_cancel_value[show_types]} \label{prop-redundant-sub}
\end{align}\<close>
snipend -

\<comment> \<open>Expression\<close>
translations
  "n" <= "CONST ConstantExpr (CONST IntVal b n)"
  "x - y" <= "CONST BinaryExpr (CONST BinSub) x y"
notation (ExprRule output)
  Refines ("_ \<longmapsto> _")
lemma diff_self_expr:
  assumes "\<forall>m p v. [m,p] \<turnstile> exp[x - x] \<mapsto> IntVal b v"
  shows "exp[x - x] \<ge> exp[const (IntVal b 0)]"
  using assms apply simp
  by (metis(full_types) evalDet val_to_bool.simps(1) zero_neq_one)

method open_eval = (simp; (rule impI)?; (rule allI)+; rule impI)

lemma diff_diff_cancel_expr:
  shows "exp[x - (x - y)] \<ge> exp[y]"
  apply open_eval
  subgoal premises eval for m p v
  proof -
    obtain vx where vx: "[m, p] \<turnstile> x \<mapsto> vx"
      using eval by blast
    obtain vy where vy: "[m, p] \<turnstile> y \<mapsto> vy"
      using eval by blast
    then have e: "[m, p] \<turnstile> exp[x - (x - y)] \<mapsto> val[vx - (vx - vy)]"
      using vx vy eval
      by (smt (verit, ccfv_SIG) bin_eval.simps(3) evalDet unfold_binary)
    then have notUn: "val[vx - (vx - vy)] \<noteq> UndefVal"
      using evaltree_not_undef by auto
    then have "val[vx - (vx - vy)] = vy"
      apply (cases vx; cases vy; auto simp: notUn)
      using eval_unused_bits_zero vy apply blast
      by (metis(full_types) intval_sub.simps(6))
    then show ?thesis 
      by (metis e eval evalDet vy)
  qed
  done

thm_oracles diff_diff_cancel_expr

snipbegin \<open>algebraic-laws-expressions\<close>
text_raw \<open>\begin{align}
@{thm[mode=ExprRule] (concl) diff_self_expr} \label{prop-MinusSame} \\
@{thm[mode=ExprRule] (concl) diff_diff_cancel_expr}
\end{align}\<close>
snipend -
no_translations
  "n" <= "CONST ConstantExpr (CONST IntVal b n)"
  "x - y" <= "CONST BinaryExpr (CONST BinSub) x y"


definition wf_stamp :: "IRExpr \<Rightarrow> bool" where
  "wf_stamp e = (\<forall>m p v. ([m, p] \<turnstile> e \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr e))"

lemma wf_stamp_eval:
  assumes "wf_stamp e"
  assumes "stamp_expr e = IntegerStamp b lo hi"
  shows "\<forall>m p v. ([m, p] \<turnstile> e \<mapsto> v) \<longrightarrow> (\<exists>vv. v = IntVal b vv)"
  using assms unfolding wf_stamp_def
  using valid_int_same_bits valid_int
  by metis

phase SnipPhase
  terminating size
begin
lemma sub_same_val:
  assumes "val[x - x] = IntVal b v"
  shows "val[x - x] = val[IntVal b 0]"
  using assms by (cases x; auto)

snipbegin \<open>sub-same-32\<close>
optimization SubIdentity:
  "x - x \<longmapsto> ConstantExpr (IntVal b 0)
     when ((stamp_expr exp[x - x] = IntegerStamp b lo hi) \<and> wf_stamp exp[x - x])"
  snipend -
   using IRExpr.disc(42) size.simps(4) size_non_const
   apply simp
  apply (rule impI) apply simp
proof -
  assume assms: "stamp_binary BinSub (stamp_expr x) (stamp_expr x) = IntegerStamp b lo hi \<and> wf_stamp exp[x - x]"
  have "\<forall>m p v . ([m, p] \<turnstile> exp[x - x] \<mapsto> v) \<longrightarrow> (\<exists>vv. v = IntVal b vv)"
    using assms wf_stamp_eval
    by (metis stamp_expr.simps(2))
  then show "\<forall>m p v. ([m,p] \<turnstile> BinaryExpr BinSub x x \<mapsto> v) \<longrightarrow> ([m,p] \<turnstile> ConstantExpr (IntVal b 0) \<mapsto> v)"
    using wf_value_def
    by (smt (verit, best) BinaryExprE TreeSnippets.wf_stamp_def assms bin_eval.simps(3) constantAsStamp.simps(1) evalDet stamp_expr.simps(2) sub_same_val unfold_const valid_stamp.simps(1) valid_value.simps(1))
qed
thm_oracles SubIdentity

snipbegin \<open>RedundantSubtract\<close>
optimization RedundantSubtract:
  "x - (x - y) \<longmapsto> y"
snipend -
  using size_simps apply simp
  using diff_diff_cancel_expr by presburger
end

subsection \<open>Representing terms\<close>

text \<open>
We wish to show a simple example of expressions represented as terms.
\<close>

snipbegin \<open>ast-example\<close>
text "@{value[display,margin=40] \<open>BinaryExpr BinAdd (BinaryExpr BinMul x x) (BinaryExpr BinMul x x)\<close>}"
snipend -

text \<open>
Then we need to show the datatypes that compose the example expression.
\<close>

snipbegin \<open>abstract-syntax-tree\<close>
text \<open>@{datatype[display,margin=40] IRExpr}\<close>
snipend -

snipbegin \<open>value\<close>
text \<open>@{datatype[display,margin=40,show_abbrevs] Value}\<close>
snipend -


subsection \<open>Term semantics\<close>

text \<open>
The core expression evaluation functions need to be introduced.
\<close>

snipbegin \<open>eval\<close>
text \<open>@{term_type[mode=type_def] unary_eval}\\
@{term_type[mode=type_def] bin_eval}\<close>
snipend -

text \<open>
We then provide the full semantics of IR expressions.
\<close>

no_translations
  ("prop") "P \<and> Q \<Longrightarrow> R" <= ("prop") "P \<Longrightarrow> Q \<Longrightarrow> R"
translations
  ("prop") "P \<Longrightarrow> Q \<Longrightarrow> R" <= ("prop") "P \<and> Q \<Longrightarrow> R"
snipbegin \<open>tree-semantics\<close>
text \<open>
\induct{@{thm[mode=Rule] evaltree.UnaryExpr [no_vars]}}{semantics:unary}
\induct{@{thm[mode=Rule] evaltree.BinaryExpr [no_vars]}}{semantics:binary}
\induct{@{thm[mode=Rule] evaltree.ConditionalExpr [no_vars]}}{semantics:conditional}
\induct{@{thm[mode=Rule] evaltree.ConstantExpr [no_vars]}}{semantics:constant}
\induct{@{thm[mode=Rule] evaltree.ParameterExpr [no_vars]}}{semantics:parameter}
\induct{@{thm[mode=Rule] evaltree.LeafExpr [no_vars]}}{semantics:leaf}
\<close>
snipend -
no_translations
  ("prop") "P \<Longrightarrow> Q \<Longrightarrow> R" <= ("prop") "P \<and> Q \<Longrightarrow> R"
translations
  ("prop") "P \<and> Q \<Longrightarrow> R" <= ("prop") "P \<Longrightarrow> Q \<Longrightarrow> R"


text \<open>And show that expression evaluation is deterministic.\<close>

snipbegin \<open>tree-evaluation-deterministic\<close>
text \<open>@{thm[display] evalDet [no_vars]}\<close>
snipend -


text \<open>
We then want to start demonstrating the obligations for optimizations.
For this we define refinement over terms.
\<close>

snipbegin \<open>expression-refinement\<close>
text \<open>@{thm le_expr_def [no_vars]} \<close>
snipend -

text \<open>
To motivate this definition we show the obligations generated
by optimization definitions.
\<close>

phase SnipPhase
  terminating size
begin
snipbegin \<open>InverseLeftSub\<close>
optimization InverseLeftSub:
  "(x - y) + y \<longmapsto> x"
snipend -
  snipbegin \<open>InverseLeftSubObligation\<close>
  text \<open>@{subgoals[display]}\<close>
  snipend -
  using RedundantSubAdd by auto

snipbegin \<open>InverseRightSub\<close>
optimization InverseRightSub: "y + (x - y) \<longmapsto> x"
snipend -
  snipbegin \<open>InverseRightSubObligation\<close>
  text \<open>@{subgoals[display]}\<close>
  snipend -
  using RedundantSubAdd2(2) rewrite_termination.simps(1) apply blast
  using RedundantSubAdd2(1) rewrite_preservation.simps(1) by blast
end

snipbegin \<open>expression-refinement-monotone\<close>
text \<open>@{thm[display,margin=60] mono_unary}
@{thm[display,margin=60] mono_binary}
@{thm[display,margin=60] mono_conditional}
\<close>
snipend -

phase SnipPhase 
  terminating size
begin
snipbegin \<open>BinaryFoldConstant\<close>
optimization BinaryFoldConstant: "BinaryExpr op (const v1) (const v2) \<longmapsto> ConstantExpr (bin_eval op v1 v2)"
snipend -
  snipbegin \<open>BinaryFoldConstantObligation\<close>
  text \<open>@{subgoals[display]}\<close>
  snipend -
  using BinaryFoldConstant(1) by auto

snipbegin \<open>AddCommuteConstantRight\<close>
optimization AddCommuteConstantRight:
  "(const v) + y \<longmapsto> y + (const v) when \<not>(is_ConstantExpr y)"
snipend -
  snipbegin \<open>AddCommuteConstantRightObligation\<close>
  text \<open>@{subgoals[display,margin=50]}\<close>
  snipend -
  using AddShiftConstantRight by auto

snipbegin \<open>AddNeutral\<close>
optimization AddNeutral: "x + (const (IntVal 32 0)) \<longmapsto> x"
snipend -
  snipbegin \<open>AddNeutralObligation\<close>
  text \<open>@{subgoals[display]}\<close>
  snipend -
  apply auto
  using AddNeutral(1) rewrite_preservation.simps(1) by force

snipbegin \<open>AddToSub\<close>
optimization AddToSub: "-x + y \<longmapsto> y - x"
snipend -
  snipbegin \<open>AddToSubObligation\<close>
  text \<open>@{subgoals[display]}\<close>
  snipend -
  using AddLeftNegateToSub by auto

end

definition trm where "trm = size"

lemma trm_defn[size_simps]:
  "trm x = size x"
  by (simp add: trm_def)

snipbegin \<open>phase\<close>
phase AddCanonicalizations
  terminating trm
begin
  text_raw "\\dots"
end
snipend -

hide_const (open) "Form.wf_stamp"

snipbegin \<open>phase-example\<close>
phase Conditional
  terminating trm
begin
snipend -

snipbegin \<open>phase-example-1\<close>optimization NegateCond: "((!c) ? t : f) \<longmapsto> (c ? f : t)"snipend -
  apply (simp add: size_simps)
  using ConditionalPhase.NegateConditionFlipBranches(1) by simp

snipbegin \<open>phase-example-2\<close>optimization TrueCond: "(true ? t : f) \<longmapsto> t"snipend -
  by (auto simp: trm_def)

snipbegin \<open>phase-example-3\<close>optimization FalseCond: "(false ? t : f) \<longmapsto> f"snipend -
  by (auto simp: trm_def)

snipbegin \<open>phase-example-4\<close>optimization BranchEqual: "(c ? x : x) \<longmapsto> x"snipend -
  by (auto simp: trm_def)
 
snipbegin \<open>phase-example-5\<close>optimization LessCond: "((u < v) ? t : f) \<longmapsto> t
                   when (stamp_under (stamp_expr u) (stamp_expr v) 
                            \<and> wf_stamp u \<and> wf_stamp v)"snipend -
  apply (auto simp: trm_def)
  using ConditionalPhase.condition_bounds_x(1)
  by (metis(full_types) StampEvalThms.wf_stamp_def TreeSnippets.wf_stamp_def bin_eval.simps(12) stamp_under_defn)

snipbegin \<open>phase-example-6\<close>optimization condition_bounds_y: "((x < y) ? x : y) \<longmapsto> y
                   when (stamp_under (stamp_expr y) (stamp_expr x) \<and> wf_stamp x \<and> wf_stamp y)"snipend -
  apply (auto simp: trm_def)
  using ConditionalPhase.condition_bounds_y(1)
  by (metis(full_types) StampEvalThms.wf_stamp_def TreeSnippets.wf_stamp_def bin_eval.simps(12) stamp_under_defn_inverse)


snipbegin \<open>phase-example-7\<close>end snipend -

lemma simplified_binary: "\<not>(is_ConstantExpr b) \<Longrightarrow> size (BinaryExpr op a b) = size a + size b + 2"
  by (induction b; induction op; auto simp: is_ConstantExpr_def)

thm bin_size
thm bin_const_size
thm unary_size
thm size_non_add
snipbegin \<open>termination\<close>
text \<open>
@{thm[display,margin=80] unary_size}
@{thm[display,margin=80] bin_const_size}
@{thm[display,margin=80] (concl) simplified_binary}
@{thm[display,margin=80] cond_size}
@{thm[display,margin=80] const_size}
@{thm[display,margin=80] param_size}
@{thm[display,margin=80] leaf_size}
\<close>
snipend -


(* definition 5 (semantics-preserving) is there a distinction in Isabelle? *)

snipbegin \<open>graph-representation\<close>
text \<open>@{bold \<open>typedef\<close>} IRGraph = 

@{term[source] \<open>{g :: ID \<rightharpoonup> (IRNode \<times> Stamp) . finite (dom g)}\<close>}\<close>
snipend -

no_translations
  ("prop") "P \<and> Q \<Longrightarrow> R" <= ("prop") "P \<Longrightarrow> Q \<Longrightarrow> R"
translations
  ("prop") "P \<Longrightarrow> Q \<Longrightarrow> R" <= ("prop") "P \<and> Q \<Longrightarrow> R"
snipbegin \<open>graph2tree\<close>
text \<open>
\induct{@{thm[mode=Rule] rep.ConstantNode [no_vars]}}{rep:constant}
\induct{@{thm[mode=Rule] rep.ParameterNode [no_vars]}}{rep:parameter}
\induct{@{thm[mode=Rule] rep.ConditionalNode [no_vars]}}{rep:conditional}
\induct{@{thm[mode=Rule] rep.AbsNode [no_vars]}}{rep:unary}
\induct{@{thm[mode=Rule] rep.SignExtendNode [no_vars]}}{rep:convert}
\induct{@{thm[mode=Rule] rep.AddNode [no_vars]}}{rep:binary}
\induct{@{thm[mode=Rule] rep.LeafNode [no_vars]}}{rep:leaf}
\induct{@{thm[mode=Rule] rep.RefNode [no_vars]}}{rep:ref}
\<close>
snipend -

snipbegin \<open>tree2graph\<close>
text \<open>
\induct{@{thm[mode=Rule] unrep.UnaryNodeSame [no_vars]}}{unrep:unarysame}
\induct{@{thm[mode=Rule] unrep.ConstantNodeNew [no_vars]}}{unrep:constantnew}
\induct{@{thm[mode=Rule] unrep.ParameterNodeNew [no_vars]}}{unrep:parameternew}
\induct{@{thm[mode=Rule] unrep.UnaryNodeNew [no_vars]}}{unrep:unarynew}
\induct{@{thm[mode=Rule] unrep.BinaryNodeNew [no_vars]}}{unrep:binarynew}
\induct{@{thm[mode=Rule] unrep.AllLeafNodes [no_vars]}}{unrep:leaf}
\<close>
snipend -
no_translations
  ("prop") "P \<Longrightarrow> Q \<Longrightarrow> R" <= ("prop") "P \<and> Q \<Longrightarrow> R"
translations
  ("prop") "P \<and> Q \<Longrightarrow> R" <= ("prop") "P \<Longrightarrow> Q \<Longrightarrow> R"


snipbegin \<open>preeval\<close>
text \<open>@{thm is_preevaluated.simps}\<close>
snipend -

snipbegin \<open>deterministic-representation\<close>
text \<open>@{thm[display] repDet [no_vars]}\<close>
snipend -
thm_oracles repDet

snipbegin \<open>well-formed-term-graph\<close>
text "@{thm (rhs) wf_term_graph_def [no_vars]}"
snipend -

(* definition 9 (well-formed graph) no? *)

snipbegin \<open>graph-semantics\<close>
text \<open>@{thm encodeeval_def}\<close>
snipend -

snipbegin \<open>graph-semantics-deterministic\<close>
text \<open>@{thm graphDet [no_vars]}\<close>
snipend -
thm_oracles graphDet

notation (latex)
  graph_refinement ("\<^latex>\<open>term-graph-refinement\<close> _")

snipbegin \<open>graph-refinement\<close>
text \<open>@{thm[display, margin=60] graph_refinement_def [no_vars]}\<close>
snipend -

(* hide as_set, should treat IRGraph as a set of pairs in paper *)
translations
  "n" <= "CONST as_set n"

snipbegin \<open>graph-semantics-preservation\<close>
text \<open>@{thm[display, margin=30] graph_semantics_preservation_subscript [no_vars]}\<close>
snipend -
thm_oracles graph_semantics_preservation_subscript

snipbegin \<open>maximal-sharing\<close>
text \<open>@{thm[display, margin=50] maximal_sharing [no_vars]}\<close>
snipend -

snipbegin \<open>tree-to-graph-rewriting\<close>
text \<open>@{thm[display, margin=30] tree_to_graph_rewriting [no_vars]}\<close>
snipend -
thm_oracles tree_to_graph_rewriting

snipbegin \<open>term-graph-refines-term\<close>
text \<open>@{thm[display] graph_represents_expression_def [no_vars]}\<close>
snipend -

snipbegin \<open>term-graph-evaluation\<close>
text \<open>@{thm[display] term_graph_evaluation [no_vars]}\<close>
snipend -

snipbegin \<open>graph-construction\<close>
text \<open>@{thm[display, margin=40] graph_construction [no_vars]}\<close>
snipend -
thm_oracles graph_construction

snipbegin \<open>term-graph-reconstruction\<close>
text \<open>@{thm[display] term_graph_reconstruction [no_vars]}\<close>
snipend -

snipbegin \<open>refined-insert\<close>
text \<open>@{thm[display, margin=40] refined_insert [no_vars]}\<close>
snipend -

end
