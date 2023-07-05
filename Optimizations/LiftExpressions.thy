section "Lifting expression refinement to graph transformations"

text \<open>
Optimizations of expression trees are simpler to encode and verify than
equivalent graph transformations.
However, to be effective, we still wish to perform
optimizations as transformations of the graph rather than
converting between representations to perform an optimization.

The following theories provide a mechanism to produce a graph transformation
function from the verified expression optimization.
Additionally, a property that, if the optimization is a refinement
at the expression level, then the graph transformation function 
preserves the semantics when applied.
\<close>

theory LiftExpressions
  imports
    Canonicalizations.Common
    Graph.IRGraph
    Semantics.TreeToGraphThms
    "HOL-Library.Finite_Map"
begin

type_synonym Pattern = "(nat, IRNode) fmap"

text \<open>
A pattern is a mechanism to represent expression trees with graph nodes.
Each pattern forms a subgraph starting from root node, 0.
The node identifiers used by the pattern need not correspond to any concrete graph.
\<close>

fun un_expr_to_node :: "IRUnaryOp \<Rightarrow> (nat \<Rightarrow> IRNode)" where
  "un_expr_to_node UnaryAbs = AbsNode" |
  "un_expr_to_node UnaryNeg = NegateNode" |
  "un_expr_to_node UnaryNot = NotNode" |
  "un_expr_to_node UnaryLogicNegation = LogicNegationNode" |
  "un_expr_to_node (UnaryNarrow inp res) = NarrowNode inp res" |
  "un_expr_to_node (UnarySignExtend inp res) = SignExtendNode inp res" |
  "un_expr_to_node (UnaryZeroExtend inp res) = ZeroExtendNode inp res" |
  "un_expr_to_node UnaryIsNull = IsNullNode" |
  "un_expr_to_node UnaryReverseBytes = ReverseBytesNode" |
  "un_expr_to_node UnaryBitCount = BitCountNode"

fun bin_expr_to_node :: "IRBinaryOp \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> IRNode)" where
  "bin_expr_to_node BinAdd = AddNode" |
  "bin_expr_to_node BinMul = MulNode" |
  "bin_expr_to_node BinSub = SubNode" |
  "bin_expr_to_node BinAnd = AndNode" |
  "bin_expr_to_node BinOr = OrNode" |
  "bin_expr_to_node BinXor = XorNode" |
  "bin_expr_to_node BinShortCircuitOr = ShortCircuitOrNode" |
  "bin_expr_to_node BinLeftShift = LeftShiftNode" |
  "bin_expr_to_node BinRightShift = RightShiftNode" |
  "bin_expr_to_node BinURightShift = UnsignedRightShiftNode" |
  "bin_expr_to_node BinIntegerEquals = IntegerEqualsNode" |
  "bin_expr_to_node BinIntegerLessThan = IntegerLessThanNode" |
  "bin_expr_to_node BinIntegerBelow = IntegerBelowNode" |
  "bin_expr_to_node BinIntegerTest = IntegerTestNode" |
  "bin_expr_to_node BinIntegerNormalizeCompare = IntegerNormalizeCompareNode" |
  "bin_expr_to_node BinIntegerMulHigh = IntegerMulHighNode"

fun gen_pattern :: "IRExpr \<Rightarrow> (nat \<times> Pattern) \<Rightarrow> (nat \<times> Pattern)" where
  "gen_pattern (UnaryExpr op x) (n, p) =
    (let (n', p') = gen_pattern x (n + 1, p) in
      (n', fmupd n ((un_expr_to_node op) (n + 1)) p'))" |
  "gen_pattern (BinaryExpr op x y) (n, p) =
    (let (n', p') = gen_pattern x (n + 1, p) in
    (let (n'', p'') = gen_pattern y (n' + 1, p') in
      (n'', fmupd n ((bin_expr_to_node op) (n + 1) (n' + 1)) p'')))" |
  "gen_pattern (ConditionalExpr c t f) (n, p) =
    (let (n', p') = gen_pattern c (n + 1, p) in
    (let (n'', p'') = gen_pattern t (n' + 1, p') in
    (let (n''', p''') = gen_pattern f (n'' + 1, p'') in
      (n''', fmupd n (ConditionalNode (n + 1) (n' + 1) (n'' + 1)) p'''))))" |
  "gen_pattern (ParameterExpr i s) (n, p) =
    (n, fmupd n (ParameterNode i) p)" |
  "gen_pattern (ConstantExpr v) (n, p) =
    (n, fmupd n (ConstantNode v) p)" |
  "gen_pattern (VariableExpr v s) (n, p) = (n, p)" |
  "gen_pattern (ConstantVar v) (n, p) = (n, p)" |
  "gen_pattern (LeafExpr nid s) (n, p) = (n, p)"

lemma de_bruijn_increases:
  assumes "(n', p') = gen_pattern e (n, p)"
  shows "n' \<ge> n"
  using assms 
proof (induction e "(n, p)" arbitrary: n p n' p' rule: gen_pattern.induct)
  case (1 op x n p)
  then show ?case
    by (smt (verit, ccfv_threshold) Pair_inject add_leD2 case_prod_conv surj_pair gen_pattern.simps
        add.commute)
next
  case (2 op x y n p)
  obtain n' p' where x_def: "(n', p') = gen_pattern x (n + 1, p)"
    by (metis surj_pair)
  then have le1: "n + 1 \<le> n'"
    using 2 by blast
  obtain n'' p'' where y_def: "(n'', p'') = gen_pattern y (n' + 1, p')"
    by (metis surj_pair)
  then have le2: "n' + 1 \<le> n''"
    using 2(2) x_def by blast
  have "n \<le> n''"
    using le1 le2 by simp
  then show ?case
    using 2 unfolding gen_pattern.simps by (metis Pair_inject case_prod_conv x_def y_def)
next
  case (3 c t f n p)
  obtain n' p' where c_def: "(n', p') = gen_pattern c (n + 1, p)"
    by (metis surj_pair)
  then have le1: "n + 1 \<le> n'"
    using 3 by blast
  obtain n'' p'' where t_def: "(n'', p'') = gen_pattern t (n' + 1, p')"
    by (metis surj_pair)
  then have le2: "n' + 1 \<le> n''"
    using 3 c_def by blast
  have "n \<le> n''"
    using le1 le2 by simp
  obtain n''' p''' where f_def: "(n''', p''') = gen_pattern f (n'' + 1, p'')"
    by (metis surj_pair)
  then have le3: "n'' + 1 \<le> n'''"
    by (meson t_def c_def 3)
  have "n \<le> n'''"
    using le1 le2 le3 by simp
  then show ?case
    using 3 by (metis (no_types, lifting) Pair_inject prod.simps(2) f_def t_def gen_pattern.simps(3)
                c_def)
next
  case (4 i s n p)
  then show ?case
    by simp
next
  case (5 v n p)
  then show ?case
    by simp
next
  case (6 v s n p)
  then show ?case
    by simp
next
  case (7 v n p)
  then show ?case
    by simp
next
  case (8 v va)
  then show ?case
    by simp
qed

lemma domain_within_de_bruijn:
  assumes "fMax (fmdom p) \<le> n"
  assumes "(n', p') = gen_pattern e (n, p)"
  shows "fMax (fmdom p') \<le> n'"
  using assms(2,1)
proof (induction e "(n, p)" arbitrary: n p n' p' rule: gen_pattern.induct)
  case (1 op x n p n' p')
  obtain xn xp where x_def: "(xn, xp) = gen_pattern x (n + 1, p)"
    by (metis surj_pair)
  have p'def: "fmdom p' = fmdom xp |\<union>| {|n|}"
    using 1 unfolding gen_pattern.simps
    by (metis case_prod_conv fmdom_fmupd funion_fempty_right funion_finsert_right prod.inject x_def)
  have xnmore: "fMax (fmdom xp) \<le> xn"
    using 1 x_def by force
  have nless: "xn > n"
    using x_def de_bruijn_increases discrete by blast
  have "fMax (fmdom xp |\<union>| {|n|}) \<le> xn"
    using nless xnmore by fastforce
  then show ?case
    by (metis "1.prems"(1) p'def case_prod_conv gen_pattern.simps(1) prod.inject x_def)
next
  case (2 op x y n p)
  obtain xn xp where x_def: "(xn, xp) = gen_pattern x (n + 1, p)"
    by (metis surj_pair)
  obtain yn yp where y_def: "(yn, yp) = gen_pattern y (xn + 1, xp)"
    by (metis surj_pair)
  have p'def: "fmdom p' = fmdom yp |\<union>| {|n|}"
    using 2 unfolding gen_pattern.simps
    by (metis (mono_tags, lifting) Pair_inject fmdom_fmupd funion_finsert_right old.prod.case y_def
        sup_bot_right x_def)
  have ynmore: "fMax (fmdom yp) \<le> yn"
    using 2 y_def trans_le_add1 x_def by presburger
  have "xn > n"
    by (metis x_def de_bruijn_increases discrete)
  then have nless: "yn > n"
    by (metis y_def de_bruijn_increases discrete order.strict_trans)
  have "fMax (fmdom p') \<le> yn"
    using nless by (auto simp add: p'def ynmore)
  then show ?case
    using 2(3) unfolding gen_pattern.simps by (metis Pair_inject case_prod_conv x_def y_def)
next
  case (3 c t f n p)
  obtain cn cp where c_def: "(cn, cp) = gen_pattern c (n + 1, p)"
    by (metis surj_pair)
  obtain tn tp where t_def: "(tn, tp) = gen_pattern t (cn + 1, cp)"
    by (metis surj_pair)
  obtain fn fp where f_def: "(fn, fp) = gen_pattern f (tn + 1, tp)"
    by (metis surj_pair)
  have p'def: "fmdom p' = fmdom fp |\<union>| {|n|}"
    by (smt (verit, del_insts) Pair_inject finsert_is_funion fmdom_fmupd funion_commute f_def t_def
        old.prod.case c_def gen_pattern.simps 3)
  have fnmore: "fMax (fmdom fp) \<le> fn"
    using 3 f_def trans_le_add1 c_def t_def by presburger
  have "cn > n"
    by (metis c_def de_bruijn_increases discrete)
  then have "tn > n"
    by (metis t_def de_bruijn_increases discrete order.strict_trans)
  then have nless: "fn > n"
    by (metis f_def de_bruijn_increases discrete order.strict_trans)
  have "fMax (fmdom p') \<le> fn"
    using nless fnmore p'def by force
  then show ?case
    by (metis (no_types, lifting) c_def case_prod_conv f_def old.prod.inject gen_pattern.simps(3)
        3(4) t_def)
next
  case (4 i s n p)
  then show ?case
    by auto
next
  case (5 v n p)
  then show ?case
    by auto
next
  case (6 v s n p)
  then show ?case
    by auto
next
  case (7 v n p)
  then show ?case
    by auto
next
  case (8 nid s n p)
  then show ?case
    by auto
qed

type_synonym Transformation = "(nat \<times> nat)"

fun gen_opt :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> (Pattern \<times> Transformation)" where
  "gen_opt lhs rhs =
    (let (n, p) = gen_pattern lhs (0, fmempty) in
    (let (n', p') = gen_pattern rhs ((n + 1), p) in
      (p', (0, n + 1))))"

type_synonym Morphism = "(nat, nat) fmap"

fun match_subtree :: "IRGraph \<Rightarrow> Pattern \<Rightarrow> ID \<Rightarrow> Morphism option" where
  "match_subtree g p n =
    (case (fmlookup p 0) of
      Some node \<Rightarrow> 
      (if (is_same_ir_node_type (kind g n) node)
        then Some (fmupd 0 n (fmempty))
        else None)
    | None \<Rightarrow> None)"

fun of_list :: "'a option list \<Rightarrow> 'a option" where
  "of_list (x # xs) = x" |
  "of_list [] = None"

definition filter_none :: "'a option list \<Rightarrow> 'a option list" where
  "filter_none = filter (\<lambda> v \<Rightarrow> v \<noteq> None)"

fun match :: "IRGraph \<Rightarrow> Pattern \<Rightarrow> Morphism option" where
  "match g p =
    of_list
     (filter_none
      (map (match_subtree g p) (sorted_list_of_set (ids g))))"

fun is_match :: "IRGraph \<Rightarrow> Pattern \<Rightarrow> bool" where
  "is_match g p = (match g p \<noteq> None)"

lemma match_none:
  "match g p = None"
  unfolding match.simps filter_none_def match_subtree.simps
  sorry

lemma match_false:
  "fcard (fmdom p) > 0 \<longrightarrow> is_match g p = False"
  using is_match.simps match_none by presburger

fun replace :: "(Pattern \<times> Transformation) \<Rightarrow> IRGraph \<Rightarrow> IRGraph" where
  "replace (p, t) g = 
    (case fmlookup p (snd t) of
      Some node \<Rightarrow> replace_node (fst t) (node, stamp g (fst t)) g |
      None \<Rightarrow> g)"

fun apply_opt :: "(Pattern \<times> Transformation) \<Rightarrow> IRGraph \<Rightarrow> IRGraph" where
  "apply_opt (p, t) g =
    (let morph = match g p in
      (if (is_match g p) then replace (p, t) g else g)
    )"

experiment begin
lemma
  assumes "([g\<^sub>1, m, p] \<turnstile> n\<^sub>1 \<mapsto> v) \<longrightarrow> ([g\<^sub>1, m, p] \<turnstile> n\<^sub>2 \<mapsto> v)"
  assumes "g\<^sub>2 = replace_node n\<^sub>1 (kind g\<^sub>1 n\<^sub>2, stamp g\<^sub>1 n\<^sub>1) g\<^sub>1"
  shows "([g\<^sub>2, m, p] \<turnstile> n\<^sub>1 \<mapsto> v)"
  using assms sorry

lemma
  assumes "([g\<^sub>1, m, p] \<turnstile> n\<^sub>1 \<mapsto> v) \<longrightarrow> ([g\<^sub>1, m, p] \<turnstile> n\<^sub>2 \<mapsto> v)"
  assumes "g\<^sub>2 = replace_node n\<^sub>1 (kind g\<^sub>1 n\<^sub>2, stamp g\<^sub>1 n\<^sub>1) g\<^sub>1"
  shows "graph_refinement g\<^sub>1 g\<^sub>2"
  using assms sorry
end

theorem
  assumes "e\<^sub>1 \<ge> e\<^sub>2"
  assumes "f = apply_opt (gen_opt e\<^sub>1 e\<^sub>2)"
  assumes "g\<^sub>2 = f g\<^sub>1"
  shows "graph_refinement g\<^sub>1 g\<^sub>2"
  using assms
proof (cases "is_match g\<^sub>1 (fst (gen_opt e\<^sub>1 e\<^sub>2))")
  case True
  then show ?thesis
    by (metis is_match.elims(1) match_none)
next
  case False
  then show ?thesis
    by (metis assms(2,3) apply_opt.elims dual_order.refl fst_conv subset_refines)
qed

definition ex1 :: "(IRExpr \<times> IRExpr)" where
  "ex1 = (
      (BinaryExpr BinMul
        (VariableExpr ''x'' (default_stamp))
        (ConstantExpr (IntVal 32 0))),
      (ConstantExpr (IntVal 32 0)))"

definition ex2 :: "(IRExpr \<times> IRExpr)" where
  "ex2 = (
      (BinaryExpr BinMul
        (VariableExpr ''x'' (default_stamp))
        (ConstantExpr (IntVal 32 1))),
      (VariableExpr ''x'' (default_stamp)))"

definition ex3 :: "(IRExpr \<times> IRExpr)" where
  "ex3 = (
      (BinaryExpr BinMul
        (VariableExpr ''x'' (default_stamp))
        (ConstantExpr (IntVal 32 2))),
      (BinaryExpr BinLeftShift
        (VariableExpr ''x'' (default_stamp)))
        (ConstantExpr (IntVal 32 1))
      )"

value "{fmlookup (snd (gen_pattern (fst ex1)
        (0, fmempty))) x | x . x \<in> {0, 1, 2}}"

value "{fmlookup (snd (gen_pattern (fst ex2)
        (0, fmempty))) x | x . x \<in> {0, 1, 2}}"

value "{fmlookup (snd (gen_pattern (fst ex3)
        (0, fmempty))) x | x . x \<in> {0, 1, 2, 3, 4}}"

value "(snd (gen_opt (fst ex1) (snd ex1)))"
value "{fmlookup (fst (gen_opt (fst ex1) (snd ex1))) x | x . x \<in> {0, 1, 2, 3, 4}}"

value "(snd (gen_opt (fst ex2) (snd ex2)))"
value "{fmlookup (fst (gen_opt (fst ex2) (snd ex2))) x | x . x \<in> {0, 1, 2, 3, 4}}"

value "(snd (gen_opt (fst ex3) (snd ex3)))"
value "{fmlookup (fst (gen_opt (fst ex3) (snd ex3))) x | x . x \<in> {0, 1, 2, 3, 4, 5, 6}}"

definition exg1 :: "IRGraph" where
  "exg1 = irgraph [
    (0, StartNode None 1, VoidStamp),
    (1, MulNode 2 3, default_stamp),
    (2, ConstantNode (IntVal 32 10), default_stamp),
    (3, ConstantNode (IntVal 32 0), default_stamp)
   ]"

value "apply_opt (gen_opt (fst ex1) (snd ex1)) exg1"

end