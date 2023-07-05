subsection \<open>Tree to Graph Theorems\<close>

theory TreeToGraphThms
imports
  IRTreeEvalThms
  IRGraphFrames
  "HOL-Eisbach.Eisbach"
  "HOL-Eisbach.Eisbach_Tools"
begin

subsubsection \<open>Extraction and Evaluation of Expression Trees is Deterministic.\<close>

text \<open>First, we prove some extra rules that relate each
  type of IRNode to the corresponding IRExpr type that 'rep' will produce.
  These are very helpful for proving that 'rep' is deterministic.
\<close>

named_theorems rep

lemma rep_constant [rep]: 
  "g \<turnstile> n \<simeq> e \<Longrightarrow> 
   kind g n = ConstantNode c \<Longrightarrow> 
   e = ConstantExpr c"
  by (induction rule: rep.induct; auto)
  
lemma rep_parameter [rep]: 
  "g \<turnstile> n \<simeq> e \<Longrightarrow> 
   kind g n = ParameterNode i \<Longrightarrow>
   (\<exists>s. e = ParameterExpr i s)"
  by (induction rule: rep.induct; auto)

lemma rep_conditional [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = ConditionalNode c t f \<Longrightarrow>
   (\<exists> ce te fe. e = ConditionalExpr ce te fe)"
  by (induction rule: rep.induct; auto)

lemma rep_abs [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = AbsNode x \<Longrightarrow>
   (\<exists>xe. e = UnaryExpr UnaryAbs xe)"
  by (induction rule: rep.induct; auto)

lemma rep_reverse_bytes [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = ReverseBytesNode x \<Longrightarrow>
   (\<exists>xe. e = UnaryExpr UnaryReverseBytes xe)"
  by (induction rule: rep.induct; auto)

lemma rep_bit_count [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = BitCountNode x \<Longrightarrow>
   (\<exists>xe. e = UnaryExpr UnaryBitCount xe)"
  by (induction rule: rep.induct; auto)

lemma rep_not [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = NotNode x \<Longrightarrow>
   (\<exists>xe. e = UnaryExpr UnaryNot xe)"
  by (induction rule: rep.induct; auto)

lemma rep_negate [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = NegateNode x \<Longrightarrow>
   (\<exists>xe. e = UnaryExpr UnaryNeg xe)"
  by (induction rule: rep.induct; auto)

lemma rep_logicnegation [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = LogicNegationNode x \<Longrightarrow>
   (\<exists>xe. e = UnaryExpr UnaryLogicNegation xe)"
  by (induction rule: rep.induct; auto)

lemma rep_add [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = AddNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinAdd xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_sub [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = SubNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinSub xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_mul [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = MulNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinMul xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_and [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = AndNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinAnd xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_or [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = OrNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinOr xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_xor [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = XorNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinXor xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_short_circuit_or [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = ShortCircuitOrNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinShortCircuitOr xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_left_shift [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = LeftShiftNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinLeftShift xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_right_shift [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = RightShiftNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinRightShift xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_unsigned_right_shift [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = UnsignedRightShiftNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinURightShift xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_integer_below [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = IntegerBelowNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinIntegerBelow xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_integer_equals [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = IntegerEqualsNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinIntegerEquals xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_integer_less_than [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = IntegerLessThanNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinIntegerLessThan xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_integer_mul_high [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = IntegerMulHighNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinIntegerMulHigh xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_integer_test [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = IntegerTestNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinIntegerTest xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_integer_normalize_compare [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = IntegerNormalizeCompareNode x y \<Longrightarrow>
   (\<exists>xe ye. e = BinaryExpr BinIntegerNormalizeCompare xe ye)"
  by (induction rule: rep.induct; auto)

lemma rep_narrow [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = NarrowNode ib rb x \<Longrightarrow>
   (\<exists>x. e = UnaryExpr (UnaryNarrow ib rb) x)"
  by (induction rule: rep.induct; auto)
 
lemma rep_sign_extend [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = SignExtendNode ib rb x \<Longrightarrow>
   (\<exists>x. e = UnaryExpr (UnarySignExtend ib rb) x)"
  by (induction rule: rep.induct; auto)

lemma rep_zero_extend [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = ZeroExtendNode ib rb x \<Longrightarrow>
   (\<exists>x. e = UnaryExpr (UnaryZeroExtend ib rb) x)"
  by (induction rule: rep.induct; auto)

lemma rep_load_field [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   is_preevaluated (kind g n) \<Longrightarrow>
   (\<exists>s. e = LeafExpr n s)"
  by (induction rule: rep.induct; auto)

lemma rep_bytecode_exception [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   (kind g n) = BytecodeExceptionNode gu st n' \<Longrightarrow>
   (\<exists>s. e = LeafExpr n s)"
  by (induction rule: rep.induct; auto)

lemma rep_new_array [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   (kind g n) = NewArrayNode len st n' \<Longrightarrow>
   (\<exists>s. e = LeafExpr n s)"
  by (induction rule: rep.induct; auto)

lemma rep_array_length [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   (kind g n) = ArrayLengthNode x n' \<Longrightarrow>
   (\<exists>s. e = LeafExpr n s)"
  by (induction rule: rep.induct; auto)

lemma rep_load_index [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   (kind g n) = LoadIndexedNode index guard x n' \<Longrightarrow>
   (\<exists>s. e = LeafExpr n s)"
  by (induction rule: rep.induct; auto)

lemma rep_store_index [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   (kind g n) = StoreIndexedNode check val st index guard x n' \<Longrightarrow>
   (\<exists>s. e = LeafExpr n s)"
  by (induction rule: rep.induct; auto)

lemma rep_ref [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = RefNode n' \<Longrightarrow>
   g \<turnstile> n' \<simeq> e"
  by (induction rule: rep.induct; auto)

lemma rep_pi [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
   kind g n = PiNode n' gu \<Longrightarrow>
   g \<turnstile> n' \<simeq> e"
  by (induction rule: rep.induct; auto)

lemma rep_is_null [rep]:
  "g \<turnstile> n \<simeq> e \<Longrightarrow> 
   kind g n = IsNullNode x \<Longrightarrow> 
   (\<exists>xe. e = (UnaryExpr UnaryIsNull xe))" 
  by (induction rule: rep.induct; auto)

method solve_det uses node =
  (match node in "kind _ _ = node _" for node \<Rightarrow> 
    \<open>match rep in r: "_ \<Longrightarrow> _ = node _ \<Longrightarrow> _" \<Rightarrow> 
      \<open>match IRNode.inject in i: "(node _ = node _) = _" \<Rightarrow>
        \<open>match RepE in e: "_ \<Longrightarrow> (\<And>x. _ = node x \<Longrightarrow> _) \<Longrightarrow> _" \<Rightarrow>
          \<open>match IRNode.distinct in d: "node _ \<noteq> RefNode _" \<Rightarrow>
            \<open>match IRNode.distinct in f: "node _  \<noteq> PiNode _ _" \<Rightarrow>
              \<open>metis i e r d f\<close>\<close>\<close>\<close>\<close>\<close> |
   match node in "kind _ _ = node _ _" for node \<Rightarrow> 
    \<open>match rep in r: "_ \<Longrightarrow> _ = node _ _ \<Longrightarrow> _" \<Rightarrow> 
      \<open>match IRNode.inject in i: "(node _ _ = node _ _) = _" \<Rightarrow>
        \<open>match RepE in e: "_ \<Longrightarrow> (\<And>x y. _ = node x y \<Longrightarrow> _) \<Longrightarrow> _" \<Rightarrow>
          \<open>match IRNode.distinct in d: "node _ _ \<noteq> RefNode _" \<Rightarrow>
            \<open>match IRNode.distinct in f: "node _ _ \<noteq> PiNode _ _" \<Rightarrow>
              \<open>metis i e r d f\<close>\<close>\<close>\<close>\<close>\<close> |
   match node in "kind _ _ = node _ _ _" for node \<Rightarrow> 
    \<open>match rep in r: "_ \<Longrightarrow> _ = node _ _ _ \<Longrightarrow> _" \<Rightarrow> 
      \<open>match IRNode.inject in i: "(node _ _ _ = node _ _ _) = _" \<Rightarrow>
        \<open>match RepE in e: "_ \<Longrightarrow> (\<And>x y z. _ = node x y z \<Longrightarrow> _) \<Longrightarrow> _" \<Rightarrow>
          \<open>match IRNode.distinct in d: "node _ _ _ \<noteq> RefNode _" \<Rightarrow>
            \<open>match IRNode.distinct in f: "node _ _ _ \<noteq> PiNode _ _" \<Rightarrow>
              \<open>metis i e r d f\<close>\<close>\<close>\<close>\<close>\<close> |
  match node in "kind _ _ = node _ _ _" for node \<Rightarrow> 
    \<open>match rep in r: "_ \<Longrightarrow> _ = node _ _ _ \<Longrightarrow> _" \<Rightarrow> 
      \<open>match IRNode.inject in i: "(node _ _ _ = node _ _ _) = _" \<Rightarrow>
        \<open>match RepE in e: "_ \<Longrightarrow> (\<And>x. _ = node _ _ x \<Longrightarrow> _) \<Longrightarrow> _" \<Rightarrow>
          \<open>match IRNode.distinct in d: "node _ _ _ \<noteq> RefNode _" \<Rightarrow>
            \<open>match IRNode.distinct in f: "node _ _ _ \<noteq> PiNode _ _" \<Rightarrow>
              \<open>metis i e r d f\<close>\<close>\<close>\<close>\<close>\<close>)

text \<open>Now we can prove that 'rep' and 'eval', and their list versions, are deterministic.
\<close>
lemma repDet:
  shows "(g \<turnstile> n \<simeq> e\<^sub>1) \<Longrightarrow> (g \<turnstile> n \<simeq> e\<^sub>2) \<Longrightarrow> e\<^sub>1 = e\<^sub>2"
proof (induction arbitrary: e\<^sub>2 rule: "rep.induct")
  case (ConstantNode n c)
  then show ?case 
    using rep_constant by simp
next
  case (ParameterNode n i s)
  then show ?case
    by (metis IRNode.distinct(3487,3525) ParameterNodeE rep_parameter)
next
  case (ConditionalNode n c t f ce te fe)
  then show ?case
    by (metis IRNode.distinct(897,935) IRNode.inject(8) ConditionalNodeE rep_conditional)
next
  case (AbsNode n x xe)
  then show ?case
    by (solve_det node: AbsNode)
next
  case (ReverseBytesNode n x xe)
  then show ?case
    by (solve_det node: ReverseBytesNode)
next
  case (BitCountNode n x xe)
  then show ?case
    by (solve_det node: BitCountNode)
next
  case (NotNode n x xe)
  then show ?case
    by (solve_det node: NotNode)
next
  case (NegateNode n x xe)
  then show ?case
    by (solve_det node: NegateNode)
next
  case (LogicNegationNode n x xe)
  then show ?case
    by (solve_det node: LogicNegationNode)
next
  case (AddNode n x y xe ye)
  then show ?case
    by (solve_det node: AddNode)
next
  case (MulNode n x y xe ye)
  then show ?case
    by (solve_det node: MulNode)
next
  case (SubNode n x y xe ye)
  then show ?case
    by (solve_det node: SubNode)
next
  case (AndNode n x y xe ye)
  then show ?case
    by (solve_det node: AndNode)
next
  case (OrNode n x y xe ye)
  then show ?case
    by (solve_det node: OrNode)
next
  case (XorNode n x y xe ye)
  then show ?case
    by (solve_det node: XorNode)
next
  case (ShortCircuitOrNode n x y xe ye)
  then show ?case
    by (solve_det node: ShortCircuitOrNode)
next
  case (LeftShiftNode n x y xe ye)
  then show ?case
    by (solve_det node: LeftShiftNode)
next
  case (RightShiftNode n x y xe ye)
  then show ?case
    by (solve_det node: RightShiftNode)
next
  case (UnsignedRightShiftNode n x y xe ye)
  then show ?case
    by (solve_det node: UnsignedRightShiftNode)
next
  case (IntegerBelowNode n x y xe ye)
  then show ?case
    by (solve_det node: IntegerBelowNode)
next
  case (IntegerEqualsNode n x y xe ye)
  then show ?case
    by (solve_det node: IntegerEqualsNode)
next
  case (IntegerLessThanNode n x y xe ye)
  then show ?case
    by (solve_det node: IntegerLessThanNode)
next
  case (IntegerTestNode n x y xe ye)
  then show ?case
    by (solve_det node: IntegerTestNode)
next
  case (IntegerNormalizeCompareNode n x y xe ye)
  then show ?case
    by (solve_det node: IntegerNormalizeCompareNode)
next
  case (IntegerMulHighNode n x xe)
  then show ?case
    by (solve_det node: IntegerMulHighNode)
next
  case (NarrowNode n x xe)
  then show ?case
    by (metis IRNode.distinct(3217,3255) IRNode.inject(36) NarrowNodeE rep_narrow)
next
  case (SignExtendNode n x xe)
  then show ?case
    by (metis IRNode.distinct(3535,3723) IRNode.inject(48) SignExtendNodeE rep_sign_extend)
next
  case (ZeroExtendNode n x xe)
  then show ?case
    by (metis IRNode.distinct(3559,3903) IRNode.inject(60) ZeroExtendNodeE rep_zero_extend)
next
  case (LeafNode n s)
  then show ?case
    by (metis is_preevaluated.simps(48,63) rep_load_field LeafNodeE)
next
  case (RefNode n')
  then show ?case
    using rep_ref by blast
next
  case (PiNode n v)
  then show ?case
    using rep_pi by blast
next
  case (IsNullNode n v)
  then show ?case
    by (metis IRNode.distinct(2461,2499) IRNode.inject(24) IsNullNodeE rep_is_null)
qed

lemma repAllDet:
  "g \<turnstile> xs \<simeq>\<^sub>L e1 \<Longrightarrow>
   g \<turnstile> xs \<simeq>\<^sub>L e2 \<Longrightarrow>
   e1 = e2"
proof (induction arbitrary: e2 rule: "replist.induct")
  case RepNil
  then show ?case
    using replist.cases by auto 
next
  case (RepCons x xe xs xse)
  then show ?case
    by (metis list.distinct(1) list.sel(1,3) repDet replist.cases) 
qed

lemma encodeEvalDet:
  "[g,m,p] \<turnstile> e \<mapsto> v1 \<Longrightarrow> 
   [g,m,p] \<turnstile> e \<mapsto> v2 \<Longrightarrow>
   v1 = v2"
  by (metis encodeeval_def evalDet repDet)

lemma graphDet: "([g,m,p] \<turnstile> n \<mapsto> v\<^sub>1) \<and> ([g,m,p] \<turnstile> n \<mapsto> v\<^sub>2) \<Longrightarrow> v\<^sub>1 = v\<^sub>2"
  by (auto simp add: encodeEvalDet)

subsubsection \<open>Monotonicity of Graph Refinement\<close>

text \<open>
Lift refinement monotonicity to graph level.
Hopefully these shouldn't really be required.
\<close>

lemma mono_abs:
  assumes "kind g1 n = AbsNode x \<and> kind g2 n = AbsNode x"
  assumes "(g1 \<turnstile> x \<simeq> xe1) \<and> (g2 \<turnstile> x \<simeq> xe2)"
  assumes "xe1 \<ge> xe2"
  assumes "(g1 \<turnstile> n \<simeq> e1) \<and> (g2 \<turnstile> n \<simeq> e2)"
  shows "e1 \<ge> e2"
  by (metis AbsNode assms mono_unary repDet)

lemma mono_not:
  assumes "kind g1 n = NotNode x \<and> kind g2 n = NotNode x"
  assumes "(g1 \<turnstile> x \<simeq> xe1) \<and> (g2 \<turnstile> x \<simeq> xe2)"
  assumes "xe1 \<ge> xe2"
  assumes "(g1 \<turnstile> n \<simeq> e1) \<and> (g2 \<turnstile> n \<simeq> e2)"
  shows "e1 \<ge> e2"
  by (metis NotNode assms mono_unary repDet)

lemma mono_negate:
  assumes "kind g1 n = NegateNode x \<and> kind g2 n = NegateNode x"
  assumes "(g1 \<turnstile> x \<simeq> xe1) \<and> (g2 \<turnstile> x \<simeq> xe2)"
  assumes "xe1 \<ge> xe2"
  assumes "(g1 \<turnstile> n \<simeq> e1) \<and> (g2 \<turnstile> n \<simeq> e2)"
  shows "e1 \<ge> e2"
  by (metis NegateNode assms mono_unary repDet)

lemma mono_logic_negation:
  assumes "kind g1 n = LogicNegationNode x \<and> kind g2 n = LogicNegationNode x"
  assumes "(g1 \<turnstile> x \<simeq> xe1) \<and> (g2 \<turnstile> x \<simeq> xe2)"
  assumes "xe1 \<ge> xe2"
  assumes "(g1 \<turnstile> n \<simeq> e1) \<and> (g2 \<turnstile> n \<simeq> e2)"
  shows "e1 \<ge> e2"
  by (metis LogicNegationNode assms mono_unary repDet)

lemma mono_narrow:
  assumes "kind g1 n = NarrowNode ib rb x \<and> kind g2 n = NarrowNode ib rb x"
  assumes "(g1 \<turnstile> x \<simeq> xe1) \<and> (g2 \<turnstile> x \<simeq> xe2)"
  assumes "xe1 \<ge> xe2"
  assumes "(g1 \<turnstile> n \<simeq> e1) \<and> (g2 \<turnstile> n \<simeq> e2)"
  shows "e1 \<ge> e2"
  by (metis NarrowNode assms mono_unary repDet)

lemma mono_sign_extend:
  assumes "kind g1 n = SignExtendNode ib rb x \<and> kind g2 n = SignExtendNode ib rb x"
  assumes "(g1 \<turnstile> x \<simeq> xe1) \<and> (g2 \<turnstile> x \<simeq> xe2)"
  assumes "xe1 \<ge> xe2"
  assumes "(g1 \<turnstile> n \<simeq> e1) \<and> (g2 \<turnstile> n \<simeq> e2)"
  shows "e1 \<ge> e2"
  by (metis SignExtendNode assms mono_unary repDet)

lemma mono_zero_extend:
  assumes "kind g1 n = ZeroExtendNode ib rb x \<and> kind g2 n = ZeroExtendNode ib rb x"
  assumes "(g1 \<turnstile> x \<simeq> xe1) \<and> (g2 \<turnstile> x \<simeq> xe2)"
  assumes "xe1 \<ge> xe2"
  assumes "(g1 \<turnstile> n \<simeq> e1) \<and> (g2 \<turnstile> n \<simeq> e2)"
  shows "e1 \<ge> e2"
  by (metis ZeroExtendNode assms mono_unary repDet)

lemma mono_conditional_graph:
  assumes "kind g1 n = ConditionalNode c t f \<and> kind g2 n = ConditionalNode c t f"
  assumes "(g1 \<turnstile> c \<simeq> ce1) \<and> (g2 \<turnstile> c \<simeq> ce2)"
  assumes "(g1 \<turnstile> t \<simeq> te1) \<and> (g2 \<turnstile> t \<simeq> te2)"
  assumes "(g1 \<turnstile> f \<simeq> fe1) \<and> (g2 \<turnstile> f \<simeq> fe2)"
  assumes "ce1 \<ge> ce2 \<and> te1 \<ge> te2 \<and> fe1 \<ge> fe2"
  assumes "(g1 \<turnstile> n \<simeq> e1) \<and> (g2 \<turnstile> n \<simeq> e2)"
  shows "e1 \<ge> e2"
  by (smt (verit, ccfv_SIG) ConditionalNode assms mono_conditional repDet le_expr_def)

lemma mono_add:
  assumes "kind g1 n = AddNode x y \<and> kind g2 n = AddNode x y"
  assumes "(g1 \<turnstile> x \<simeq> xe1) \<and> (g2 \<turnstile> x \<simeq> xe2)"
  assumes "(g1 \<turnstile> y \<simeq> ye1) \<and> (g2 \<turnstile> y \<simeq> ye2)"
  assumes "xe1 \<ge> xe2 \<and> ye1 \<ge> ye2"
  assumes "(g1 \<turnstile> n \<simeq> e1) \<and> (g2 \<turnstile> n \<simeq> e2)"
  shows "e1 \<ge> e2"
  by (metis (no_types, lifting) AddNode mono_binary assms repDet)

lemma mono_mul:
  assumes "kind g1 n = MulNode x y \<and> kind g2 n = MulNode x y"
  assumes "(g1 \<turnstile> x \<simeq> xe1) \<and> (g2 \<turnstile> x \<simeq> xe2)"
  assumes "(g1 \<turnstile> y \<simeq> ye1) \<and> (g2 \<turnstile> y \<simeq> ye2)"
  assumes "xe1 \<ge> xe2 \<and> ye1 \<ge> ye2"
  assumes "(g1 \<turnstile> n \<simeq> e1) \<and> (g2 \<turnstile> n \<simeq> e2)"
  shows "e1 \<ge> e2"
  by (metis (no_types, lifting) MulNode assms mono_binary repDet)

lemma term_graph_evaluation:
  "(g \<turnstile> n \<unlhd> e) \<Longrightarrow> (\<forall> m p v . ([m,p] \<turnstile> e \<mapsto> v) \<longrightarrow> ([g,m,p] \<turnstile> n \<mapsto> v))"
  using graph_represents_expression_def encodeeval_def by (auto; meson)

lemma encodes_contains:
  "g \<turnstile> n \<simeq> e \<Longrightarrow>
  kind g n \<noteq> NoNode"
  apply (induction rule: rep.induct)
  apply (match IRNode.distinct in e: "?n \<noteq> NoNode" \<Rightarrow> \<open>presburger add: e\<close>)+
  by fastforce+

lemma no_encoding:
  assumes "n \<notin> ids g"
  shows "\<not>(g \<turnstile> n \<simeq> e)"
  using assms apply simp apply (rule notI) by (induction e; simp add: encodes_contains)

lemma not_excluded_keep_type:
  assumes "n \<in> ids g1"
  assumes "n \<notin> excluded"
  assumes "(excluded \<unlhd> as_set g1) \<subseteq> as_set g2"
  shows "kind g1 n = kind g2 n \<and> stamp g1 n = stamp g2 n"
  using assms by (auto simp add: domain_subtraction_def as_set_def)

method metis_node_eq_unary for node :: "'a \<Rightarrow> IRNode" =
  (match IRNode.inject in i: "(node _ = node _) = _" \<Rightarrow> 
      \<open>metis i\<close>)
method metis_node_eq_binary for node :: "'a \<Rightarrow> 'a \<Rightarrow> IRNode" =
  (match IRNode.inject in i: "(node _ _ = node _ _) = _" \<Rightarrow> 
      \<open>metis i\<close>)
method metis_node_eq_ternary for node :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> IRNode" =
  (match IRNode.inject in i: "(node _ _ _ = node _ _ _) = _" \<Rightarrow> 
      \<open>metis i\<close>)

subsubsection \<open>Lift Data-flow Tree Refinement to Graph Refinement\<close>

theorem graph_semantics_preservation:
  assumes a: "e1' \<ge> e2'"
  assumes b: "({n'} \<unlhd> as_set g1) \<subseteq> as_set g2"
  assumes c: "g1 \<turnstile> n' \<simeq> e1'"
  assumes d: "g2 \<turnstile> n' \<simeq> e2'"
  shows "graph_refinement g1 g2"
  unfolding graph_refinement_def apply rule
  apply (metis b d ids_some no_encoding not_excluded_keep_type singleton_iff subsetI)
  apply (rule allI) apply (rule impI) apply (rule allI) apply (rule impI)
  unfolding graph_represents_expression_def
proof -
  fix n e1
  assume e: "n \<in> ids g1"
  assume f: "(g1 \<turnstile> n \<simeq> e1)"
  show "\<exists> e2. (g2 \<turnstile> n \<simeq> e2) \<and> e1 \<ge> e2"
  proof (cases "n = n'")
    case True
    have g: "e1 = e1'" 
      using f by (simp add: repDet True c)
    have h: "(g2 \<turnstile> n \<simeq> e2') \<and> e1' \<ge> e2'"
      using a by (simp add: d True)
    then show ?thesis 
      by (auto simp add: g)
  next
    case False
    have "n \<notin> {n'}"
      by (simp add: False)
    then have i: "kind g1 n = kind g2 n \<and> stamp g1 n = stamp g2 n"
      using not_excluded_keep_type b e by presburger
    show ?thesis 
      using f i
    proof (induction e1)
      case (ConstantNode n c)
      then show ?case
        by (metis eq_refl rep.ConstantNode)
    next
      case (ParameterNode n i s)
      then show ?case
        by (metis eq_refl rep.ParameterNode)
    next
      case (ConditionalNode n c t f ce1 te1 fe1)
      have k: "g1 \<turnstile> n \<simeq> ConditionalExpr ce1 te1 fe1" 
        using ConditionalNode by (simp add: ConditionalNode.hyps(2) rep.ConditionalNode f)
      obtain cn tn fn where l: "kind g1 n = ConditionalNode cn tn fn"
        by (auto simp add: ConditionalNode.hyps(1))
      then have mc: "g1 \<turnstile> cn \<simeq> ce1"
        using ConditionalNode.hyps(1,2) by simp
      from l have mt: "g1 \<turnstile> tn \<simeq> te1"
        using ConditionalNode.hyps(1,3) by simp
      from l have mf: "g1 \<turnstile> fn \<simeq> fe1"
        using ConditionalNode.hyps(1,4) by simp
      then show ?case
      proof -
        have "g1 \<turnstile> cn \<simeq> ce1" 
          by (simp add: mc)
        have "g1 \<turnstile> tn \<simeq> te1" 
          by (simp add: mt)
        have "g1 \<turnstile> fn \<simeq> fe1" 
          by (simp add: mf)
        have cer: "\<exists> ce2. (g2 \<turnstile> cn \<simeq> ce2) \<and> ce1 \<ge> ce2"
          using ConditionalNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_ternary ConditionalNode)
        have ter: "\<exists> te2. (g2 \<turnstile> tn \<simeq> te2) \<and> te1 \<ge> te2"
          using ConditionalNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_ternary ConditionalNode)
        have "\<exists> fe2. (g2 \<turnstile> fn \<simeq> fe2) \<and> fe1 \<ge> fe2"
          using ConditionalNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_ternary ConditionalNode)
        then have "\<exists> ce2 te2 fe2. (g2 \<turnstile> n \<simeq> ConditionalExpr ce2 te2 fe2) \<and> 
               ConditionalExpr ce1 te1 fe1 \<ge> ConditionalExpr ce2 te2 fe2"
          apply meson
          by (smt (verit, best) mono_conditional ConditionalNode.prems l rep.ConditionalNode cer ter)
        then show ?thesis
          by meson
      qed
    next
      case (AbsNode n x xe1)
      have k: "g1 \<turnstile> n \<simeq> UnaryExpr UnaryAbs xe1" 
        using AbsNode by (simp add: AbsNode.hyps(2) rep.AbsNode f)
      obtain xn where l: "kind g1 n = AbsNode xn"
        by (auto simp add: AbsNode.hyps(1))
      then have m: "g1 \<turnstile> xn \<simeq> xe1"
        using AbsNode.hyps(1,2) by simp
      then show ?case
      proof (cases "xn = n'")
        case True
        then have n: "xe1 = e1'" 
          using m by (simp add: repDet c)
        then have ev: "g2 \<turnstile> n \<simeq> UnaryExpr UnaryAbs e2'" 
          using l d by (simp add: rep.AbsNode True AbsNode.prems)
        then have r: "UnaryExpr UnaryAbs e1' \<ge> UnaryExpr UnaryAbs e2'"
          by (meson a mono_unary)
        then show ?thesis
          by (metis n ev)
      next
        case False
        have "g1 \<turnstile> xn \<simeq> xe1" 
          by (simp add: m)
        have "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using AbsNode False b encodes_contains l not_excluded_keep_type not_in_g singleton_iff
          by (metis_node_eq_unary AbsNode)
        then have "\<exists> xe2. (g2 \<turnstile> n \<simeq> UnaryExpr UnaryAbs xe2) \<and> 
           UnaryExpr UnaryAbs xe1 \<ge> UnaryExpr UnaryAbs xe2"
          by (metis AbsNode.prems l mono_unary rep.AbsNode)
        then show ?thesis
          by meson
      qed
    next
      case (ReverseBytesNode n x xe1)
      have k: "g1 \<turnstile> n \<simeq> UnaryExpr UnaryReverseBytes xe1"
        by (simp add: ReverseBytesNode.hyps(1,2) rep.ReverseBytesNode)
      obtain xn where l: "kind g1 n = ReverseBytesNode xn"
        by (simp add: ReverseBytesNode.hyps(1))
      then have m: "g1 \<turnstile> xn \<simeq> xe1"
        by (metis IRNode.inject(45) ReverseBytesNode.hyps(1,2))
      then show ?case
      proof (cases "xn = n'")
        case True
        then have n: "xe1 = e1'"
          using m by (simp add: repDet c)
        then have ev: "g2 \<turnstile> n \<simeq> UnaryExpr UnaryReverseBytes e2'"
          using ReverseBytesNode.prems True d l rep.ReverseBytesNode by presburger
        then have r: "UnaryExpr UnaryReverseBytes e1' \<ge> UnaryExpr UnaryReverseBytes e2'"
          by (meson a mono_unary)
        then show ?thesis
          by (metis n ev)
      next
        case False
        have "g1 \<turnstile> xn \<simeq> xe1"
          by (simp add: m)
        have "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          by (metis False IRNode.inject(45) ReverseBytesNode.IH ReverseBytesNode.hyps(1,2) b l
              encodes_contains ids_some not_excluded_keep_type singleton_iff)
        then have "\<exists> xe2. (g2 \<turnstile> n \<simeq> UnaryExpr UnaryReverseBytes xe2) \<and>
  UnaryExpr UnaryReverseBytes xe1 \<ge> UnaryExpr UnaryReverseBytes xe2"
          by (metis ReverseBytesNode.prems l mono_unary rep.ReverseBytesNode)
        then show ?thesis
          by meson
      qed
    next
      case (BitCountNode n x xe1)
      have k: "g1 \<turnstile> n \<simeq> UnaryExpr UnaryBitCount xe1"
        by (simp add: BitCountNode.hyps(1,2) rep.BitCountNode)
      obtain xn where l: "kind g1 n = BitCountNode xn"
        by (simp add: BitCountNode.hyps(1))
      then have m: "g1 \<turnstile> xn \<simeq> xe1"
        by (metis BitCountNode.hyps(1,2) IRNode.inject(6))
      then show ?case
      proof (cases "xn = n'")
        case True
        then have n: "xe1 = e1'"
          using m by (simp add: repDet c)
        then have ev: "g2 \<turnstile> n \<simeq> UnaryExpr UnaryBitCount e2'"
          using BitCountNode.prems True d l rep.BitCountNode by presburger
        then have r: "UnaryExpr UnaryBitCount e1' \<ge> UnaryExpr UnaryBitCount e2'"
          by (meson a mono_unary)
        then show ?thesis
          by (metis n ev)
      next
        case False
        have "g1 \<turnstile> xn \<simeq> xe1"
          by (simp add: m)
        have "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          by (metis BitCountNode.IH BitCountNode.hyps(1) False IRNode.inject(6) b emptyE insertE l m
              no_encoding not_excluded_keep_type)
        then have "\<exists> xe2. (g2 \<turnstile> n \<simeq> UnaryExpr UnaryBitCount xe2) \<and>
      UnaryExpr UnaryBitCount xe1 \<ge> UnaryExpr UnaryBitCount xe2"
          by (metis BitCountNode.prems l mono_unary rep.BitCountNode)
        then show ?thesis
          by meson
      qed
    next
      case (NotNode n x xe1)
      have k: "g1 \<turnstile> n \<simeq> UnaryExpr UnaryNot xe1" 
        using NotNode by (simp add: NotNode.hyps(2) rep.NotNode f)
      obtain xn where l: "kind g1 n = NotNode xn"
        by (auto simp add: NotNode.hyps(1))
      then have m: "g1 \<turnstile> xn \<simeq> xe1"
        using NotNode.hyps(1,2) by simp
      then show ?case
      proof (cases "xn = n'")
        case True
        then have n: "xe1 = e1'" 
          using m by (simp add: repDet c)
        then have ev: "g2 \<turnstile> n \<simeq> UnaryExpr UnaryNot e2'" 
          using l by (simp add: rep.NotNode d True NotNode.prems)
        then have r: "UnaryExpr UnaryNot e1' \<ge> UnaryExpr UnaryNot e2'"
          by (meson a mono_unary)
        then show ?thesis
          by (metis n ev)
      next
        case False
        have "g1 \<turnstile> xn \<simeq> xe1" 
          by (simp add: m)
        have "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using NotNode False b l not_excluded_keep_type singletonD no_encoding
          by (metis_node_eq_unary NotNode)
        then have "\<exists> xe2. (g2 \<turnstile> n \<simeq> UnaryExpr UnaryNot xe2) \<and> 
           UnaryExpr UnaryNot xe1 \<ge> UnaryExpr UnaryNot xe2"
          by (metis NotNode.prems l mono_unary rep.NotNode)
        then show ?thesis
          by meson
      qed
    next
      case (NegateNode n x xe1)
      have k: "g1 \<turnstile> n \<simeq> UnaryExpr UnaryNeg xe1" 
        using NegateNode by (simp add: NegateNode.hyps(2) rep.NegateNode f)
      obtain xn where l: "kind g1 n = NegateNode xn"
        by (auto simp add: NegateNode.hyps(1))
      then have m: "g1 \<turnstile> xn \<simeq> xe1"
        using NegateNode.hyps(1,2) by simp
      then show ?case
      proof (cases "xn = n'")
        case True
        then have n: "xe1 = e1'" 
          using m by (simp add: c repDet)
        then have ev: "g2 \<turnstile> n \<simeq> UnaryExpr UnaryNeg e2'" 
          using l by (simp add: rep.NegateNode True NegateNode.prems d)
        then have r: "UnaryExpr UnaryNeg e1' \<ge> UnaryExpr UnaryNeg e2'"
          by (meson a mono_unary)
        then show ?thesis
          by (metis n ev)
      next
        case False
        have "g1 \<turnstile> xn \<simeq> xe1" 
          by (simp add: m)
        have "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using NegateNode False b l not_excluded_keep_type singletonD no_encoding
          by (metis_node_eq_unary NegateNode)
        then have "\<exists> xe2. (g2 \<turnstile> n \<simeq> UnaryExpr UnaryNeg xe2) \<and> 
           UnaryExpr UnaryNeg xe1 \<ge> UnaryExpr UnaryNeg xe2"
          by (metis NegateNode.prems l mono_unary rep.NegateNode)
        then show ?thesis
          by meson
      qed
    next
      case (LogicNegationNode n x xe1)
      have k: "g1 \<turnstile> n \<simeq> UnaryExpr UnaryLogicNegation xe1" 
        using LogicNegationNode by (simp add: LogicNegationNode.hyps(2) rep.LogicNegationNode)
      obtain xn where l: "kind g1 n = LogicNegationNode xn"
        by (simp add: LogicNegationNode.hyps(1))
      then have m: "g1 \<turnstile> xn \<simeq> xe1"
        using LogicNegationNode.hyps(1,2) by simp
      then show ?case
      proof (cases "xn = n'")
        case True
        then have n: "xe1 = e1'" 
          using m by (simp add: c repDet)
        then have ev: "g2 \<turnstile> n \<simeq> UnaryExpr UnaryLogicNegation e2'" 
          using l by (simp add: rep.LogicNegationNode True LogicNegationNode.prems d
                                LogicNegationNode.hyps(1))
        then have r: "UnaryExpr UnaryLogicNegation e1' \<ge> UnaryExpr UnaryLogicNegation e2'"
          by (meson a mono_unary)
        then show ?thesis
          by (metis n ev)
      next
        case False
        have "g1 \<turnstile> xn \<simeq> xe1" 
          by (simp add: m)
        have "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using LogicNegationNode False b l not_excluded_keep_type singletonD no_encoding
          by (metis_node_eq_unary LogicNegationNode)
        then have "\<exists> xe2. (g2 \<turnstile> n \<simeq> UnaryExpr UnaryLogicNegation xe2) \<and> 
 UnaryExpr UnaryLogicNegation xe1 \<ge> UnaryExpr UnaryLogicNegation xe2"
          by (metis LogicNegationNode.prems l mono_unary rep.LogicNegationNode)
        then show ?thesis
          by meson
      qed
    next
      case (AddNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<simeq> BinaryExpr BinAdd xe1 ye1" 
        using AddNode by (simp add: AddNode.hyps(2) rep.AddNode f)
      obtain xn yn where l: "kind g1 n = AddNode xn yn"
        by (simp add: AddNode.hyps(1))
      then have mx: "g1 \<turnstile> xn \<simeq> xe1"
        using AddNode.hyps(1,2) by simp
      from l have my: "g1 \<turnstile> yn \<simeq> ye1"
        using AddNode.hyps(1,3) by simp
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<simeq> xe1" 
          by (simp add: mx)
        have "g1 \<turnstile> yn \<simeq> ye1" 
          by (simp add: my)
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using AddNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary AddNode)
        have "\<exists> ye2. (g2 \<turnstile> yn \<simeq> ye2) \<and> ye1 \<ge> ye2"
          using AddNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary AddNode)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<simeq> BinaryExpr BinAdd xe2 ye2) \<and> 
            BinaryExpr BinAdd xe1 ye1 \<ge> BinaryExpr BinAdd xe2 ye2"
          by (metis AddNode.prems l mono_binary rep.AddNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (MulNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<simeq> BinaryExpr BinMul xe1 ye1" 
        using MulNode by (simp add: MulNode.hyps(2) rep.MulNode f)
      obtain xn yn where l: "kind g1 n = MulNode xn yn"
        by (simp add: MulNode.hyps(1))
      then have mx: "g1 \<turnstile> xn \<simeq> xe1"
        using MulNode.hyps(1,2) by simp
      from l have my: "g1 \<turnstile> yn \<simeq> ye1"
        using MulNode.hyps(1,3) by simp
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<simeq> xe1" 
          by (simp add: mx)
        have "g1 \<turnstile> yn \<simeq> ye1" 
          by (simp add: my)
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using MulNode  a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary MulNode)
        have "\<exists> ye2. (g2 \<turnstile> yn \<simeq> ye2) \<and> ye1 \<ge> ye2"
          using MulNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary MulNode)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<simeq> BinaryExpr BinMul xe2 ye2) \<and> 
            BinaryExpr BinMul xe1 ye1 \<ge> BinaryExpr BinMul xe2 ye2"
          by (metis MulNode.prems l mono_binary rep.MulNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (SubNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<simeq> BinaryExpr BinSub xe1 ye1" 
        using SubNode by (simp add: SubNode.hyps(2) rep.SubNode f)
      obtain xn yn where l: "kind g1 n = SubNode xn yn"
        by (simp add: SubNode.hyps(1))
      then have mx: "g1 \<turnstile> xn \<simeq> xe1"
        using SubNode.hyps(1,2) by simp
      from l have my: "g1 \<turnstile> yn \<simeq> ye1"
        using SubNode.hyps(1,3) by simp
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<simeq> xe1" 
          by (simp add: mx)
        have "g1 \<turnstile> yn \<simeq> ye1" 
          by (simp add: my)
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using SubNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary SubNode)
        have "\<exists> ye2. (g2 \<turnstile> yn \<simeq> ye2) \<and> ye1 \<ge> ye2"
          using SubNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary SubNode)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<simeq> BinaryExpr BinSub xe2 ye2) \<and> 
            BinaryExpr BinSub xe1 ye1 \<ge> BinaryExpr BinSub xe2 ye2"
          by (metis SubNode.prems l mono_binary rep.SubNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (AndNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<simeq> BinaryExpr BinAnd xe1 ye1" 
        using AndNode by (simp add: AndNode.hyps(2) rep.AndNode f)
      obtain xn yn where l: "kind g1 n = AndNode xn yn"
        using AndNode.hyps(1) by simp
      then have mx: "g1 \<turnstile> xn \<simeq> xe1"
        using AndNode.hyps(1,2) by simp
      from l have my: "g1 \<turnstile> yn \<simeq> ye1"
        using AndNode.hyps(1,3) by simp
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<simeq> xe1" 
          by (simp add: mx)
        have "g1 \<turnstile> yn \<simeq> ye1" 
          by (simp add: my)
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using AndNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary AndNode)
        have "\<exists> ye2. (g2 \<turnstile> yn \<simeq> ye2) \<and> ye1 \<ge> ye2"
          using AndNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary AndNode)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<simeq> BinaryExpr BinAnd xe2 ye2) \<and> 
            BinaryExpr BinAnd xe1 ye1 \<ge> BinaryExpr BinAnd xe2 ye2"
          by (metis AndNode.prems l mono_binary rep.AndNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (OrNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<simeq> BinaryExpr BinOr xe1 ye1" 
        using OrNode by (simp add: OrNode.hyps(2) rep.OrNode f)
      obtain xn yn where l: "kind g1 n = OrNode xn yn"
        using OrNode.hyps(1) by simp
      then have mx: "g1 \<turnstile> xn \<simeq> xe1"
        using OrNode.hyps(1,2) by simp
      from l have my: "g1 \<turnstile> yn \<simeq> ye1"
        using OrNode.hyps(1,3) by simp
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<simeq> xe1" 
          by (simp add: mx)
        have "g1 \<turnstile> yn \<simeq> ye1" 
          by (simp add: my)
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using OrNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary OrNode)
        have "\<exists> ye2. (g2 \<turnstile> yn \<simeq> ye2) \<and> ye1 \<ge> ye2"
          using OrNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary OrNode)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<simeq> BinaryExpr BinOr xe2 ye2) \<and> 
             BinaryExpr BinOr xe1 ye1 \<ge> BinaryExpr BinOr xe2 ye2"
          by (metis OrNode.prems l mono_binary rep.OrNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (XorNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<simeq> BinaryExpr BinXor xe1 ye1" 
        using XorNode by (simp add: XorNode.hyps(2) rep.XorNode f)
      obtain xn yn where l: "kind g1 n = XorNode xn yn"
        using XorNode.hyps(1) by simp
      then have mx: "g1 \<turnstile> xn \<simeq> xe1"
        using XorNode.hyps(1,2) by simp
      from l have my: "g1 \<turnstile> yn \<simeq> ye1"
        using XorNode.hyps(1,3) by simp
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<simeq> xe1" 
          by (simp add: mx)
        have "g1 \<turnstile> yn \<simeq> ye1" 
          by (simp add: my)
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using XorNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary XorNode)
        have "\<exists> ye2. (g2 \<turnstile> yn \<simeq> ye2) \<and> ye1 \<ge> ye2"
          using XorNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary XorNode)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<simeq> BinaryExpr BinXor xe2 ye2) \<and> 
            BinaryExpr BinXor xe1 ye1 \<ge> BinaryExpr BinXor xe2 ye2"
          by (metis XorNode.prems l mono_binary rep.XorNode xer)
        then show ?thesis
          by meson
      qed
    next
    case (ShortCircuitOrNode n x y xe1 ye1)
    have k: "g1 \<turnstile> n \<simeq> BinaryExpr BinShortCircuitOr xe1 ye1" 
      using ShortCircuitOrNode by (simp add: ShortCircuitOrNode.hyps(2) rep.ShortCircuitOrNode f)
      obtain xn yn where l: "kind g1 n = ShortCircuitOrNode xn yn"
        using ShortCircuitOrNode.hyps(1) by simp
      then have mx: "g1 \<turnstile> xn \<simeq> xe1"
        using ShortCircuitOrNode.hyps(1,2) by simp
      from l have my: "g1 \<turnstile> yn \<simeq> ye1"
        using ShortCircuitOrNode.hyps(1,3) by simp
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<simeq> xe1" 
          by (simp add: mx)
        have "g1 \<turnstile> yn \<simeq> ye1" 
          by (simp add: my)
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using ShortCircuitOrNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary ShortCircuitOrNode)
        have "\<exists> ye2. (g2 \<turnstile> yn \<simeq> ye2) \<and> ye1 \<ge> ye2"
          using ShortCircuitOrNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary ShortCircuitOrNode)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<simeq> BinaryExpr BinShortCircuitOr xe2 ye2) \<and> 
 BinaryExpr BinShortCircuitOr xe1 ye1 \<ge> BinaryExpr BinShortCircuitOr xe2 ye2"
          by (metis ShortCircuitOrNode.prems l mono_binary rep.ShortCircuitOrNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (LeftShiftNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<simeq> BinaryExpr BinLeftShift xe1 ye1" 
        using LeftShiftNode by (simp add: LeftShiftNode.hyps(2) rep.LeftShiftNode f)
      obtain xn yn where l: "kind g1 n = LeftShiftNode xn yn"
        using LeftShiftNode.hyps(1) by simp
      then have mx: "g1 \<turnstile> xn \<simeq> xe1"
        using LeftShiftNode.hyps(1,2) by simp
      from l have my: "g1 \<turnstile> yn \<simeq> ye1"
        using LeftShiftNode.hyps(1,3) by simp
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<simeq> xe1" 
          by (simp add: mx)
        have "g1 \<turnstile> yn \<simeq> ye1" 
          by (simp add: my)
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using LeftShiftNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary LeftShiftNode)
        have "\<exists> ye2. (g2 \<turnstile> yn \<simeq> ye2) \<and> ye1 \<ge> ye2"
          using LeftShiftNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary LeftShiftNode)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<simeq> BinaryExpr BinLeftShift xe2 ye2) \<and> 
      BinaryExpr BinLeftShift xe1 ye1 \<ge> BinaryExpr BinLeftShift xe2 ye2"
          by (metis LeftShiftNode.prems l mono_binary rep.LeftShiftNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (RightShiftNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<simeq> BinaryExpr BinRightShift xe1 ye1" 
        using RightShiftNode by (simp add: RightShiftNode.hyps(2) rep.RightShiftNode)
      obtain xn yn where l: "kind g1 n = RightShiftNode xn yn"
        using RightShiftNode.hyps(1) by simp
      then have mx: "g1 \<turnstile> xn \<simeq> xe1"
        using RightShiftNode.hyps(1,2) by simp
      from l have my: "g1 \<turnstile> yn \<simeq> ye1"
        using RightShiftNode.hyps(1,3) by simp
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<simeq> xe1" 
          by (simp add: mx)
        have "g1 \<turnstile> yn \<simeq> ye1" 
          by (simp add: my)
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using RightShiftNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary RightShiftNode)
        have "\<exists> ye2. (g2 \<turnstile> yn \<simeq> ye2) \<and> ye1 \<ge> ye2"
          using RightShiftNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary RightShiftNode)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<simeq> BinaryExpr BinRightShift xe2 ye2) \<and> 
     BinaryExpr BinRightShift xe1 ye1 \<ge> BinaryExpr BinRightShift xe2 ye2"
          by (metis RightShiftNode.prems l mono_binary rep.RightShiftNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (UnsignedRightShiftNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<simeq> BinaryExpr BinURightShift xe1 ye1" 
        using UnsignedRightShiftNode by (simp add: UnsignedRightShiftNode.hyps(2) 
                                                   rep.UnsignedRightShiftNode)
      obtain xn yn where l: "kind g1 n = UnsignedRightShiftNode xn yn"
        using UnsignedRightShiftNode.hyps(1) by simp
      then have mx: "g1 \<turnstile> xn \<simeq> xe1"
        using UnsignedRightShiftNode.hyps(1,2) by simp
      from l have my: "g1 \<turnstile> yn \<simeq> ye1"
        using UnsignedRightShiftNode.hyps(1,3) by simp
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<simeq> xe1" 
          by (simp add: mx)
        have "g1 \<turnstile> yn \<simeq> ye1" 
          by (simp add: my)
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using UnsignedRightShiftNode a b c d no_encoding not_excluded_keep_type repDet singletonD 
                l
          by (metis_node_eq_binary UnsignedRightShiftNode)
        have "\<exists> ye2. (g2 \<turnstile> yn \<simeq> ye2) \<and> ye1 \<ge> ye2"
          using UnsignedRightShiftNode a b c d no_encoding not_excluded_keep_type repDet singletonD 
                l
          by (metis_node_eq_binary UnsignedRightShiftNode)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<simeq> BinaryExpr BinURightShift xe2 ye2) \<and> 
    BinaryExpr BinURightShift xe1 ye1 \<ge> BinaryExpr BinURightShift xe2 ye2"
          by (metis UnsignedRightShiftNode.prems l mono_binary rep.UnsignedRightShiftNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (IntegerBelowNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<simeq> BinaryExpr BinIntegerBelow xe1 ye1" 
        using IntegerBelowNode by (simp add: IntegerBelowNode.hyps(2) rep.IntegerBelowNode)
      obtain xn yn where l: "kind g1 n = IntegerBelowNode xn yn"
        using IntegerBelowNode.hyps(1) by simp
      then have mx: "g1 \<turnstile> xn \<simeq> xe1"
        using IntegerBelowNode.hyps(1,2) by simp
      from l have my: "g1 \<turnstile> yn \<simeq> ye1"
        using IntegerBelowNode.hyps(1,3) by simp
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<simeq> xe1" 
          by (simp add: mx)
        have "g1 \<turnstile> yn \<simeq> ye1" 
          by (simp add: my)
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using IntegerBelowNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary IntegerBelowNode)
        have "\<exists> ye2. (g2 \<turnstile> yn \<simeq> ye2) \<and> ye1 \<ge> ye2"
          using IntegerBelowNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary IntegerBelowNode)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<simeq> BinaryExpr BinIntegerBelow xe2 ye2) \<and> 
   BinaryExpr BinIntegerBelow xe1 ye1 \<ge> BinaryExpr BinIntegerBelow xe2 ye2"
          by (metis IntegerBelowNode.prems l mono_binary rep.IntegerBelowNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (IntegerEqualsNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<simeq> BinaryExpr BinIntegerEquals xe1 ye1" 
        using IntegerEqualsNode by (simp add: IntegerEqualsNode.hyps(2) rep.IntegerEqualsNode)
      obtain xn yn where l: "kind g1 n = IntegerEqualsNode xn yn"
        using IntegerEqualsNode.hyps(1) by simp
      then have mx: "g1 \<turnstile> xn \<simeq> xe1"
        using IntegerEqualsNode.hyps(1,2) by simp
      from l have my: "g1 \<turnstile> yn \<simeq> ye1"
        using IntegerEqualsNode.hyps(1,3) by simp
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<simeq> xe1" 
          by (simp add: mx)
        have "g1 \<turnstile> yn \<simeq> ye1" 
          by (simp add: my)
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using IntegerEqualsNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary IntegerEqualsNode)
        have "\<exists> ye2. (g2 \<turnstile> yn \<simeq> ye2) \<and> ye1 \<ge> ye2"
          using IntegerEqualsNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary IntegerEqualsNode)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<simeq> BinaryExpr BinIntegerEquals xe2 ye2) \<and> 
  BinaryExpr BinIntegerEquals xe1 ye1 \<ge> BinaryExpr BinIntegerEquals xe2 ye2"
          by (metis IntegerEqualsNode.prems l mono_binary rep.IntegerEqualsNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (IntegerLessThanNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<simeq> BinaryExpr BinIntegerLessThan xe1 ye1" 
        using IntegerLessThanNode by (simp add: IntegerLessThanNode.hyps(2) rep.IntegerLessThanNode)
      obtain xn yn where l: "kind g1 n = IntegerLessThanNode xn yn"
        using IntegerLessThanNode.hyps(1) by simp
      then have mx: "g1 \<turnstile> xn \<simeq> xe1"
        using IntegerLessThanNode.hyps(1,2) by simp
      from l have my: "g1 \<turnstile> yn \<simeq> ye1"
        using IntegerLessThanNode.hyps(1,3) by simp
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<simeq> xe1" 
          by (simp add: mx)
        have "g1 \<turnstile> yn \<simeq> ye1" 
          by (simp add: my)
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using IntegerLessThanNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary IntegerLessThanNode)
        have "\<exists> ye2. (g2 \<turnstile> yn \<simeq> ye2) \<and> ye1 \<ge> ye2"
          using IntegerLessThanNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis_node_eq_binary IntegerLessThanNode)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<simeq> BinaryExpr BinIntegerLessThan xe2 ye2) \<and> 
BinaryExpr BinIntegerLessThan xe1 ye1 \<ge> BinaryExpr BinIntegerLessThan xe2 ye2"
          by (metis IntegerLessThanNode.prems l mono_binary rep.IntegerLessThanNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (IntegerTestNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<simeq> BinaryExpr BinIntegerTest xe1 ye1" 
        using IntegerTestNode by (meson rep.IntegerTestNode) 
      obtain xn yn where l: "kind g1 n = IntegerTestNode xn yn"
        by (simp add: IntegerTestNode.hyps(1))
      then have mx: "g1 \<turnstile> xn \<simeq> xe1"
        using IRNode.inject(21) IntegerTestNode.hyps(1,2) by presburger
      from l have my: "g1 \<turnstile> yn \<simeq> ye1"
        by (metis IRNode.inject(21) IntegerTestNode.hyps(1,3))
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<simeq> xe1"
          by (simp add: mx)
        have "g1 \<turnstile> yn \<simeq> ye1"
          by (simp add: my)
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using IntegerTestNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis IRNode.inject(21))
        have "\<exists> ye2. (g2 \<turnstile> yn \<simeq> ye2) \<and> ye1 \<ge> ye2"
          using IntegerLessThanNode a b c d l no_encoding not_excluded_keep_type repDet singletonD
          by (metis IRNode.inject(21) IntegerTestNode.IH(2) IntegerTestNode.hyps(1) my)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<simeq> BinaryExpr BinIntegerTest xe2 ye2) \<and> 
    BinaryExpr BinIntegerTest xe1 ye1 \<ge> BinaryExpr BinIntegerTest xe2 ye2"
          by (metis IntegerTestNode.prems l mono_binary xer rep.IntegerTestNode)
        then show ?thesis
          by meson
      qed
    next
      case (IntegerNormalizeCompareNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<simeq> BinaryExpr BinIntegerNormalizeCompare xe1 ye1"
        by (simp add: IntegerNormalizeCompareNode.hyps(1,2,3) rep.IntegerNormalizeCompareNode)
      obtain xn yn where l: "kind g1 n = IntegerNormalizeCompareNode xn yn"
        by (simp add: IntegerNormalizeCompareNode.hyps(1))
      then have mx: "g1 \<turnstile> xn \<simeq> xe1"
        using IRNode.inject(20) IntegerNormalizeCompareNode.hyps(1,2) by presburger
      from l have my: "g1 \<turnstile> yn \<simeq> ye1"
        using IRNode.inject(20) IntegerNormalizeCompareNode.hyps(1,3) by presburger
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<simeq> xe1"
          by (simp add: mx)
        have "g1 \<turnstile> yn \<simeq> ye1"
          by (simp add: my)
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          by (metis IRNode.inject(20) IntegerNormalizeCompareNode.IH(1) l mx no_encoding a b c d
              IntegerNormalizeCompareNode.hyps(1) emptyE insertE not_excluded_keep_type repDet)
        have "\<exists> ye2. (g2 \<turnstile> yn \<simeq> ye2) \<and> ye1 \<ge> ye2"
          by (metis IRNode.inject(20) IntegerNormalizeCompareNode.IH(2) my no_encoding a b c d l
              IntegerNormalizeCompareNode.hyps(1) emptyE insertE not_excluded_keep_type repDet)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<simeq> BinaryExpr BinIntegerNormalizeCompare xe2 ye2) \<and>
    BinaryExpr BinIntegerNormalizeCompare xe1 ye1 \<ge> BinaryExpr BinIntegerNormalizeCompare xe2 ye2"
          by (metis IntegerNormalizeCompareNode.prems l mono_binary rep.IntegerNormalizeCompareNode
              xer)
        then show ?thesis
          by meson
      qed
    next
      case (IntegerMulHighNode n x y xe1 ye1)
      have k: "g1 \<turnstile> n \<simeq> BinaryExpr BinIntegerMulHigh xe1 ye1"
        by (simp add: IntegerMulHighNode.hyps(1,2,3) rep.IntegerMulHighNode)
      obtain xn yn where l: "kind g1 n = IntegerMulHighNode xn yn"
        by (simp add: IntegerMulHighNode.hyps(1))
      then have mx: "g1 \<turnstile> xn \<simeq> xe1"
        using IRNode.inject(19) IntegerMulHighNode.hyps(1,2) by presburger
      from l have my: "g1 \<turnstile> yn \<simeq> ye1"
        using IRNode.inject(19) IntegerMulHighNode.hyps(1,3) by presburger
      then show ?case
      proof -
        have "g1 \<turnstile> xn \<simeq> xe1"
          by (simp add: mx)
        have "g1 \<turnstile> yn \<simeq> ye1"
          by (simp add: my)
        have xer: "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          by (metis IRNode.inject(19) IntegerMulHighNode.IH(1) IntegerMulHighNode.hyps(1) a b c d
              emptyE insertE l mx no_encoding not_excluded_keep_type repDet)
        have "\<exists> ye2. (g2 \<turnstile> yn \<simeq> ye2) \<and> ye1 \<ge> ye2"
          by (metis IRNode.inject(19) IntegerMulHighNode.IH(2) IntegerMulHighNode.hyps(1) a b c d
              emptyE insertE l my no_encoding not_excluded_keep_type repDet)
        then have "\<exists> xe2 ye2. (g2 \<turnstile> n \<simeq> BinaryExpr BinIntegerMulHigh xe2 ye2) \<and>
 BinaryExpr BinIntegerMulHigh xe1 ye1 \<ge> BinaryExpr BinIntegerMulHigh xe2 ye2"
          by (metis IntegerMulHighNode.prems l mono_binary rep.IntegerMulHighNode xer)
        then show ?thesis
          by meson
      qed
    next
      case (NarrowNode n inputBits resultBits x xe1)
      have k: "g1 \<turnstile> n \<simeq> UnaryExpr (UnaryNarrow inputBits resultBits) xe1" 
        using NarrowNode by (simp add: NarrowNode.hyps(2) rep.NarrowNode)
      obtain xn where l: "kind g1 n = NarrowNode inputBits resultBits xn"
        using NarrowNode.hyps(1) by simp
      then have m: "g1 \<turnstile> xn \<simeq> xe1"
        using NarrowNode.hyps(1,2) by simp
      then show ?case
      proof (cases "xn = n'")
        case True
        then have n: "xe1 = e1'" 
          using m by (simp add: repDet c)
        then have ev: "g2 \<turnstile> n \<simeq> UnaryExpr (UnaryNarrow inputBits resultBits) e2'" 
          using l by (simp add: rep.NarrowNode d True NarrowNode.prems)
        then have r: "UnaryExpr (UnaryNarrow inputBits resultBits) e1' \<ge> 
                      UnaryExpr (UnaryNarrow inputBits resultBits) e2'"
          by (meson a mono_unary)
        then show ?thesis
          by (metis n ev)
      next
        case False
        have "g1 \<turnstile> xn \<simeq> xe1" 
          by (simp add: m)
        have "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using NarrowNode False b encodes_contains l not_excluded_keep_type not_in_g singleton_iff
          by (metis_node_eq_ternary NarrowNode)
        then have "\<exists> xe2. (g2 \<turnstile> n \<simeq> UnaryExpr (UnaryNarrow inputBits resultBits) xe2) \<and> 
                                    UnaryExpr (UnaryNarrow inputBits resultBits) xe1 \<ge> 
                                    UnaryExpr (UnaryNarrow inputBits resultBits) xe2"
          by (metis NarrowNode.prems l mono_unary rep.NarrowNode)
        then show ?thesis
          by meson
      qed
    next
      case (SignExtendNode n inputBits resultBits x xe1)
      have k: "g1 \<turnstile> n \<simeq> UnaryExpr (UnarySignExtend inputBits resultBits) xe1" 
        using SignExtendNode by (simp add: SignExtendNode.hyps(2) rep.SignExtendNode)
      obtain xn where l: "kind g1 n = SignExtendNode inputBits resultBits xn"
        using SignExtendNode.hyps(1) by simp
      then have m: "g1 \<turnstile> xn \<simeq> xe1"
        using SignExtendNode.hyps(1,2) by simp
      then show ?case
      proof (cases "xn = n'")
        case True
        then have n: "xe1 = e1'" 
          using m by (simp add: repDet c)
        then have ev: "g2 \<turnstile> n \<simeq> UnaryExpr (UnarySignExtend inputBits resultBits) e2'" 
          using l by (simp add: True d rep.SignExtendNode SignExtendNode.prems)
        then have r: "UnaryExpr (UnarySignExtend inputBits resultBits) e1' \<ge> 
                      UnaryExpr (UnarySignExtend inputBits resultBits) e2'"
          by (meson a mono_unary)
        then show ?thesis
          by (metis n ev)
      next
        case False
        have "g1 \<turnstile> xn \<simeq> xe1" 
          by (simp add: m)
        have "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using SignExtendNode False b encodes_contains l not_excluded_keep_type not_in_g 
                singleton_iff
          by (metis_node_eq_ternary SignExtendNode)
        then have "\<exists> xe2. (g2 \<turnstile> n \<simeq> UnaryExpr (UnarySignExtend inputBits resultBits) xe2) \<and> 
                                    UnaryExpr (UnarySignExtend inputBits resultBits) xe1 \<ge> 
                                    UnaryExpr (UnarySignExtend inputBits resultBits) xe2"
          by (metis SignExtendNode.prems l mono_unary rep.SignExtendNode)
        then show ?thesis
          by meson
      qed
    next
      case (ZeroExtendNode n inputBits resultBits x xe1)
      have k: "g1 \<turnstile> n \<simeq> UnaryExpr (UnaryZeroExtend inputBits resultBits) xe1" 
        using ZeroExtendNode by (simp add: ZeroExtendNode.hyps(2) rep.ZeroExtendNode)
      obtain xn where l: "kind g1 n = ZeroExtendNode inputBits resultBits xn"
        using ZeroExtendNode.hyps(1) by simp
      then have m: "g1 \<turnstile> xn \<simeq> xe1"
        using ZeroExtendNode.hyps(1,2) by simp
      then show ?case
      proof (cases "xn = n'")
        case True
        then have n: "xe1 = e1'" 
          using m by (simp add: repDet c)
        then have ev: "g2 \<turnstile> n \<simeq> UnaryExpr (UnaryZeroExtend inputBits resultBits) e2'" 
          using l by (simp add: ZeroExtendNode.prems True d rep.ZeroExtendNode)
        then have r: "UnaryExpr (UnaryZeroExtend inputBits resultBits) e1' \<ge> 
                      UnaryExpr (UnaryZeroExtend inputBits resultBits) e2'"
          by (meson a mono_unary)
        then show ?thesis
          by (metis n ev)
      next
        case False
        have "g1 \<turnstile> xn \<simeq> xe1" 
          by (simp add: m)
        have "\<exists> xe2. (g2 \<turnstile> xn \<simeq> xe2) \<and> xe1 \<ge> xe2"
          using ZeroExtendNode b encodes_contains l not_excluded_keep_type not_in_g singleton_iff 
                False
          by (metis_node_eq_ternary ZeroExtendNode)
        then have "\<exists> xe2. (g2 \<turnstile> n \<simeq> UnaryExpr (UnaryZeroExtend inputBits resultBits) xe2) \<and> 
                                    UnaryExpr (UnaryZeroExtend inputBits resultBits) xe1 \<ge> 
                                    UnaryExpr (UnaryZeroExtend inputBits resultBits) xe2"
          by (metis ZeroExtendNode.prems l mono_unary rep.ZeroExtendNode)
        then show ?thesis
          by meson
      qed
    next
      case (LeafNode n s)
      then show ?case
        by (metis eq_refl rep.LeafNode)
    next
      case (PiNode n' gu)
      then show ?case
        by (metis encodes_contains not_excluded_keep_type not_in_g rep.PiNode repDet singleton_iff
            a b c d)
    next
      case (RefNode n')
      then show ?case
        by (metis a b c d no_encoding not_excluded_keep_type rep.RefNode repDet singletonD)
    next
      case (IsNullNode n)
      then show ?case
        by (metis insertE mono_unary no_encoding not_excluded_keep_type rep.IsNullNode repDet emptyE 
            a b c d) 
    qed
  qed
qed

lemma graph_semantics_preservation_subscript:
  assumes a: "e\<^sub>1' \<ge> e\<^sub>2'"
  assumes b: "({n} \<unlhd> as_set g\<^sub>1) \<subseteq> as_set g\<^sub>2"
  assumes c: "g\<^sub>1 \<turnstile> n \<simeq> e\<^sub>1'"
  assumes d: "g\<^sub>2 \<turnstile> n \<simeq> e\<^sub>2'"
  shows "graph_refinement g\<^sub>1 g\<^sub>2"
  using assms by (simp add: graph_semantics_preservation)

lemma tree_to_graph_rewriting:
  "e\<^sub>1 \<ge> e\<^sub>2 
  \<and> (g\<^sub>1 \<turnstile> n \<simeq> e\<^sub>1) \<and> maximal_sharing g\<^sub>1
  \<and> ({n} \<unlhd> as_set g\<^sub>1) \<subseteq> as_set g\<^sub>2 
  \<and> (g\<^sub>2 \<turnstile> n \<simeq> e\<^sub>2) \<and> maximal_sharing g\<^sub>2
  \<Longrightarrow> graph_refinement g\<^sub>1 g\<^sub>2"
  by (auto simp add: graph_semantics_preservation)

declare [[simp_trace]]
lemma equal_refines:
  fixes e1 e2 :: IRExpr
  assumes "e1 = e2"
  shows "e1 \<ge> e2"
  using assms by simp
declare [[simp_trace=false]]

inductive_cases UnaryRepE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (UnaryExpr op xe)"
inductive_cases BinaryRepE[elim!]:\<^marker>\<open>tag invisible\<close>
  "g \<turnstile> n \<simeq> (BinaryExpr op xe ye)"

lemma eval_contains_id[simp]: "g1 \<turnstile> n \<simeq> e \<Longrightarrow> n \<in> ids g1"
  using no_encoding by auto

lemma subset_kind[simp]: "as_set g1 \<subseteq> as_set g2 \<Longrightarrow> g1 \<turnstile> n \<simeq> e \<Longrightarrow> kind g1 n = kind g2 n"
  using eval_contains_id as_set_def by blast

lemma subset_stamp[simp]: "as_set g1 \<subseteq> as_set g2 \<Longrightarrow> g1 \<turnstile> n \<simeq> e \<Longrightarrow> stamp g1 n = stamp g2 n"
  using eval_contains_id as_set_def by blast

method solve_subset_eval uses as_set eval =
  (metis eval as_set subset_kind subset_stamp |
   metis eval as_set subset_kind)

(*
lemmas rep_rules =
  ConstantNode
  ParameterNode
  ConditionalNode

method solve_subset_eval uses as_set =
  (match premises in "kind _ _ = node _ \<Longrightarrow> _" for node \<Rightarrow>
    \<open>match rep_rules in eval: "kind _ _ = node _ \<Longrightarrow> _" \<Rightarrow> 
       \<open>metis eval as_set subset_kind\<close>\<close>)

method solve_subset_debug uses as_set =
  (match premises in k: "kind _ _ = node _ _" for node \<Rightarrow>
    \<open>match rep_rules in eval: "kind _ _ = node _ _ \<Longrightarrow> _" \<Rightarrow> 
       \<open>print_term node\<close>\<close>)
*)

lemma subset_implies_evals:
  assumes "as_set g1 \<subseteq> as_set g2"
  assumes "(g1 \<turnstile> n \<simeq> e)"
  shows "(g2 \<turnstile> n \<simeq> e)"
  using assms(2)
  apply (induction e)
                          apply (solve_subset_eval as_set: assms(1) eval: ConstantNode)
                         apply (solve_subset_eval as_set: assms(1) eval: ParameterNode)
                        apply (solve_subset_eval as_set: assms(1) eval: ConditionalNode)
                       apply (solve_subset_eval as_set: assms(1) eval: AbsNode)
                      apply (solve_subset_eval as_set: assms(1) eval: ReverseBytesNode)
                     apply (solve_subset_eval as_set: assms(1) eval: BitCountNode)
                      apply (solve_subset_eval as_set: assms(1) eval: NotNode)
                     apply (solve_subset_eval as_set: assms(1) eval: NegateNode)
                    apply (solve_subset_eval as_set: assms(1) eval: LogicNegationNode)
                   apply (solve_subset_eval as_set: assms(1) eval: AddNode)
                  apply (solve_subset_eval as_set: assms(1) eval: MulNode)
                 apply (solve_subset_eval as_set: assms(1) eval: SubNode)
                apply (solve_subset_eval as_set: assms(1) eval: AndNode)
               apply (solve_subset_eval as_set: assms(1) eval: OrNode)
              apply (solve_subset_eval as_set: assms(1) eval: XorNode)
             apply (solve_subset_eval as_set: assms(1) eval: ShortCircuitOrNode)
            apply (solve_subset_eval as_set: assms(1) eval: LeftShiftNode)
           apply (solve_subset_eval as_set: assms(1) eval: RightShiftNode)
          apply (solve_subset_eval as_set: assms(1) eval: UnsignedRightShiftNode)
         apply (solve_subset_eval as_set: assms(1) eval: IntegerBelowNode)
        apply (solve_subset_eval as_set: assms(1) eval: IntegerEqualsNode)
       apply (solve_subset_eval as_set: assms(1) eval: IntegerLessThanNode)
       apply (solve_subset_eval as_set: assms(1) eval: IntegerTestNode)
      apply (solve_subset_eval as_set: assms(1) eval: IntegerNormalizeCompareNode)
      apply (solve_subset_eval as_set: assms(1) eval: IntegerMulHighNode)
      apply (solve_subset_eval as_set: assms(1) eval: NarrowNode)
     apply (solve_subset_eval as_set: assms(1) eval: SignExtendNode)
    apply (solve_subset_eval as_set: assms(1) eval: ZeroExtendNode)
   apply (solve_subset_eval as_set: assms(1) eval: LeafNode)
      apply (solve_subset_eval as_set: assms(1) eval: PiNode)
  apply (solve_subset_eval as_set: assms(1) eval: RefNode)
  by (solve_subset_eval as_set: assms(1) eval: IsNullNode)

lemma subset_refines:
  assumes "as_set g1 \<subseteq> as_set g2"
  shows "graph_refinement g1 g2"
proof -
  have "ids g1 \<subseteq> ids g2" 
    using assms as_set_def by blast
  then show ?thesis 
    unfolding graph_refinement_def 
    apply rule apply (rule allI) apply (rule impI) apply (rule allI) apply (rule impI)
    unfolding graph_represents_expression_def
    proof -
      fix n e1
      assume 1:"n \<in> ids g1"
      assume 2:"g1 \<turnstile> n \<simeq> e1"
      show "\<exists>e2. (g2 \<turnstile> n \<simeq> e2) \<and> e1 \<ge> e2"
        by (meson equal_refines subset_implies_evals assms 1 2)
    qed
  qed

lemma graph_construction:
  "e\<^sub>1 \<ge> e\<^sub>2
  \<and> as_set g\<^sub>1 \<subseteq> as_set g\<^sub>2
  \<and> (g\<^sub>2 \<turnstile> n \<simeq> e\<^sub>2)
  \<Longrightarrow> (g\<^sub>2 \<turnstile> n \<unlhd> e\<^sub>1) \<and> graph_refinement g\<^sub>1 g\<^sub>2"
  by (meson encodeeval_def graph_represents_expression_def le_expr_def subset_refines)

subsubsection \<open>Term Graph Reconstruction\<close>

lemma find_exists_kind:
  assumes "find_node_and_stamp g (node, s) = Some nid"
  shows "kind g nid = node"
  by (metis (mono_tags, lifting) find_Some_iff find_node_and_stamp.simps assms)

lemma find_exists_stamp:
  assumes "find_node_and_stamp g (node, s) = Some nid"
  shows "stamp g nid = s"
  by (metis (mono_tags, lifting) find_Some_iff find_node_and_stamp.simps assms)

lemma find_new_kind:
  assumes "g' = add_node nid (node, s) g"
  assumes "node \<noteq> NoNode"
  shows "kind g' nid = node"
  by (simp add: add_node_lookup assms)

lemma find_new_stamp:
  assumes "g' = add_node nid (node, s) g"
  assumes "node \<noteq> NoNode"
  shows "stamp g' nid = s"
  by (simp add: assms add_node_lookup)

lemma sorted_bottom:
  assumes "finite xs"
  assumes "x \<in> xs"
  shows "x \<le> last(sorted_list_of_set(xs::nat set))"
  proof -
  obtain largest where largest: "largest = last (sorted_list_of_set(xs))"
    by simp
  obtain sortedList where sortedList: "sortedList = sorted_list_of_set(xs)"
    by simp
  have step: "\<forall>i. 0 < i \<and> i < (length (sortedList)) \<longrightarrow> sortedList!(i-1) \<le> sortedList!(i)"
    unfolding sortedList apply auto
    by (metis diff_le_self sorted_list_of_set.length_sorted_key_list_of_set sorted_nth_mono
        sorted_list_of_set(2))
  have finalElement: "last (sorted_list_of_set(xs)) =
                                       sorted_list_of_set(xs)!(length (sorted_list_of_set(xs)) - 1)"
    using assms last_conv_nth sorted_list_of_set.sorted_key_list_of_set_eq_Nil_iff by blast
  have contains0: "(x \<in> xs) = (x \<in> set (sorted_list_of_set(xs)))"
    using assms(1) by auto
  have lastLargest: "((x \<in> xs) \<longrightarrow> (largest \<ge> x))"
    using step unfolding largest finalElement apply auto
    by (metis (no_types, lifting) One_nat_def Suc_pred assms(1) card_Diff1_less in_set_conv_nth
        sorted_list_of_set.length_sorted_key_list_of_set card_Diff_singleton_if less_Suc_eq_le
        sorted_list_of_set.sorted_sorted_key_list_of_set length_pos_if_in_set sorted_nth_mono
        contains0)
  then show ?thesis
    by (simp add: assms largest)
qed

lemma fresh: "finite xs \<Longrightarrow> last(sorted_list_of_set(xs::nat set)) + 1 \<notin> xs"
  using sorted_bottom not_le by auto

lemma fresh_ids:
  assumes "n = get_fresh_id g"
  shows "n \<notin> ids g"
proof -
  have "finite (ids g)" 
    by (simp add: Rep_IRGraph)
  then show ?thesis
    using assms fresh unfolding get_fresh_id.simps by blast
qed

lemma graph_unchanged_rep_unchanged:
  assumes "\<forall>n \<in> ids g. kind g n = kind g' n"
  assumes "\<forall>n \<in> ids g. stamp g n = stamp g' n"
  shows "(g \<turnstile> n \<simeq> e) \<longrightarrow> (g' \<turnstile> n \<simeq> e)"
  apply (rule impI) subgoal premises e using e assms
    apply (induction n e)
                          apply (metis no_encoding rep.ConstantNode)
                         apply (metis no_encoding rep.ParameterNode)
                        apply (metis no_encoding rep.ConditionalNode)
                       apply (metis no_encoding rep.AbsNode)
                      apply (metis no_encoding rep.ReverseBytesNode)
                      apply (metis no_encoding rep.BitCountNode)
                      apply (metis no_encoding rep.NotNode)
                     apply (metis no_encoding rep.NegateNode)
                    apply (metis no_encoding rep.LogicNegationNode)
                   apply (metis no_encoding rep.AddNode)
                  apply (metis no_encoding rep.MulNode)
                 apply (metis no_encoding rep.SubNode)
                apply (metis no_encoding rep.AndNode)
               apply (metis no_encoding rep.OrNode)
                apply (metis no_encoding rep.XorNode)
               apply (metis no_encoding rep.ShortCircuitOrNode)
              apply (metis no_encoding rep.LeftShiftNode)
             apply (metis no_encoding rep.RightShiftNode)
            apply (metis no_encoding rep.UnsignedRightShiftNode)
           apply (metis no_encoding rep.IntegerBelowNode)
          apply (metis no_encoding rep.IntegerEqualsNode)
         apply (metis no_encoding rep.IntegerLessThanNode)
         apply (metis no_encoding rep.IntegerTestNode)
        apply (metis no_encoding rep.IntegerNormalizeCompareNode)
        apply (metis no_encoding rep.IntegerMulHighNode)
        apply (metis no_encoding rep.NarrowNode)
       apply (metis no_encoding rep.SignExtendNode)
      apply (metis no_encoding rep.ZeroExtendNode)
     apply (metis no_encoding rep.LeafNode)
      apply (metis no_encoding rep.PiNode)
    apply (metis no_encoding rep.RefNode)
   by (metis no_encoding rep.IsNullNode)
  done

lemma fresh_node_subset:
  assumes "n \<notin> ids g"
  assumes "g' = add_node n (k, s) g"
  shows "as_set g \<subseteq> as_set g'"
  by (smt (z3) Collect_mono_iff Diff_idemp Diff_insert_absorb add_changed as_set_def unchanged.simps
      disjoint_change assms)

lemma unrep_subset:
  assumes "(g \<oplus> e \<leadsto> (g', n))"
  shows "as_set g \<subseteq> as_set g'"
  using assms proof (induction g e "(g', n)" arbitrary: g' n)
  case (ConstantNodeSame g c n)
  then show ?case by blast
next
  case (ConstantNodeNew g c n g')
  then show ?case 
    using fresh_ids fresh_node_subset by simp
next
  case (ParameterNodeSame g i s n)
  then show ?case 
    by auto
next
  case (ParameterNodeNew g i s n g')
  then show ?case 
    using fresh_ids fresh_node_subset by simp
next
  case (ConditionalNodeSame g ce g2 c te g3 t fe g4 f s' n)
  then show ?case 
    by auto
next
  case (ConditionalNodeNew g ce g2 c te g3 t fe g4 f s' n g')
  then show ?case 
    by (meson subset_trans fresh_ids fresh_node_subset)
next
  case (UnaryNodeSame g xe g2 x s' op n)
  then show ?case 
    by auto
next
  case (UnaryNodeNew g xe g2 x s' op n g')
  then show ?case 
    by (meson subset_trans fresh_ids fresh_node_subset)
next
  case (BinaryNodeSame g xe g2 x ye g3 y s' op n)
  then show ?case 
    by auto
next
  case (BinaryNodeNew g xe g2 x ye g3 y s' op n g')
  then show ?case 
    by (meson subset_trans fresh_ids fresh_node_subset)
next
  case (AllLeafNodes g n s)
  then show ?case 
    by auto
qed

lemma fresh_node_preserves_other_nodes:
  assumes "n' = get_fresh_id g"
  assumes "g' = add_node n' (k, s) g"
  shows "\<forall> n \<in> ids g . (g \<turnstile> n \<simeq> e) \<longrightarrow> (g' \<turnstile> n \<simeq> e)"
  using assms apply auto
  by (metis fresh_node_subset subset_implies_evals fresh_ids assms)

lemma found_node_preserves_other_nodes:
  assumes "find_node_and_stamp g (k, s) = Some n"
  shows "\<forall> n \<in> ids g. (g \<turnstile> n \<simeq> e) \<longleftrightarrow> (g \<turnstile> n \<simeq> e)"
  by (auto simp add: assms) 

lemma unrep_ids_subset[simp]:
  assumes "g \<oplus> e \<leadsto> (g', n)"
  shows "ids g \<subseteq> ids g'"
  by (meson graph_refinement_def subset_refines unrep_subset assms)

lemma unrep_unchanged:
  assumes "g \<oplus> e \<leadsto> (g', n)"
  shows "\<forall> n \<in> ids g . \<forall> e. (g \<turnstile> n \<simeq> e) \<longrightarrow> (g' \<turnstile> n \<simeq> e)"
  by (meson subset_implies_evals unrep_subset assms)

theorem term_graph_reconstruction:
  "g \<oplus> e \<leadsto> (g', n) \<Longrightarrow> (g' \<turnstile> n \<simeq> e) \<and> as_set g \<subseteq> as_set g'"
  subgoal premises e apply (rule conjI) defer
    using e unrep_subset apply blast using e
  proof (induction g e "(g', n)" arbitrary: g' n)
    case (ConstantNodeSame g' c n)
    then have "kind g' n = ConstantNode c"
      using find_exists_kind by blast
    then show ?case 
      by (simp add: ConstantNode)
  next
    case (ConstantNodeNew g c)
    then show ?case
      using IRNode.distinct(697) by (simp add: add_node_lookup ConstantNode)
  next
    case (ParameterNodeSame i s)
    then show ?case
      by (metis ParameterNode find_exists_kind find_exists_stamp)
  next
    case (ParameterNodeNew g i s)
    then show ?case
      by (metis IRNode.distinct(3523) ParameterNode find_new_kind find_new_stamp)
  next
    case (ConditionalNodeSame g4 c t f s' n g ce g2 te g3 fe)
    then have k: "kind g4 n = ConditionalNode c t f"
      using find_exists_kind by blast
    have c: "g4 \<turnstile> c \<simeq> ce" 
      using local.ConditionalNodeSame unrep_unchanged no_encoding by blast
    have t: "g4 \<turnstile> t \<simeq> te" 
      using local.ConditionalNodeSame unrep_unchanged no_encoding by blast
    have f: "g4 \<turnstile> f \<simeq> fe" 
      using local.ConditionalNodeSame unrep_unchanged no_encoding by blast
    then show ?case 
      by (auto simp add: k ConditionalNode c t)
  next
    case (ConditionalNodeNew g4 c t f s' g ce g2 te g3 fe n g')
    moreover have "ConditionalNode c t f \<noteq> NoNode"
      by simp
    ultimately have k: "kind g' n = ConditionalNode c t f"
      by (simp add: find_new_kind)
    then have c: "g' \<turnstile> c \<simeq> ce" 
      by (metis ConditionalNodeNew.hyps(9) fresh_node_preserves_other_nodes no_encoding 
          local.ConditionalNodeNew(3,4,6,9,10) unrep_unchanged)
    then have t: "g' \<turnstile> t \<simeq> te" 
      by (metis no_encoding fresh_node_preserves_other_nodes local.ConditionalNodeNew(5,6,9,10) 
          unrep_unchanged)
    then have f: "g' \<turnstile> f \<simeq> fe" 
      by (metis no_encoding fresh_node_preserves_other_nodes local.ConditionalNodeNew(7,9,10))
    then show ?case 
      by (simp add: c t ConditionalNode k)
  next
    case (UnaryNodeSame g' op x s' n g xe)
    then have k: "kind g' n = unary_node op x"
      using find_exists_kind by blast
    then have "g' \<turnstile> x \<simeq> xe" 
      by (simp add: local.UnaryNodeSame)
    then show ?case 
      using k apply (cases op)
      using unary_node.simps(1,2,3,4,5,6,7,8,9,10)
            AbsNode NegateNode NotNode LogicNegationNode NarrowNode SignExtendNode ZeroExtendNode 
            IsNullNode ReverseBytesNode BitCountNode
      by presburger+
  next
    case (UnaryNodeNew g2 op x s' g xe n g')
    moreover have "unary_node op x \<noteq> NoNode"
      using unary_node.elims by blast
    ultimately have k: "kind g' n = unary_node op x"
      by (simp add: find_new_kind)
    have "x \<in> ids g2" 
      using local.UnaryNodeNew eval_contains_id by simp
    then have "x \<noteq> n" 
      using fresh_ids by (auto simp add: local.UnaryNodeNew(5))
    have "g' \<turnstile> x \<simeq> xe" 
      using \<open>x \<in> ids g2\<close> by (simp add: fresh_node_preserves_other_nodes local.UnaryNodeNew)
    then show ?case 
      using k apply (cases op)
      using unary_node.simps(1,2,3,4,5,6,7,8,9,10)
            AbsNode NegateNode NotNode LogicNegationNode NarrowNode SignExtendNode ZeroExtendNode 
            IsNullNode ReverseBytesNode BitCountNode
      by presburger+
  next
    case (BinaryNodeSame g3 op x y s' n g xe g2 ye)
    then have k: "kind g3 n = bin_node op x y"
      using find_exists_kind by blast
    have x: "g3 \<turnstile> x \<simeq> xe" 
      using local.BinaryNodeSame unrep_unchanged no_encoding by blast
    have y: "g3 \<turnstile> y \<simeq> ye" 
      by (simp add: local.BinaryNodeSame)
    then show ?case 
      using x k apply (cases op)
      using bin_node.simps(1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16)
            AddNode MulNode SubNode AndNode OrNode ShortCircuitOrNode LeftShiftNode RightShiftNode 
            UnsignedRightShiftNode IntegerEqualsNode IntegerLessThanNode IntegerBelowNode XorNode
            IntegerTestNode IntegerNormalizeCompareNode IntegerMulHighNode
      by presburger+
  next
    case (BinaryNodeNew g3 op x y s' g xe g2 ye n g')
    moreover have "bin_node op x y \<noteq> NoNode"
      using bin_node.elims by blast
    ultimately have k: "kind g' n = bin_node op x y"
      by (simp add: find_new_kind)
    then have k: "kind g' n = bin_node op x y"
      by simp
    have x: "g' \<turnstile> x \<simeq> xe" 
      using local.BinaryNodeNew
      by (meson fresh_node_preserves_other_nodes no_encoding unrep_unchanged)
    have y: "g' \<turnstile> y \<simeq> ye" 
      using local.BinaryNodeNew 
      by (meson fresh_node_preserves_other_nodes no_encoding)
    then show ?case 
      using x k apply (cases op)
      using bin_node.simps(1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16)
            AddNode MulNode SubNode AndNode OrNode ShortCircuitOrNode LeftShiftNode RightShiftNode
            UnsignedRightShiftNode IntegerEqualsNode IntegerLessThanNode XorNode IntegerBelowNode
            IntegerTestNode IntegerNormalizeCompareNode IntegerMulHighNode
      by presburger+
  next
    case (AllLeafNodes g n s)
    then show ?case 
      by (simp add: rep.LeafNode)
  qed
  done

lemma ref_refinement:
  assumes "g \<turnstile> n \<simeq> e\<^sub>1"
  assumes "kind g n' = RefNode n"
  shows "g \<turnstile> n' \<unlhd> e\<^sub>1"
  by (meson equal_refines graph_represents_expression_def RefNode assms)

lemma unrep_refines:
  assumes "g \<oplus> e \<leadsto> (g', n)"
  shows "graph_refinement g g'"
  using assms by (simp add: unrep_subset subset_refines)

lemma add_new_node_refines:
  assumes "n \<notin> ids g"
  assumes "g' = add_node n (k, s) g"
  shows "graph_refinement g g'"
  using assms by (simp add: fresh_node_subset subset_refines)

lemma add_node_as_set:
  assumes "g' = add_node n (k, s) g"
  shows "({n} \<unlhd> as_set g) \<subseteq> as_set g'"
  unfolding assms
  by (smt (verit, ccfv_SIG) case_prodE changeonly.simps mem_Collect_eq prod.sel(1) subsetI assms
      add_changed as_set_def domain_subtraction_def)

theorem refined_insert:
  assumes "e\<^sub>1 \<ge> e\<^sub>2"
  assumes "g\<^sub>1 \<oplus> e\<^sub>2 \<leadsto> (g\<^sub>2, n')"
  shows "(g\<^sub>2 \<turnstile> n' \<unlhd> e\<^sub>1) \<and> graph_refinement g\<^sub>1 g\<^sub>2"
  using assms graph_construction term_graph_reconstruction by blast

lemma ids_finite: "finite (ids g)"
  by simp

lemma unwrap_sorted: "set (sorted_list_of_set (ids g)) = ids g"
  using ids_finite by simp

lemma find_none:
  assumes "find_node_and_stamp g (k, s) = None"
  shows "\<forall> n \<in> ids g. kind g n \<noteq> k \<or> stamp g n \<noteq> s"
proof -
  have "(\<nexists>n. n \<in> ids g \<and> (kind g n = k \<and> stamp g n = s))"
    by (metis (mono_tags) unwrap_sorted find_None_iff find_node_and_stamp.simps assms)
  then show ?thesis
    by auto
qed

(*

section \<open>An attempt at a constructive refinement proof\<close>
lemma add_node_ids_subset:
  assumes "n \<in> ids g"
  assumes "g' = add_node n node g"
  shows "ids g' = ids g \<union> {n}"
  using assms unfolding add_node_def
  apply (cases "fst node = NoNode") 
  using ids.rep_eq replace_node.rep_eq replace_node_def apply auto[1]
  unfolding ids_def
  by (smt (verit, best) Collect_cong Un_insert_right dom_fun_upd fst_conv fun_upd_apply ids.rep_eq ids_def insert_absorb mem_Collect_eq option.inject option.simps(3) replace_node.rep_eq replace_node_def sup_bot.right_neutral)
  
theorem constructive_refinement:
  assumes 1: "e\<^sub>1 \<ge> e\<^sub>2"
  assumes "g\<^sub>1 \<turnstile> n \<simeq> e\<^sub>1"
  assumes "g\<^sub>1 \<oplus> e\<^sub>2 \<leadsto> (g\<^sub>2, n')"
  assumes "n \<noteq> n'"
  assumes "g\<^sub>3 = add_node n (RefNode n', stamp g\<^sub>2 n') g\<^sub>2"
  shows "graph_refinement g\<^sub>1 g\<^sub>3"
proof -
  have step1: "graph_refinement g\<^sub>1 g\<^sub>2"
    using assms(2,3)
    by (simp add: subset_refines unrep_subset)
  have "n \<in> ids g\<^sub>2"
    using assms(2) assms(3) no_encoding unrep_unchanged by blast
  then have "ids g\<^sub>2 = ids g\<^sub>3"
    using assms(5) add_node_ids_subset
    by blast
  have 3: "g\<^sub>2 \<turnstile> n \<simeq> e\<^sub>1"
    using assms(3)
    using assms(2) subset_implies_evals unrep_subset by blast
  then have g2rep1: "g\<^sub>2 \<turnstile> n \<unlhd> e\<^sub>1"
    using 1 unfolding graph_represents_expression_def
    by blast
  have g2rep: "g\<^sub>2 \<turnstile> n' \<unlhd> e\<^sub>1"
    using assms(3) term_graph_reconstruction
    using "1" graph_construction by blast
  have 2: "({n} \<unlhd> as_set g\<^sub>2) \<subseteq> as_set g\<^sub>3"
    using assms(5) add_node_as_set by blast
  have "kind g\<^sub>3 n = RefNode n'"
    using assms(5) find_new_kind by blast
  have g3rep: "(g\<^sub>3 \<turnstile> n' \<unlhd> e\<^sub>1)"
    using g2rep1 g2rep assms(4) 2 
    (*by (meson \<open>kind g\<^sub>3 n = RefNode n'\<close> assms(5) graph_represents_expression_def rep_ref)*)
  have refkind: "kind g\<^sub>3 n = RefNode n'"
    using assms(5) add_node_lookup
    by (metis IRNode.distinct(2755))
  then have 4: "g\<^sub>3 \<turnstile> n \<unlhd> e\<^sub>1"
    using assms
    using RefNode g3rep
    by (meson graph_represents_expression_def)
  have step2: "graph_refinement g\<^sub>2 g\<^sub>3"
    using graph_semantics_preservation 1 2 3 4
    by (meson graph_represents_expression_def order_trans)
  from step1 step2 show ?thesis
    by (meson assms(3) graph_refinement_def order_trans subsetD subset_implies_evals unrep_subset)
qed
*)





(*
lemma
  assumes "maximal_sharing g\<^sub>1"
  assumes "e\<^sub>1 \<ge> e\<^sub>2"
  assumes "g\<^sub>1 \<oplus> e\<^sub>2 \<leadsto> (g\<^sub>2, n')"
  shows "maximal_sharing g\<^sub>2"
  using assms(3,1)
  apply (induction g\<^sub>1 e\<^sub>2 "(g\<^sub>2, n')" arbitrary: g\<^sub>2 n') 
  apply blast using find_none sorry
*)


(*
lemma
  assumes "maximal_sharing g"
  assumes "g \<oplus> e \<leadsto> (g', n)"
  shows "\<forall>n' . n' \<in> ids g' - ids g \<longrightarrow> 
         (\<forall>e . (g' \<turnstile> n' \<simeq> e) \<longrightarrow> 
          \<not>(\<exists>n'' . n'' \<in> true_ids g' \<and> n'' = n' \<and> (g' \<turnstile> n'' \<simeq> e)))"
  using assms(2)
  apply (induction g e "(g', n)" arbitrary: g' n) 
  apply blast sorry

lemma
  "maximal_sharing g \<Longrightarrow> g \<oplus> e \<leadsto> (g', n) \<Longrightarrow> maximal_sharing g'"
  sorry

lemma only_n_changes:
  assumes "({n} \<unlhd> as_set g) \<subseteq> as_set g'"
  shows "\<forall>n'. n' \<in> ids g - {n} \<longrightarrow> (\<forall>e. (g \<turnstile> n' \<simeq> e) \<longrightarrow> (g' \<turnstile> n' \<simeq> e))"
  apply (rule allI) apply (rule impI)
  subgoal premises set for n' apply (rule allI) apply (rule impI)
    subgoal premises eval for e
      using eval set assms proof (induction n' e )
      case (ConstantNode n c)
      then show ?case
        by (metis Diff_iff not_excluded_keep_type rep.ConstantNode)
    next
      case (ParameterNode n i s)
      then show ?case
        by (metis DiffD1 DiffD2 not_excluded_keep_type rep.ParameterNode)
    next
      case (ConditionalNode n c t f ce te fe)
      then show ?case sorry
    next
      case (AbsNode n x xe)
      then show ?case sorry
    next
      case (NotNode n x xe)
      then show ?case sorry
    next
      case (NegateNode n x xe)
      then show ?case sorry
    next
      case (LogicNegationNode n x xe)
      then show ?case sorry
    next
      case (AddNode n x y xe ye)
      then show ?case sorry
    next
      case (MulNode n x y xe ye)
      then show ?case sorry
    next
      case (SubNode n x y xe ye)
      then show ?case sorry
    next
      case (AndNode n x y xe ye)
      then show ?case sorry
    next
      case (OrNode n x y xe ye)
      then show ?case sorry
    next
      case (XorNode n x y xe ye)
      then show ?case sorry
    next
      case (LeftShiftNode n x y xe ye)
      then show ?case sorry
    next
      case (RightShiftNode n x y xe ye)
      then show ?case sorry
    next
      case (UnsignedRightShiftNode n x y xe ye)
      then show ?case sorry
    next
      case (IntegerBelowNode n x y xe ye)
      then show ?case sorry
    next
      case (IntegerEqualsNode n x y xe ye)
      then show ?case sorry
    next
      case (IntegerLessThanNode n x y xe ye)
      then show ?case sorry
    next
      case (NarrowNode n inputBits resultBits x xe)
      then show ?case sorry
    next
      case (SignExtendNode n inputBits resultBits x xe)
      then show ?case sorry
    next
      case (ZeroExtendNode n inputBits resultBits x xe)
      then show ?case sorry
    next
      case (LeafNode n s)
      then show ?case sorry
    next
      case (RefNode n n' e)
      then show ?case sorry
    qed
     
      apply (metis ConstantNode DiffE not_excluded_keep_type)
      apply (metis DiffD1 DiffD2 ParameterNode not_excluded_keep_type) sorry
  proof -
    have "kind g n' = kind g' n'"
      using assms set
      by (meson Diff_iff not_excluded_keep_type)
    moreover have "stamp g n' = stamp g' n'"
      using assms set
      by (meson DiffE not_excluded_keep_type)
    ultimately show "\<forall>e. (g \<turnstile> n' \<simeq> e) \<longrightarrow> (g' \<turnstile> n' \<simeq> e)"
      using assms sorry
  qed
  done*)

method ref_represents uses node =
  (metis IRNode.distinct(2755) RefNode dual_order.refl find_new_kind fresh_node_subset node subset_implies_evals)

(*
lemma
  assumes "kind g n = RefNode n'"
  assumes "g \<turnstile> n \<simeq> e"
  assumes "n \<noteq> n'"
  shows "n \<notin> eval_usages g n'"
  using assms(2,1,3) apply (induction e arbitrary: n; auto) sorry


lemma unaffected_rep:
  assumes "({n} \<unlhd> as_set g) \<subseteq> as_set g'"
  assumes "g \<turnstile> n' \<simeq> e"
  assumes "n \<notin> eval_usages g n'"
  shows "g' \<turnstile> n' \<simeq> e"
  using assms(2)
proof -
  have ne: "n \<noteq> n'"
    using assms(3)
    using assms(2) eval_contains_id eval_usages_self by blast
  show ?thesis 
    using assms(2) assms ne apply (induction e) using ne 
                        apply (metis ConstantNode encodes_contains not_excluded_keep_type not_in_g singleton_iff)
                      apply (metis ParameterNode empty_iff encode_in_ids insertE not_excluded_keep_type)
    sorry
qed

lemma ref_add_represents:
  assumes "g \<turnstile> n \<unlhd> e"
  assumes "g \<turnstile> n' \<unlhd> e"
  assumes "g' = add_node n' (RefNode n, s) g"
  assumes "n' \<notin> eval_usages g n"
  shows "g' \<turnstile> n' \<unlhd> e" using assms
  by (metis IRNode.distinct(2755) RefNode add_node_as_set find_new_kind graph_represents_expression_def unaffected_rep)
(*proof -
  have as_set: "({n'} \<unlhd> as_set g) \<subseteq> as_set g'"
    using assms(3)
    by (simp add: add_node_as_set)
  have "kind g' n' = RefNode n"
    using assms(3)
    using find_new_kind by blast
  show ?thesis unfolding graph_represents_expression_def 
  proof -
    obtain e' where e'def: "(g \<turnstile> n \<simeq> e') \<and> e \<ge> e'"
      using assms(1) graph_represents_expression_def by blast
    then obtain e2' where "g' \<turnstile> n \<simeq> e2'"
      using as_set using unaffected_rep
      using assms(4) by blast
    obtain e'' where e''def: "(g \<turnstile> n' \<simeq> e'') \<and> e \<ge> e''"
      using assms(2) graph_represents_expression_def by blast
    have "g' \<turnstile> n' \<simeq> e''"
      using as_set e''def sorry
    show "\<exists>e'. (g' \<turnstile> n' \<simeq> e') \<and> e \<ge> e'"
   sorry
   sorry
                      (*apply (ref_represents node: rep.ConstantNode)
                      apply (ref_represents node: rep.ParameterNode)
                      apply (ref_represents node: rep.ConditionalNode)
                      apply (ref_represents node: rep.AbsNode)
                     apply (ref_represents node: rep.NotNode)
                    apply (ref_represents node: rep.NegateNode)
                   apply (ref_represents node: rep.LogicNegationNode)
                  apply (ref_represents node: rep.AddNode)
                 apply (ref_represents node: rep.MulNode)
                apply (ref_represents node: rep.SubNode)
               apply (ref_represents node: rep.AndNode)
              apply (ref_represents node: rep.OrNode)
             apply (ref_represents node: rep.XorNode)
            apply (ref_represents node: rep.LeftShiftNode)
           apply (ref_represents node: rep.RightShiftNode)
          apply (ref_represents node: rep.UnsignedRightShiftNode)
         apply (ref_represents node: rep.IntegerBelowNode)
        apply (ref_represents node: rep.IntegerEqualsNode)
       apply (ref_represents node: rep.IntegerLessThanNode)
      apply (ref_represents node: rep.NarrowNode)
     apply (ref_represents node: rep.SignExtendNode)
    apply (ref_represents node: rep.ZeroExtendNode)
   apply (ref_represents node: rep.LeafNode)
  by (ref_represents node: rep.RefNode)*)
*)

theorem constructive_refinement:
  assumes 1: "e\<^sub>1 \<ge> e\<^sub>2"
  assumes "g\<^sub>1 \<turnstile> n \<simeq> e\<^sub>1"
  assumes "g\<^sub>1 \<triangleleft> e\<^sub>2 \<leadsto> (g\<^sub>2, n')"
  assumes "n \<noteq> n'"
  assumes "g\<^sub>3 = add_node n (RefNode n', stamp g\<^sub>2 n') g\<^sub>2"
  shows "graph_refinement g\<^sub>1 g\<^sub>3"
proof -
  have step1: "graph_refinement g\<^sub>1 g\<^sub>2"
    using assms(2,3)
    by (simp add: subset_refines unrep_subset)
  have "ids g\<^sub>2 \<subseteq> ids g\<^sub>3"
    using assms(5)
    by (metis (no_types, lifting) IRNode.distinct(2755) add_node_def assms(2) assms(3) find_new_kind ids_some insertE insert_Diff no_encoding replace_node_def replace_node_unchanged subsetI unrep_unchanged)
  have 3: "g\<^sub>2 \<turnstile> n \<simeq> e\<^sub>1"
    using assms(3)
    using assms(2) subset_implies_evals unrep_subset by blast
  then have g2rep1: "g\<^sub>2 \<turnstile> n \<unlhd> e\<^sub>1"
    using 1 unfolding graph_represents_expression_def
    by blast
  have g2rep: "g\<^sub>2 \<turnstile> n' \<unlhd> e\<^sub>1"
    using assms(3) term_graph_reconstruction
    using "1" graph_construction by blast
  have 2: "({n} \<unlhd> as_set g\<^sub>2) \<subseteq> as_set g\<^sub>3"
    using assms(5) add_node_as_set by blast
  have "kind g\<^sub>3 n = RefNode n'"
    using assms(5) find_new_kind by blast
  have g3rep: "(g\<^sub>3 \<turnstile> n' \<unlhd> e\<^sub>1)"
    using g2rep1 g2rep assms(4) 2 ref_add_represents g2rep1 sorry
    (*by (meson \<open>kind g\<^sub>3 n = RefNode n'\<close> assms(5) graph_represents_expression_def rep_ref)*)
  have refkind: "kind g\<^sub>3 n = RefNode n'"
    using assms(5) add_node_lookup
    by (metis IRNode.distinct(2755))
  then have 4: "g\<^sub>3 \<turnstile> n \<unlhd> e\<^sub>1"
    using assms
    using RefNode g3rep
    by (meson graph_represents_expression_def)
  have step2: "graph_refinement g\<^sub>2 g\<^sub>3"
    using graph_semantics_preservation 1 2 3 4
    by (meson graph_represents_expression_def order_trans)
  from step1 step2 show ?thesis
    by (meson assms(3) graph_refinement_def order_trans subsetD subset_implies_evals unrep_subset)
qed
*)

subsubsection \<open>Data-flow Tree to Subgraph Preserves Maximal Sharing\<close>

lemma same_kind_stamp_encodes_equal:
  assumes "kind g n = kind g n'"
  assumes "stamp g n = stamp g n'"
  assumes "\<not>(is_preevaluated (kind g n))"
  shows "\<forall> e. (g \<turnstile> n \<simeq> e) \<longrightarrow> (g \<turnstile> n' \<simeq> e)"
  apply (rule allI)
  subgoal for e
    apply (rule impI)
    subgoal premises eval using eval assms
      apply (induction e)
    using ConstantNode apply presburger
    using ParameterNode apply presburger 
                        apply (metis ConditionalNode)
                        apply (metis AbsNode)
                        apply (metis ReverseBytesNode)
                        apply (metis BitCountNode)
                       apply (metis NotNode)
                      apply (metis NegateNode)
                     apply (metis LogicNegationNode)
                    apply (metis AddNode)
                   apply (metis MulNode)
                  apply (metis SubNode)
                 apply (metis AndNode)
                apply (metis OrNode)
                apply (metis XorNode)
                apply (metis ShortCircuitOrNode)
              apply (metis LeftShiftNode)
             apply (metis RightShiftNode)
            apply (metis UnsignedRightShiftNode)
           apply (metis IntegerBelowNode)
          apply (metis IntegerEqualsNode)
         apply (metis IntegerLessThanNode)
          apply (metis IntegerTestNode)
        apply (metis IntegerNormalizeCompareNode)
        apply (metis IntegerMulHighNode)
        apply (metis NarrowNode)
       apply (metis SignExtendNode)
      apply (metis ZeroExtendNode)
    defer
     apply (metis PiNode)
   apply (metis RefNode) 
  apply (metis IsNullNode)
  by blast
    done
  done

lemma new_node_not_present:
  assumes "find_node_and_stamp g (node, s) = None"
  assumes "n = get_fresh_id g"
  assumes "g' = add_node n (node, s) g"
  shows "\<forall> n' \<in> true_ids g. (\<forall>e. ((g \<turnstile> n \<simeq> e) \<and> (g \<turnstile> n' \<simeq> e)) \<longrightarrow> n = n')"
  using assms encode_in_ids fresh_ids by blast

lemma true_ids_def:
  "true_ids g = {n \<in> ids g. \<not>(is_RefNode (kind g n)) \<and> ((kind g n) \<noteq> NoNode)}"
  using true_ids_def by (auto simp add: is_RefNode_def)

lemma add_node_some_node_def:
  assumes "k \<noteq> NoNode"
  assumes "g' = add_node nid (k, s) g"
  shows "g' = Abs_IRGraph ((Rep_IRGraph g)(nid \<mapsto> (k, s)))"
  by (metis Rep_IRGraph_inverse add_node.rep_eq fst_conv assms)

lemma ids_add_update_v1:
  assumes "g' = add_node nid (k, s) g"
  assumes "k \<noteq> NoNode"
  shows "dom (Rep_IRGraph g') = dom (Rep_IRGraph g) \<union> {nid}"
  by (simp add: add_node.rep_eq assms)

lemma ids_add_update_v2:
  assumes "g' = add_node nid (k, s) g"
  assumes "k \<noteq> NoNode"
  shows "nid \<in> ids g'"
  by (simp add: find_new_kind assms)

lemma add_node_ids_subset:
  assumes "n \<in> ids g"
  assumes "g' = add_node n node g"
  shows "ids g' = ids g \<union> {n}"
  using assms replace_node.rep_eq by (auto simp add: replace_node_def ids.rep_eq add_node_def)

lemma convert_maximal:
  assumes "\<forall>n n'. n \<in> true_ids g \<and> n' \<in> true_ids g \<longrightarrow> 
          (\<forall>e e'. (g \<turnstile> n \<simeq> e) \<and> (g \<turnstile> n' \<simeq> e') \<longrightarrow> e \<noteq> e')"
  shows "maximal_sharing g"
  using assms by (auto simp add: maximal_sharing)

lemma add_node_set_eq:
  assumes "k \<noteq> NoNode"
  assumes "n \<notin> ids g"
  shows "as_set (add_node n (k, s) g) = as_set g \<union> {(n, (k, s))}"
  using assms unfolding as_set_def by (transfer; auto)

lemma add_node_as_set_eq:
  assumes "g' = add_node n (k, s) g"
  assumes "n \<notin> ids g"
  shows "({n} \<unlhd> as_set g') = as_set g"
  unfolding domain_subtraction_def
  by (smt (z3) assms add_node_set_eq Collect_cong Rep_IRGraph_inverse UnCI add_node.rep_eq le_boolE
      as_set_def case_prodE2 case_prodI2 le_boolI' mem_Collect_eq prod.sel(1) singletonD singletonI
      UnE)

lemma true_ids:
  "true_ids g = ids g - {n \<in> ids g. is_RefNode (kind g n)}"
  unfolding true_ids_def by fastforce

lemma as_set_ids:
  assumes "as_set g = as_set g'"
  shows "ids g = ids g'"
  by (metis antisym equalityD1 graph_refinement_def subset_refines assms)

lemma ids_add_update:
  assumes "k \<noteq> NoNode"
  assumes "n \<notin> ids g"
  assumes "g' = add_node n (k, s) g"
  shows "ids g' = ids g \<union> {n}"
  by (smt (z3) Diff_idemp Diff_insert_absorb Un_commute add_node.rep_eq insert_is_Un insert_Collect
      add_node_def ids.rep_eq ids_add_update_v1 insertE assms replace_node_unchanged Collect_cong
      map_upd_Some_unfold mem_Collect_eq replace_node_def ids_add_update_v2)

lemma true_ids_add_update:
  assumes "k \<noteq> NoNode"
  assumes "n \<notin> ids g"
  assumes "g' = add_node n (k, s) g"
  assumes "\<not>(is_RefNode k)"
  shows "true_ids g' = true_ids g \<union> {n}" 
  by (smt (z3) Collect_cong Diff_iff Diff_insert_absorb Un_commute add_node_def find_new_kind assms
     insert_Diff_if insert_is_Un mem_Collect_eq replace_node_def replace_node_unchanged true_ids
     ids_add_update)

lemma new_def:
  assumes "(new \<unlhd> as_set g') = as_set g"
  shows "n \<in> ids g \<longrightarrow> n \<notin> new"
  using assms apply auto unfolding as_set_def
  by (smt (z3) as_set_def case_prodD domain_subtraction_def mem_Collect_eq assms ids_some)

lemma add_preserves_rep:
  assumes unchanged: "(new \<unlhd> as_set g') = as_set g"
  assumes closed: "wf_closed g"
  assumes existed: "n \<in> ids g"
  assumes "g' \<turnstile> n \<simeq> e"
  shows "g \<turnstile> n \<simeq> e"
proof (cases "n \<in> new")
  case True
  have "n \<notin> ids g"
    using unchanged True as_set_def unfolding domain_subtraction_def by blast
  then show ?thesis 
    using existed by simp
next
  case False
  have kind_eq: "\<forall> n' . n' \<notin> new \<longrightarrow> kind g n' = kind g' n'"
    \<comment>\<open>can be more general than $stamp\_eq$ because NoNode default is equal\<close>
    apply (rule allI; rule impI)
    by (smt (z3) case_prodE domain_subtraction_def ids_some mem_Collect_eq subsetI unchanged
        not_excluded_keep_type)
  from False have stamp_eq: "\<forall> n' \<in> ids g' . n' \<notin> new \<longrightarrow> stamp g n' = stamp g' n'"
    by (metis equalityE not_excluded_keep_type unchanged)
  show ?thesis 
    using assms(4) kind_eq stamp_eq False
  proof (induction n e rule: rep.induct)
    case (ConstantNode n c)
    then show ?case
      by (simp add: rep.ConstantNode)
  next
    case (ParameterNode n i s)
    then show ?case
      by (metis no_encoding rep.ParameterNode)
  next
    case (ConditionalNode n c t f ce te fe)
    have kind: "kind g n = ConditionalNode c t f"
      by (simp add: kind_eq ConditionalNode.prems(3) ConditionalNode.hyps(1))
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{c, t, f} = inputs g n"
      by (simp add: kind)
    have "c \<in> ids g \<and> t \<in> ids g \<and> f \<in> ids g"
      using closed wf_closed_def isin inputs by blast
    then have "c \<notin> new \<and> t \<notin> new \<and> f \<notin> new"
      using unchanged by (simp add: new_def)
    then show ?case 
      by (simp add: rep.ConditionalNode ConditionalNode)
  next
    case (AbsNode n x xe)
    then have kind: "kind g n = AbsNode x"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{x} = inputs g n"
      by (simp add: kind)
    have "x \<in> ids g"
      using closed wf_closed_def isin inputs by blast
    then have "x \<notin> new"
      using unchanged by (simp add: new_def)
    then show ?case
      by (simp add: AbsNode rep.AbsNode)
  next
    case (ReverseBytesNode n x xe)
    then have kind: "kind g n = ReverseBytesNode x"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{x} = inputs g n"
      by (simp add: kind)
    have "x \<in> ids g"
      using closed wf_closed_def isin inputs by blast
    then have "x \<notin> new"
      using unchanged by (simp add: new_def)
    then show ?case
      using ReverseBytesNode.IH kind kind_eq rep.ReverseBytesNode stamp_eq by blast
  next
    case (BitCountNode n x xe)
    then have kind: "kind g n = BitCountNode x"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{x} = inputs g n"
      by (simp add: kind)
    have "x \<in> ids g"
      using closed wf_closed_def isin inputs by blast
    then have "x \<notin> new"
      using unchanged by (simp add: new_def)
    then show ?case
      using BitCountNode.IH kind kind_eq rep.BitCountNode stamp_eq by blast
  next
    case (NotNode n x xe)
    then have kind: "kind g n = NotNode x"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{x} = inputs g n"
      by (simp add: kind)
    have "x \<in> ids g"
      using closed wf_closed_def isin inputs by blast
    then have "x \<notin> new"
      using unchanged by (simp add: new_def)
    then show ?case 
      by (simp add: NotNode rep.NotNode)
  next
    case (NegateNode n x xe)
    then have kind: "kind g n = NegateNode x"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{x} = inputs g n"
      by (simp add: kind)
    have "x \<in> ids g"
      using closed  wf_closed_def isin inputs by blast
    then have "x \<notin> new"
      using unchanged by (simp add: new_def)
    then show ?case 
      by (simp add: NegateNode rep.NegateNode)
  next
    case (LogicNegationNode n x xe)
    then have kind: "kind g n = LogicNegationNode x"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{x} = inputs g n"
      by (simp add: kind)
    have "x \<in> ids g"
      using closed wf_closed_def isin inputs by blast
    then have "x \<notin> new"
      using unchanged by (simp add: new_def)
    then show ?case 
      by (simp add: LogicNegationNode rep.LogicNegationNode)
  next
    case (AddNode n x y xe ye)
    then have kind: "kind g n = AddNode x y"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{x, y} = inputs g n"
      by (simp add: kind)
    have "x \<in> ids g \<and> y \<in> ids g"
      using closed wf_closed_def isin inputs by blast
    then have "x \<notin> new \<and> y \<notin> new"
      using unchanged by (simp add: new_def)
    then show ?case 
      by (simp add: AddNode rep.AddNode)
  next
    case (MulNode n x y xe ye)
    then have kind: "kind g n = MulNode x y"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{x, y} = inputs g n"
      by (simp add: kind)
    have "x \<in> ids g \<and> y \<in> ids g"
      using closed wf_closed_def isin inputs by blast
    then have "x \<notin> new \<and> y \<notin> new"
      using unchanged by (simp add: new_def)
    then show ?case 
      by (simp add: MulNode rep.MulNode)
  next
    case (SubNode n x y xe ye)
    then have kind: "kind g n = SubNode x y"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{x, y} = inputs g n"
      by (simp add: kind)
    have "x \<in> ids g \<and> y \<in> ids g"
      using closed wf_closed_def isin inputs by blast
    then have "x \<notin> new \<and> y \<notin> new"
      using unchanged by (simp add: new_def)
    then show ?case 
      by (simp add: SubNode rep.SubNode)
  next
    case (AndNode n x y xe ye)
    then have kind: "kind g n = AndNode x y"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{x, y} = inputs g n"
      by (simp add: kind)
    have "x \<in> ids g \<and> y \<in> ids g"
      using closed wf_closed_def isin inputs by blast
    then have "x \<notin> new \<and> y \<notin> new"
      using unchanged by (simp add: new_def)
    then show ?case 
      by (simp add: AndNode rep.AndNode)
  next
    case (OrNode n x y xe ye)
    then have kind: "kind g n = OrNode x y"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{x, y} = inputs g n"
      by (simp add: kind)
    have "x \<in> ids g \<and> y \<in> ids g"
      using closed wf_closed_def isin inputs by blast
    then have "x \<notin> new \<and> y \<notin> new"
      using unchanged by (simp add: new_def)
    then show ?case 
      by (simp add: OrNode rep.OrNode)
  next
    case (XorNode n x y xe ye)
    then have kind: "kind g n = XorNode x y"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{x, y} = inputs g n"
      by (simp add: kind)
    have "x \<in> ids g \<and> y \<in> ids g"
      using closed wf_closed_def isin inputs by blast
    then have "x \<notin> new \<and> y \<notin> new"
      using unchanged by (simp add: new_def)
    then show ?case 
      by (simp add: XorNode rep.XorNode)
  next
    case (ShortCircuitOrNode n x y xe ye)
    then have kind: "kind g n = ShortCircuitOrNode x y"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{x, y} = inputs g n"
      by (simp add: kind)
    have "x \<in> ids g \<and> y \<in> ids g"
      using closed wf_closed_def isin inputs by blast
    then have "x \<notin> new \<and> y \<notin> new"
      using unchanged by (simp add: new_def)
    then show ?case 
      by (simp add: ShortCircuitOrNode rep.ShortCircuitOrNode)
  next
    case (LeftShiftNode n x y xe ye)
    then have kind: "kind g n = LeftShiftNode x y"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{x, y} = inputs g n"
      by (simp add: kind)
    have "x \<in> ids g \<and> y \<in> ids g"
      using closed wf_closed_def isin inputs by blast
    then have "x \<notin> new \<and> y \<notin> new"
      using unchanged by (simp add: new_def)
    then show ?case 
      by (simp add: LeftShiftNode rep.LeftShiftNode)
  next
    case (RightShiftNode n x y xe ye)
    then have kind: "kind g n = RightShiftNode x y"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{x, y} = inputs g n"
      by (simp add: kind)
    have "x \<in> ids g \<and> y \<in> ids g"
      using closed wf_closed_def isin inputs by blast
    then have "x \<notin> new \<and> y \<notin> new"
      using unchanged by (simp add: new_def)
    then show ?case 
      by (simp add: RightShiftNode rep.RightShiftNode)
  next
    case (UnsignedRightShiftNode n x y xe ye)
    then have kind: "kind g n = UnsignedRightShiftNode x y"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{x, y} = inputs g n"
      by (simp add: kind)
    have "x \<in> ids g \<and> y \<in> ids g"
      using closed wf_closed_def isin inputs by blast
    then have "x \<notin> new \<and> y \<notin> new"
      using unchanged by (simp add: new_def)
    then show ?case 
      by (simp add: UnsignedRightShiftNode rep.UnsignedRightShiftNode)
  next
    case (IntegerBelowNode n x y xe ye)
    then have kind: "kind g n = IntegerBelowNode x y"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{x, y} = inputs g n"
      by (simp add: kind)
    have "x \<in> ids g \<and> y \<in> ids g"
      using closed wf_closed_def isin inputs by blast
    then have "x \<notin> new \<and> y \<notin> new"
      using unchanged by (simp add: new_def)
    then show ?case 
      by (simp add: IntegerBelowNode rep.IntegerBelowNode)
  next
    case (IntegerEqualsNode n x y xe ye)
    then have kind: "kind g n = IntegerEqualsNode x y"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{x, y} = inputs g n"
      by (simp add: kind)
    have "x \<in> ids g \<and> y \<in> ids g"
      using closed wf_closed_def isin inputs by blast
    then have "x \<notin> new \<and> y \<notin> new"
      using unchanged by (simp add: new_def)
    then show ?case 
      by (simp add: IntegerEqualsNode rep.IntegerEqualsNode)
  next
    case (IntegerLessThanNode n x y xe ye)
    then have kind: "kind g n = IntegerLessThanNode x y"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{x, y} = inputs g n"
      by (simp add: kind)
    have "x \<in> ids g \<and> y \<in> ids g"
      using closed wf_closed_def isin inputs by blast
    then have "x \<notin> new \<and> y \<notin> new"
      using unchanged by (simp add: new_def)
    then show ?case 
      by (simp add: IntegerLessThanNode rep.IntegerLessThanNode)
  next
    case (IntegerTestNode n x y xe ye)
    then have kind: "kind g n = IntegerTestNode x y"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{x, y} = inputs g n"
      by (simp add: kind)
    have "x \<in> ids g \<and> y \<in> ids g"
      using closed wf_closed_def isin inputs by blast
    then have "x \<notin> new \<and> y \<notin> new"
      using unchanged by (simp add: new_def)
    then show ?case 
      by (simp add: IntegerTestNode rep.IntegerTestNode)
  next
    case (IntegerNormalizeCompareNode n x y xe ye)
    then have kind: "kind g n = IntegerNormalizeCompareNode x y"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{x, y} = inputs g n"
      by (simp add: kind)
    have "x \<in> ids g \<and> y \<in> ids g"
      using closed wf_closed_def isin inputs by blast
    then have "x \<notin> new \<and> y \<notin> new"
      using unchanged by (simp add: new_def)
    then show ?case
      using IntegerNormalizeCompareNode.IH(1,2) kind kind_eq rep.IntegerNormalizeCompareNode
            stamp_eq by blast
  next
    case (IntegerMulHighNode n x y xe ye)
    then have kind: "kind g n = IntegerMulHighNode x y"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{x, y} = inputs g n"
      by (simp add: kind)
    have "x \<in> ids g \<and> y \<in> ids g"
      using closed wf_closed_def isin inputs by blast
    then have "x \<notin> new \<and> y \<notin> new"
      using unchanged by (simp add: new_def)
    then show ?case
      using IntegerMulHighNode.IH(1,2) kind kind_eq rep.IntegerMulHighNode stamp_eq by blast
  next
    case (NarrowNode n inputBits resultBits x xe)
    then have kind: "kind g n = NarrowNode inputBits resultBits x"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{x} = inputs g n"
      by (simp add: kind)
    have "x \<in> ids g"
      using closed wf_closed_def isin inputs by blast
    then have "x \<notin> new"
      using unchanged by (simp add: new_def)
    then show ?case 
      by (simp add: NarrowNode rep.NarrowNode)
  next
    case (SignExtendNode n inputBits resultBits x xe)
    then have kind: "kind g n = SignExtendNode inputBits resultBits x"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{x} = inputs g n"
      by (simp add: kind)
    have "x \<in> ids g"
      using closed wf_closed_def isin inputs by blast
    then have "x \<notin> new"
      using unchanged by (simp add: new_def)
    then show ?case 
      by (simp add: SignExtendNode rep.SignExtendNode)
  next
    case (ZeroExtendNode n inputBits resultBits x xe)
    then have kind: "kind g n = ZeroExtendNode inputBits resultBits x"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{x} = inputs g n"
      by (simp add: kind)
    have "x \<in> ids g"
      using closed wf_closed_def isin inputs by blast
    then have "x \<notin> new"
      using unchanged by (simp add: new_def)
    then show ?case 
      by (simp add: ZeroExtendNode rep.ZeroExtendNode)
  next
    case (LeafNode n s)
    then show ?case
      by (metis no_encoding rep.LeafNode)
  next
    case (PiNode n n' gu e)
    then have kind: "kind g n = PiNode n' gu"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "set (n' # (opt_to_list gu)) = inputs g n"
      by (simp add: kind)
    have "n' \<in> ids g"
      by (metis in_mono list.set_intros(1) inputs isin wf_closed_def closed)
    then show ?case
      using PiNode.IH kind kind_eq new_def rep.PiNode stamp_eq unchanged by blast
  next
    case (RefNode n n' e)
    then have kind: "kind g n = RefNode n'"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{n'} = inputs g n"
      by (simp add: kind)
    have "n' \<in> ids g"
      using closed wf_closed_def isin inputs by blast
    then have "n' \<notin> new"
      using unchanged by (simp add: new_def)
    then show ?case
      by (simp add: RefNode rep.RefNode)
  next
    case (IsNullNode n v)
    then have kind: "kind g n = IsNullNode v"
      by simp
    then have isin: "n \<in> ids g"
      by simp
    have inputs: "{v} = inputs g n"
      by (simp add: kind)
    have "v \<in> ids g"
      using closed wf_closed_def isin inputs by blast
    then have "v \<notin> new"
      using unchanged by (simp add: new_def)
    then show ?case 
      by (simp add: rep.IsNullNode stamp_eq kind_eq kind IsNullNode.IH)
  qed 
qed

lemma not_in_no_rep:
  "n \<notin> ids g \<Longrightarrow> \<forall>e. \<not>(g \<turnstile> n \<simeq> e)"
  using eval_contains_id by auto

(*
lemma insert_maximal_sharing:
  assumes "k \<noteq> NoNode \<and> \<not>(is_RefNode k)"
  assumes "find_node_and_stamp g (k, s) = None"
  assumes "n = get_fresh_id g"
  assumes "g' = add_node n (k, s) g"
  assumes "g' \<turnstile> n \<simeq> e"
  assumes "wf_closed g"
  assumes "maximal_sharing g"
  shows "maximal_sharing g'"
using assms proof -
  have "kind g' n = k"
    using assms find_new_kind by blast
  have "\<not>(is_RefNode k) \<and> k \<noteq> NoNode"
    using assms(1) by simp
  then have dom: "true_ids g' = true_ids g \<union> {n}"
    using assms(3) assms(4) fresh_ids true_ids_add_update by presburger
  have new: "n \<notin> ids g"
    using fresh_ids
    using assms(3) by presburger
  obtain new where "new = true_ids g' - true_ids g"
    by simp
  then have new_def: "new = {n}"
    by (metis (no_types, lifting) DiffE Diff_cancel IRGraph.true_ids_def Un_insert_right dom insert_Diff_if new sup_bot_right)
  then have unchanged: "(new \<unlhd> as_set g') = as_set g"
    using add_node_as_set_eq assms(4) new by presburger
  then have kind_eq: "\<forall>n' . n' \<notin> new \<longrightarrow> kind g n' = kind g' n'"
    by (metis add_node_as_set assms(4) local.new_def not_excluded_keep_type not_in_g order_class.order_eq_iff)
  from unchanged have stamp_eq: "\<forall>n' \<in> ids g . n' \<notin> new \<longrightarrow> stamp g n' = stamp g' n'"
    using not_excluded_keep_type new_def new
    by (metis add_node_as_set assms(4))
  show ?thesis unfolding maximal_sharing apply (rule allI; rule allI; rule impI)
  using assms(7) unfolding maximal_sharing apply auto
  proof -
    fix n\<^sub>1 n\<^sub>2 e
    assume 1: "\<forall>n\<^sub>1 n\<^sub>2.
          n\<^sub>1 \<in> true_ids g \<and> n\<^sub>2 \<in> true_ids g \<longrightarrow>
          (\<exists>e. (g \<turnstile> n\<^sub>1 \<simeq> e) \<and> (g \<turnstile> n\<^sub>2 \<simeq> e) \<and> stamp g n\<^sub>1 = stamp g n\<^sub>2) \<longrightarrow> n\<^sub>1 = n\<^sub>2"
    assume "n\<^sub>1 \<in> true_ids g'"
    assume "n\<^sub>2 \<in> true_ids g'"
    show "g' \<turnstile> n\<^sub>1 \<simeq> e \<Longrightarrow> g' \<turnstile> n\<^sub>2 \<simeq> e \<Longrightarrow> stamp g' n\<^sub>1 = stamp g' n\<^sub>2 \<Longrightarrow> n\<^sub>1 = n\<^sub>2" 
    proof (cases "n\<^sub>1 \<in> true_ids g")
      case n1: True
      then show "g' \<turnstile> n\<^sub>1 \<simeq> e \<Longrightarrow> g' \<turnstile> n\<^sub>2 \<simeq> e \<Longrightarrow> stamp g' n\<^sub>1 = stamp g' n\<^sub>2 \<Longrightarrow> n\<^sub>1 = n\<^sub>2"
      proof (cases "n\<^sub>2 \<in> true_ids g")
        case n2: True
        assume n1rep': "g' \<turnstile> n\<^sub>1 \<simeq> e"
        assume n2rep': "g' \<turnstile> n\<^sub>2 \<simeq> e"
        assume "stamp g' n\<^sub>1 = stamp g' n\<^sub>2"
        have n1rep: "g \<turnstile> n\<^sub>1 \<simeq> e"
          using n1rep' kind_eq stamp_eq new_def add_preserves_rep
          using IRGraph.true_ids_def assms(6) n1 unchanged by auto
        have n2rep: "g \<turnstile> n\<^sub>2 \<simeq> e"
          using n2rep' kind_eq stamp_eq new_def add_preserves_rep
          using IRGraph.true_ids_def assms(6) n2 unchanged by auto
        have "stamp g n\<^sub>1 = stamp g n\<^sub>2"
          by (metis \<open>stamp g' n\<^sub>1 = stamp g' n\<^sub>2\<close> assms(4) fresh_node_subset n1rep n2rep new subset_stamp)
        then show ?thesis using 1
          using n1 n2
          using n1rep n2rep by blast
      next
        case n2: False
        assume n1rep': "g' \<turnstile> n\<^sub>1 \<simeq> e"
        assume n2rep': "g' \<turnstile> n\<^sub>2 \<simeq> e"
        assume "stamp g' n\<^sub>1 = stamp g' n\<^sub>2"
        have "n\<^sub>2 = n"
          using \<open>n\<^sub>2 \<in> true_ids g'\<close> dom n2 by auto
        then have ne: "n\<^sub>2 \<notin> ids g"
          using new n2 by blast
        then show ?thesis sorry
        have n1rep: "g \<turnstile> n\<^sub>1 \<simeq> e"
          using n1rep' kind_eq stamp_eq new_def add_preserves_rep
          by (metis DiffD1 assms(6) n1 true_ids unchanged)
        have n2rep: "g \<turnstile> n\<^sub>2 \<simeq> e"
          using n2rep' kind_eq stamp_eq new_def add_preserves_rep
          sorry \<comment>\<open>thought this seemed a bit too good to be true\<close>
        then show "n\<^sub>1 = n\<^sub>2" sorry
      qed
    next
      case n1: False
      then show "g' \<turnstile> n\<^sub>1 \<simeq> e \<Longrightarrow> g' \<turnstile> n\<^sub>2 \<simeq> e \<Longrightarrow> stamp g' n\<^sub>1 = stamp g' n\<^sub>2 \<Longrightarrow> n\<^sub>1 = n\<^sub>2"
      proof (cases "n\<^sub>2 \<in> true_ids g")
        case n2: True
        assume n1rep': "g' \<turnstile> n\<^sub>1 \<simeq> e"
        assume n2rep': "g' \<turnstile> n\<^sub>2 \<simeq> e"
        assume "stamp g' n\<^sub>1 = stamp g' n\<^sub>2"
        have "n\<^sub>1 = n"
          using \<open>n\<^sub>1 \<in> true_ids g'\<close> dom n1 by auto
        then have ne: "n\<^sub>1 \<notin> ids g"
          using new n2 by blast
        have n1rep: "g \<turnstile> n\<^sub>1 \<simeq> e"
          using n1rep' kind_eq stamp_eq new_def add_preserves_rep
          using ConstantNodeNew.prems(1) IRGraph.true_ids_def n1 unchanged
          by (smt (verit, best) ConstantNodeE ConstantNodeNew.hyps(1) ConstantNodeNew.hyps(3) IRNode.disc(2703) TreeToGraphThms.true_ids_def UnE \<open>kind g' n = ConstantNode c\<close> \<open>n\<^sub>1 \<in> true_ids g'\<close> \<open>stamp g' n\<^sub>1 = stamp g' n\<^sub>2\<close> dom find_new_stamp find_none mem_Collect_eq n2 n2rep' rep_constant singletonD)
        then show ?thesis
          using n1rep not_in_no_rep ne by blast
      next
        case n2: False
        assume n1rep': "g' \<turnstile> n\<^sub>1 \<simeq> e"
        assume n2rep': "g' \<turnstile> n\<^sub>2 \<simeq> e"
        assume "stamp g' n\<^sub>1 = stamp g' n\<^sub>2"
        have "n\<^sub>1 = n \<and> n\<^sub>2 = n"
          using \<open>n\<^sub>1 \<in> true_ids g'\<close> dom n1
          using \<open>n\<^sub>2 \<in> true_ids g'\<close> n2 by blast
        then show ?thesis
          by simp
      qed
    qed
*)

lemma unary_inputs:
  assumes "kind g n = unary_node op x"
  shows "inputs g n = {x}"
  by (cases op; auto simp add: assms)

lemma unary_succ:
  assumes "kind g n = unary_node op x"
  shows "succ g n = {}"
  by (cases op; auto simp add: assms)

lemma binary_inputs:
  assumes "kind g n = bin_node op x y"
  shows "inputs g n = {x, y}"
  by (cases op; auto simp add: assms)

lemma binary_succ:
  assumes "kind g n = bin_node op x y"
  shows "succ g n = {}"
  by (cases op; auto simp add: assms)

lemma unrep_contains:
  assumes "g \<oplus> e \<leadsto> (g', n)"
  shows "n \<in> ids g'"
  using assms not_in_no_rep term_graph_reconstruction by blast

lemma unrep_preserves_contains:
  assumes "n \<in> ids g"
  assumes "g \<oplus> e \<leadsto> (g', n')"
  shows "n \<in> ids g'"
  by (meson subsetD unrep_ids_subset assms)

lemma unrep_preserves_closure:
  assumes "wf_closed g"
  assumes "g \<oplus> e \<leadsto> (g', n)"
  shows "wf_closed g'"
  using assms(2,1) wf_closed_def
  proof (induction g e "(g', n)" arbitrary: g' n)
    case (ConstantNodeSame g c n)
    then show ?case
      by simp
  next
    case (ConstantNodeNew g c n g')
    then have dom: "ids g' = ids g \<union> {n}"
      by (meson IRNode.distinct(1041) add_node_ids_subset ids_add_update)
    have k: "kind g' n = ConstantNode c"
      by (simp add: add_node_lookup ConstantNodeNew)
    then have inp: "{} = inputs g' n"
      by simp
    from k have suc: "{} = succ g' n"
      by simp
    have "inputs g' n \<subseteq> ids g' \<and> succ g' n \<subseteq> ids g' \<and> kind g' n \<noteq> NoNode"
      by (simp add: k)
    then show ?case
      by (smt (verit) ConstantNodeNew.hyps(3) ConstantNodeNew.prems Un_insert_right add_changed dom
          changeonly.elims(2) insert_iff singleton_iff subset_insertI subset_trans sup_bot_right
          succ.simps inputs.simps)
  next
    case (ParameterNodeSame g i s n)
    then show ?case 
      by simp
  next
    case (ParameterNodeNew g i s n g')
    then have dom: "ids g' = ids g \<union> {n}"
      by (meson IRNode.distinct(3523) add_node_ids_subset ids_add_update)
    have k: "kind g' n = ParameterNode i"
      by (simp add: add_node_lookup ParameterNodeNew)
    then have inp: "{} = inputs g' n"
      by simp
    from k have suc: "{} = succ g' n"
      by simp
    have "inputs g' n \<subseteq> ids g' \<and> succ g' n \<subseteq> ids g' \<and> kind g' n \<noteq> NoNode"
      by (simp add: k)
    then show ?case
      by (smt (verit) ParameterNodeNew.hyps(3) ParameterNodeNew.prems Un_insert_right sup_bot_right
          add_node_as_set dom inputs.elims insertE not_excluded_keep_type order_trans singletonD 
          subset_insertI succ.elims)
  next
    case (ConditionalNodeSame g ce g2 c te g3 t fe g4 f s' n)
    then show ?case 
      by simp
  next
    case (ConditionalNodeNew g4 c t f s' g ce g2 te g3 fe n g')
    then have dom: "ids g' = ids g4 \<union> {n}"
      by (meson IRNode.distinct(933) add_node_ids_subset ids_add_update)
    have k: "kind g' n = ConditionalNode c t f"
      by (auto simp add: find_new_kind ConditionalNodeNew.hyps(10))
    then have inp: "{c, t, f} = inputs g' n"
      by simp
    from k have suc: "{} = succ g' n"
      by simp
    have "inputs g' n \<subseteq> ids g' \<and> succ g' n \<subseteq> ids g' \<and> kind g' n \<noteq> NoNode"
      by (metis (mono_tags, lifting) ConditionalNodeNew.hyps(2,4,6) IRNode.distinct(933) insertCI k
          Un_empty_right Un_insert_right dom empty_subsetI in_mono insert_subsetI unrep_contains
          unrep_ids_subset inp suc)
    then show ?case 
      by (smt (z3) dom ConditionalNodeNew.hyps ConditionalNodeNew.prems Diff_eq_empty_iff Diff_iff 
          Un_insert_right Un_upper1 add_node_def inputs.simps insertE replace_node_def succ.simps
          replace_node_unchanged subset_trans sup_bot_right)
  next
    case (UnaryNodeSame g xe g2 x s' op n)
    then show ?case 
      by simp
  next
    case (UnaryNodeNew g2 op x s' g xe n g')
    then have dom: "ids g' = ids g2 \<union> {n}"
      by (metis add_node_ids_subset add_node_lookup ids_add_update ids_some unrep.UnaryNodeNew 
          unrep_contains)
    have k: "kind g' n = unary_node op x"
      by (metis fresh_ids ids_some add_node_lookup UnaryNodeNew(5,6))
    then have inp: "{x} = inputs g' n"
      using unary_inputs by simp
    from k have suc: "{} = succ g' n"
      using unary_succ by simp
    have "inputs g' n \<subseteq> ids g' \<and> succ g' n \<subseteq> ids g' \<and> kind g' n \<noteq> NoNode" 
      by (metis Un_upper1 dom empty_subsetI ids_some insert_not_empty insert_subsetI not_in_g_inputs 
          subset_iff UnaryNodeNew(2) unrep_contains suc k inp)
    then show ?case
      by (smt (verit, ccfv_threshold) Un_insert_right UnaryNodeNew.hyps UnaryNodeNew.prems dom
          add_changed succ.simps changeonly.elims(2) inputs.simps insert_iff singleton_iff
          subset_insertI subset_trans sup_bot_right)
  next
    case (BinaryNodeSame g xe g2 x ye g3 y s' op n)
    then show ?case 
      by simp
  next
    case (BinaryNodeNew g3 op x y s' g xe g2 ye n g')
    then have dom: "ids g' = ids g3 \<union> {n}"
      by (metis binary_inputs fresh_ids ids_add_update ids_some insert_not_empty not_in_g_inputs)
    have k: "kind g' n = bin_node op x y"
      by (metis fresh_ids ids_some add_node_lookup BinaryNodeNew(7,8))
    then have inp: "{x, y} = inputs g' n"
      using binary_inputs by simp
    from k have suc: "{} = succ g' n"
      using binary_succ by simp
    have "inputs g' n \<subseteq> ids g' \<and> succ g' n \<subseteq> ids g' \<and> kind g' n \<noteq> NoNode"
      by (metis Un_upper1 dom empty_subsetI ids_some insert_not_empty insert_subsetI not_in_g_inputs 
          subset_iff BinaryNodeNew(2,4) unrep_preserves_contains k inp suc unrep_contains)
    then show ?case 
      by (smt (verit, del_insts) dom BinaryNodeNew Diff_eq_empty_iff Un_insert_right sup_bot_right
          add_node_def inputs.simps succ.simps replace_node_def replace_node_unchanged subset_trans
          insertE Diff_iff Un_upper1)
  next
    case (AllLeafNodes g n s)
    then show ?case
      by simp
  qed

inductive_cases ConstUnrepE: "g \<oplus> (ConstantExpr x) \<leadsto> (g', n)"

definition constant_value where
  "constant_value = (IntVal 32 0)"
definition bad_graph where
  "bad_graph = irgraph [
    (0, AbsNode 1, constantAsStamp constant_value),
    (1, RefNode 2, constantAsStamp constant_value),
    (2, ConstantNode constant_value, constantAsStamp constant_value)
  ]"

(*
experiment begin
lemma
  assumes "maximal_sharing g"
  assumes "wf_closed g"
  assumes "kind g y = AbsNode y'"
  assumes "kind g y' = RefNode y''"
  assumes "kind g y'' = ConstantNode v"
  assumes "stamp g y'' = constantAsStamp v"
  assumes "g \<oplus> (UnaryExpr UnaryAbs (ConstantExpr v)) \<leadsto> (g', n)" (is "g \<oplus> ?e \<leadsto> (g', n)")
  shows "\<not>(maximal_sharing g')"
  using assms(3,2,1)
proof -
  have "y'' \<in> ids g"
    using assms(5) by simp
  then have "List.member (sorted_list_of_set (ids g)) y''"
    by (metis member_def unwrap_sorted)
  then have "find (\<lambda>i. kind g i = ConstantNode v \<and> stamp g i = constantAsStamp v) (sorted_list_of_set (ids g)) = Some y''"
    using assms(5,6) find_Some_iff sorry
  then have "g \<oplus> ConstantExpr v \<leadsto> (g, y'')"
    using assms(5) ConstUnrepE sorry
  then show ?thesis sorry
qed
end

lemma conditional_rep_kind:
  assumes "g \<turnstile> n \<simeq> ConditionalExpr ce te fe"
  assumes "g \<turnstile> c \<simeq> ce"
  assumes "g \<turnstile> t \<simeq> te"
  assumes "g \<turnstile> f \<simeq> fe"
  assumes "\<not>(\<exists>n'. kind g n = RefNode n')"
  shows "kind g n = ConditionalNode c t f"
  using assms apply (induction n "ConditionalExpr ce te fe" rule: rep.induct) defer
  apply meson using repDet sorry

lemma unary_rep_kind:
  assumes "g \<turnstile> n \<simeq> UnaryExpr op xe"
  assumes "g \<turnstile> x \<simeq> xe"
  assumes "\<not>(\<exists>n'. kind g n = RefNode n')"
  shows "kind g n = unary_node op x"
  using assms apply (cases op) using AbsNodeE sorry

lemma binary_rep_kind:
  assumes "g \<turnstile> n \<simeq> BinaryExpr op xe ye"
  assumes "g \<turnstile> x \<simeq> xe"
  assumes "g \<turnstile> y \<simeq> ye"
  assumes "\<not>(\<exists>n'. kind g n = RefNode n')"
  shows "kind g n = bin_node op x y"
  using assms sorry

theorem unrep_maximal_sharing:
  assumes "maximal_sharing g"
  assumes "wf_closed g"
  assumes "g \<oplus> e \<leadsto> (g', n)"
  shows "maximal_sharing g'"
  using assms(3,2,1)
  proof (induction g e "(g', n)" arbitrary: g' n)
    case (ConstantNodeSame g c n)
    then show ?case by blast
  next
    case (ConstantNodeNew g c n g')
    then have "kind g' n = ConstantNode c"
      using find_new_kind by blast
    then have repn: "g' \<turnstile> n \<simeq> ConstantExpr c"
      using rep.ConstantNode by simp
    from ConstantNodeNew have real_node: "\<not>(is_RefNode (ConstantNode c)) \<and> ConstantNode c \<noteq> NoNode"
      by simp                       
    then have dom: "true_ids g' = true_ids g \<union> {n}"
      using ConstantNodeNew.hyps(2) ConstantNodeNew.hyps(3) fresh_ids
      by (meson true_ids_add_update)
    have new: "n \<notin> ids g"
      using fresh_ids
      using ConstantNodeNew.hyps(2) by blast
    obtain new where "new = true_ids g' - true_ids g"
      by simp
    then have new_def: "new = {n}"
      by (metis (no_types, lifting) DiffE Diff_cancel IRGraph.true_ids_def Un_insert_right dom insert_Diff_if new sup_bot_right)
    then have unchanged: "(new \<unlhd> as_set g') = as_set g"
      using ConstantNodeNew(3) new add_node_as_set_eq
      by presburger
    then have kind_eq: "\<forall>n' . n' \<notin> new \<longrightarrow> kind g n' = kind g' n'"
      by (metis ConstantNodeNew.hyps(3) \<open>new = {n}\<close> add_node_as_set dual_order.eq_iff not_excluded_keep_type not_in_g)
    from unchanged have stamp_eq: "\<forall>n' \<in> ids g . n' \<notin> new \<longrightarrow> stamp g n' = stamp g' n'"
      using not_excluded_keep_type new_def new
      by (metis ConstantNodeNew.hyps(3) add_node_as_set)
    show ?case unfolding maximal_sharing apply (rule allI; rule allI; rule impI)
      using ConstantNodeNew(5) unfolding maximal_sharing apply auto
      proof -
      fix n\<^sub>1 n\<^sub>2 e
      assume 1: "\<forall>n\<^sub>1 n\<^sub>2.
          n\<^sub>1 \<in> true_ids g \<and> n\<^sub>2 \<in> true_ids g \<longrightarrow>
          (\<exists>e. (g \<turnstile> n\<^sub>1 \<simeq> e) \<and> (g \<turnstile> n\<^sub>2 \<simeq> e) \<and> stamp g n\<^sub>1 = stamp g n\<^sub>2) \<longrightarrow> n\<^sub>1 = n\<^sub>2"
      assume "n\<^sub>1 \<in> true_ids g'"
      assume "n\<^sub>2 \<in> true_ids g'"
      show "g' \<turnstile> n\<^sub>1 \<simeq> e \<Longrightarrow> g' \<turnstile> n\<^sub>2 \<simeq> e \<Longrightarrow> stamp g' n\<^sub>1 = stamp g' n\<^sub>2 \<Longrightarrow> n\<^sub>1 = n\<^sub>2" 
      proof (cases "n\<^sub>1 \<in> true_ids g")
        case n1: True
        then show "g' \<turnstile> n\<^sub>1 \<simeq> e \<Longrightarrow> g' \<turnstile> n\<^sub>2 \<simeq> e \<Longrightarrow> stamp g' n\<^sub>1 = stamp g' n\<^sub>2 \<Longrightarrow> n\<^sub>1 = n\<^sub>2"
        proof (cases "n\<^sub>2 \<in> true_ids g")
          case n2: True
          assume n1rep': "g' \<turnstile> n\<^sub>1 \<simeq> e"
          assume n2rep': "g' \<turnstile> n\<^sub>2 \<simeq> e"
          assume stmp: "stamp g' n\<^sub>1 = stamp g' n\<^sub>2"
          have n1rep: "g \<turnstile> n\<^sub>1 \<simeq> e"
            using n1rep' kind_eq stamp_eq new_def add_preserves_rep
            using ConstantNodeNew.prems(1) IRGraph.true_ids_def n1 unchanged by auto
          have n2rep: "g \<turnstile> n\<^sub>2 \<simeq> e"
            using n2rep' kind_eq stamp_eq new_def add_preserves_rep
            using ConstantNodeNew.prems(1) IRGraph.true_ids_def n2 unchanged by auto
          have "stamp g n\<^sub>1 = stamp g n\<^sub>2"
            by (metis ConstantNodeNew.hyps(3) stmp fresh_node_subset n1rep n2rep new subset_stamp)
          then show ?thesis using 1
            using n1 n2
            using n1rep n2rep by blast
        next
          case n2: False
          assume n1rep': "g' \<turnstile> n\<^sub>1 \<simeq> e"
          assume n2rep': "g' \<turnstile> n\<^sub>2 \<simeq> e"
          assume stmp: "stamp g' n\<^sub>1 = stamp g' n\<^sub>2"
          have n2_def: "n\<^sub>2 = n"
            using \<open>n\<^sub>2 \<in> true_ids g'\<close> dom n2 by auto
          have n1rep: "g \<turnstile> n\<^sub>1 \<simeq> ConstantExpr c"
            by (metis (no_types, lifting) ConstantNodeNew.prems(1) DiffE IRGraph.true_ids_def add_preserves_rep n1 n1rep' n2_def n2rep' repDet repn unchanged)
          then have n1in: "n\<^sub>1 \<in> ids g"
            using no_encoding by metis
          have k: "kind g n\<^sub>1 = ConstantNode c"
            using TreeToGraphThms.true_ids_def n1 n1rep by force
          have s: "stamp g n\<^sub>1 = constantAsStamp c"
            by (metis ConstantNodeNew.hyps(3) real_node n2_def stmp find_new_stamp fresh_node_subset n1rep new subset_stamp)
          from k s show ?thesis
             using find_none ConstantNodeNew.hyps(1) n1in by blast
        qed
      next
        case n1: False
        then show "g' \<turnstile> n\<^sub>1 \<simeq> e \<Longrightarrow> g' \<turnstile> n\<^sub>2 \<simeq> e \<Longrightarrow> stamp g' n\<^sub>1 = stamp g' n\<^sub>2 \<Longrightarrow> n\<^sub>1 = n\<^sub>2"
        proof (cases "n\<^sub>2 \<in> true_ids g")
          case n2: True
          assume n1rep': "g' \<turnstile> n\<^sub>1 \<simeq> e"
          assume n2rep': "g' \<turnstile> n\<^sub>2 \<simeq> e"
          assume stmp: "stamp g' n\<^sub>1 = stamp g' n\<^sub>2"
          have n1_def: "n\<^sub>1 = n"
            using \<open>n\<^sub>1 \<in> true_ids g'\<close> dom n1 by auto
          have n2in: "n\<^sub>2 \<in> ids g"
            using IRGraph.true_ids_def n2 by auto
          have k: "kind g n\<^sub>2 = ConstantNode c"
            by (metis (mono_tags, lifting) ConstantNodeE ConstantNodeNew.prems(1) DiffE IRGraph.true_ids_def add_preserves_rep mem_Collect_eq n1_def n1rep' n2 n2rep' repDet repn unchanged)
          have s: "stamp g n\<^sub>2 = constantAsStamp c"
            by (metis ConstantNodeNew.hyps(3) TreeToGraphThms.new_def add_node_lookup n1_def n2in real_node stamp_eq stmp unchanged)
          from k s show ?thesis
            using find_none ConstantNodeNew.hyps(1) n2in by blast
        next
          case n2: False
          assume n1rep': "g' \<turnstile> n\<^sub>1 \<simeq> e"
          assume n2rep': "g' \<turnstile> n\<^sub>2 \<simeq> e"
          assume "stamp g' n\<^sub>1 = stamp g' n\<^sub>2"
          have "n\<^sub>1 = n \<and> n\<^sub>2 = n"
            using \<open>n\<^sub>1 \<in> true_ids g'\<close> dom n1
            using \<open>n\<^sub>2 \<in> true_ids g'\<close> n2 by blast
          then show ?thesis
            by simp
        qed
      qed
    qed
  next
    case (ParameterNodeSame g i s n)
    then show ?case by blast
  next
    case (ParameterNodeNew g i s n g')
    then have k: "kind g' n = ParameterNode i"
      using find_new_kind by blast
    have "stamp g' n = s"
      using ParameterNodeNew.hyps(3) find_new_stamp by blast
    then have repn: "g' \<turnstile> n \<simeq> ParameterExpr i s"
      using rep.ParameterNode k by simp
    from ConstantNodeNew have "\<not>(is_RefNode (ParameterNode i)) \<and> ParameterNode i \<noteq> NoNode"
      by simp
    then have dom: "true_ids g' = true_ids g \<union> {n}"
      using ParameterNodeNew.hyps(2) ParameterNodeNew.hyps(3) fresh_ids
      by (meson true_ids_add_update)
    have new: "n \<notin> ids g"
      using fresh_ids
      using ParameterNodeNew.hyps(2) by blast
    obtain new where "new = true_ids g' - true_ids g"
      by simp
    then have new_def: "new = {n}"
      by (metis (no_types, lifting) DiffE Diff_cancel IRGraph.true_ids_def Un_insert_right dom insert_Diff_if new sup_bot_right)
    then have unchanged: "(new \<unlhd> as_set g') = as_set g"
      using ParameterNodeNew(3) new add_node_as_set_eq
      by presburger
    then have kind_eq: "\<forall>n' . n' \<notin> new \<longrightarrow> kind g n' = kind g' n'"
      by (metis ParameterNodeNew.hyps(3) \<open>new = {n}\<close> add_node_as_set dual_order.eq_iff not_excluded_keep_type not_in_g)
    from unchanged have stamp_eq: "\<forall>n' \<in> ids g . n' \<notin> new \<longrightarrow> stamp g n' = stamp g' n'"
      using not_excluded_keep_type new_def new
      by (metis ParameterNodeNew.hyps(3) add_node_as_set)
    show ?case unfolding maximal_sharing apply (rule allI; rule allI; rule impI)
      using ParameterNodeNew(5) unfolding maximal_sharing apply auto
      proof -
      fix n\<^sub>1 n\<^sub>2 e
      assume 1: "\<forall>n\<^sub>1 n\<^sub>2.
          n\<^sub>1 \<in> true_ids g \<and> n\<^sub>2 \<in> true_ids g \<longrightarrow>
          (\<exists>e. (g \<turnstile> n\<^sub>1 \<simeq> e) \<and> (g \<turnstile> n\<^sub>2 \<simeq> e) \<and> stamp g n\<^sub>1 = stamp g n\<^sub>2) \<longrightarrow> n\<^sub>1 = n\<^sub>2"
      assume "n\<^sub>1 \<in> true_ids g'"
      assume "n\<^sub>2 \<in> true_ids g'"
      show "g' \<turnstile> n\<^sub>1 \<simeq> e \<Longrightarrow> g' \<turnstile> n\<^sub>2 \<simeq> e \<Longrightarrow> stamp g' n\<^sub>1 = stamp g' n\<^sub>2 \<Longrightarrow> n\<^sub>1 = n\<^sub>2" 
      proof (cases "n\<^sub>1 \<in> true_ids g")
        case n1: True
        then show "g' \<turnstile> n\<^sub>1 \<simeq> e \<Longrightarrow> g' \<turnstile> n\<^sub>2 \<simeq> e \<Longrightarrow> stamp g' n\<^sub>1 = stamp g' n\<^sub>2 \<Longrightarrow> n\<^sub>1 = n\<^sub>2"
        proof (cases "n\<^sub>2 \<in> true_ids g")
          case n2: True
          assume n1rep': "g' \<turnstile> n\<^sub>1 \<simeq> e"
          assume n2rep': "g' \<turnstile> n\<^sub>2 \<simeq> e"
          assume "stamp g' n\<^sub>1 = stamp g' n\<^sub>2"
          have n1rep: "g \<turnstile> n\<^sub>1 \<simeq> e"
            using n1rep' kind_eq stamp_eq new_def add_preserves_rep
            using ParameterNodeNew.prems(1) IRGraph.true_ids_def n1 unchanged by auto
          have n2rep: "g \<turnstile> n\<^sub>2 \<simeq> e"
            using n2rep' kind_eq stamp_eq new_def add_preserves_rep
            using ParameterNodeNew.prems(1) IRGraph.true_ids_def n2 unchanged by auto
          have "stamp g n\<^sub>1 = stamp g n\<^sub>2"
            by (metis ParameterNodeNew.hyps(3) \<open>stamp g' n\<^sub>1 = stamp g' n\<^sub>2\<close> fresh_node_subset n1rep n2rep new subset_stamp)
          then show ?thesis using 1
            using n1 n2
            using n1rep n2rep by blast
        next
          case n2: False
          assume n1rep': "g' \<turnstile> n\<^sub>1 \<simeq> e"
          assume n2rep': "g' \<turnstile> n\<^sub>2 \<simeq> e"
          assume "stamp g' n\<^sub>1 = stamp g' n\<^sub>2"
          have "n\<^sub>2 = n"
            using \<open>n\<^sub>2 \<in> true_ids g'\<close> dom n2 by auto
          then have ne: "n\<^sub>2 \<notin> ids g"
            using new n2 by blast
          have n1rep: "g \<turnstile> n\<^sub>1 \<simeq> e"
            using n1rep' kind_eq stamp_eq new_def add_preserves_rep
            using ParameterNodeNew.prems(1) IRGraph.true_ids_def n1 unchanged by auto
          have n2rep: "g \<turnstile> n\<^sub>2 \<simeq> e"
            using n2rep' kind_eq stamp_eq new_def add_preserves_rep
            using ParameterNodeNew.prems(1) IRGraph.true_ids_def unchanged
            by (metis (no_types, lifting) IRNode.disc(2703) ParameterNodeE ParameterNodeNew.hyps(1) TreeToGraphThms.true_ids_def \<open>n\<^sub>2 = n\<close> find_none mem_Collect_eq n1 n1rep' repDet repn)
          then show ?thesis
            using n2rep not_in_no_rep ne by blast 
        qed
      next
        case n1: False
        then show "g' \<turnstile> n\<^sub>1 \<simeq> e \<Longrightarrow> g' \<turnstile> n\<^sub>2 \<simeq> e \<Longrightarrow> stamp g' n\<^sub>1 = stamp g' n\<^sub>2 \<Longrightarrow> n\<^sub>1 = n\<^sub>2"
        proof (cases "n\<^sub>2 \<in> true_ids g")
          case n2: True
          assume n1rep': "g' \<turnstile> n\<^sub>1 \<simeq> e"
          assume n2rep': "g' \<turnstile> n\<^sub>2 \<simeq> e"
          assume "stamp g' n\<^sub>1 = stamp g' n\<^sub>2"
          have "n\<^sub>1 = n"
            using \<open>n\<^sub>1 \<in> true_ids g'\<close> dom n1 by auto
          then have ne: "n\<^sub>1 \<notin> ids g"
            using new n2 by blast
          have n1rep: "g \<turnstile> n\<^sub>1 \<simeq> e"
            using n1rep' kind_eq stamp_eq new_def add_preserves_rep
            using ParameterNodeNew.prems(1) IRGraph.true_ids_def n1 unchanged
            by (metis (no_types, lifting) IRNode.disc(2703) ParameterNodeE ParameterNodeNew.hyps(1) TreeToGraphThms.true_ids_def \<open>n\<^sub>1 = n\<close> find_none mem_Collect_eq n2 n2rep' repDet repn)
          then show ?thesis
            using n1rep not_in_no_rep ne by blast
        next
          case n2: False
          assume n1rep': "g' \<turnstile> n\<^sub>1 \<simeq> e"
          assume n2rep': "g' \<turnstile> n\<^sub>2 \<simeq> e"
          assume "stamp g' n\<^sub>1 = stamp g' n\<^sub>2"
          have "n\<^sub>1 = n \<and> n\<^sub>2 = n"
            using \<open>n\<^sub>1 \<in> true_ids g'\<close> dom n1
            using \<open>n\<^sub>2 \<in> true_ids g'\<close> n2 by blast
          then show ?thesis
            by simp
        qed
      qed
    qed
  next
    case (ConditionalNodeSame g ce g2 c te g3 t fe g4 f s' n)
    then show ?case
      using unrep_preserves_closure by blast
  next
    case (ConditionalNodeNew g ce g2 c te g3 t fe g4 f s' n g')
    then have k: "kind g' n = ConditionalNode c t f"
      using find_new_kind by blast
    have "stamp g' n = s'"
      using ConditionalNodeNew.hyps(10) IRNode.distinct(591) find_new_stamp by blast
    then have repn: "g' \<turnstile> n \<simeq> ConditionalExpr ce te fe"
      using rep.ConditionalNode k
      by (metis ConditionalNodeNew.hyps(1) ConditionalNodeNew.hyps(10) ConditionalNodeNew.hyps(3) ConditionalNodeNew.hyps(5) ConditionalNodeNew.hyps(9) fresh_ids fresh_node_subset subset_implies_evals term_graph_reconstruction)
    from ConstantNodeNew have "\<not>(is_RefNode (ConditionalNode c t f)) \<and> ConditionalNode c t f \<noteq> NoNode"
      by simp
    then have dom: "true_ids g' = true_ids g4 \<union> {n}"
      using ConditionalNodeNew.hyps(10) ConditionalNodeNew.hyps(9) fresh_ids true_ids_add_update by presburger
    have new: "n \<notin> ids g"
      using fresh_ids
      by (meson ConditionalNodeNew.hyps(1) ConditionalNodeNew.hyps(3) ConditionalNodeNew.hyps(5) ConditionalNodeNew.hyps(9) unrep_preserves_contains)
    obtain new where "new = true_ids g' - true_ids g4"
      by simp
    then have new_def: "new = {n}"
      using dom
      by (metis ConditionalNodeNew.hyps(9) DiffD1 DiffI Diff_cancel Diff_insert Un_insert_right boolean_algebra.disj_zero_right fresh_ids insertCI insert_Diff true_ids)
    then have unchanged: "(new \<unlhd> as_set g') = as_set g4"
      using new add_node_as_set_eq
      using ConditionalNodeNew.hyps(10) ConditionalNodeNew.hyps(9) fresh_ids by presburger
    then have kind_eq: "\<forall>n' . n' \<notin> new \<longrightarrow> kind g4 n' = kind g' n'"
      by (metis ConditionalNodeNew.hyps(10) add_node_as_set equalityE local.new_def not_excluded_keep_type not_in_g)
    from unchanged have stamp_eq: "\<forall>n' \<in> ids g . n' \<notin> new \<longrightarrow> stamp g4 n' = stamp g' n'"
      using not_excluded_keep_type new_def new
      by (metis ConditionalNodeNew.hyps(1) ConditionalNodeNew.hyps(10) ConditionalNodeNew.hyps(3) ConditionalNodeNew.hyps(5) add_node_as_set unrep_preserves_contains)
    have max_g4: "maximal_sharing g4"
      using ConditionalNodeNew.hyps(1) ConditionalNodeNew.hyps(2) ConditionalNodeNew.hyps(3) ConditionalNodeNew.hyps(4) ConditionalNodeNew.hyps(6) ConditionalNodeNew.prems(1) ConditionalNodeNew.prems(2) unrep_preserves_closure by blast
    show ?case unfolding maximal_sharing apply (rule allI; rule allI; rule impI)
      using max_g4 unfolding maximal_sharing apply auto
      proof -
      fix n\<^sub>1 n\<^sub>2 e
      assume 1: "\<forall>n\<^sub>1 n\<^sub>2.
          n\<^sub>1 \<in> true_ids g4 \<and> n\<^sub>2 \<in> true_ids g4 \<longrightarrow>
          (\<exists>e. (g4 \<turnstile> n\<^sub>1 \<simeq> e) \<and> (g4 \<turnstile> n\<^sub>2 \<simeq> e) \<and> stamp g4 n\<^sub>1 = stamp g4 n\<^sub>2) \<longrightarrow> n\<^sub>1 = n\<^sub>2"
      assume "n\<^sub>1 \<in> true_ids g'"
      assume "n\<^sub>2 \<in> true_ids g'"
      show "g' \<turnstile> n\<^sub>1 \<simeq> e \<Longrightarrow> g' \<turnstile> n\<^sub>2 \<simeq> e \<Longrightarrow> stamp g' n\<^sub>1 = stamp g' n\<^sub>2 \<Longrightarrow> n\<^sub>1 = n\<^sub>2" 
      proof (cases "n\<^sub>1 \<in> true_ids g4")
        case n1: True
        then show "g' \<turnstile> n\<^sub>1 \<simeq> e \<Longrightarrow> g' \<turnstile> n\<^sub>2 \<simeq> e \<Longrightarrow> stamp g' n\<^sub>1 = stamp g' n\<^sub>2 \<Longrightarrow> n\<^sub>1 = n\<^sub>2"
        proof (cases "n\<^sub>2 \<in> true_ids g4")
          case n2: True
          assume n1rep': "g' \<turnstile> n\<^sub>1 \<simeq> e"
          assume n2rep': "g' \<turnstile> n\<^sub>2 \<simeq> e"
          assume "stamp g' n\<^sub>1 = stamp g' n\<^sub>2"
          have n1rep: "g4 \<turnstile> n\<^sub>1 \<simeq> e"
            using n1rep' kind_eq stamp_eq new_def add_preserves_rep
            using ConditionalNodeNew.prems(1) IRGraph.true_ids_def n1 unchanged
            by (metis (mono_tags, lifting) ConditionalNodeNew.hyps(1) ConditionalNodeNew.hyps(3) ConditionalNodeNew.hyps(5) DiffE unrep_preserves_closure)
          have n2rep: "g4 \<turnstile> n\<^sub>2 \<simeq> e"
            using n2rep' kind_eq stamp_eq new_def add_preserves_rep
            using ConditionalNodeNew.prems(1) IRGraph.true_ids_def n2 unchanged
            by (metis (no_types, lifting) ConditionalNodeNew.hyps(1) ConditionalNodeNew.hyps(3) ConditionalNodeNew.hyps(5) DiffE unrep_preserves_closure)
          have "stamp g4 n\<^sub>1 = stamp g4 n\<^sub>2"
            by (metis ConditionalNodeNew.hyps(10) ConditionalNodeNew.hyps(9) \<open>stamp g' n\<^sub>1 = stamp g' n\<^sub>2\<close> fresh_ids fresh_node_subset n1rep n2rep subset_stamp)
          then show ?thesis using 1
            using n1 n2
            using n1rep n2rep by blast
        next
          case n2: False
          assume n1rep': "g' \<turnstile> n\<^sub>1 \<simeq> e"
          assume n2rep': "g' \<turnstile> n\<^sub>2 \<simeq> e"
          assume stmp: "stamp g' n\<^sub>1 = stamp g' n\<^sub>2"
          have n2_def: "n\<^sub>2 = n"
            using \<open>n\<^sub>2 \<in> true_ids g'\<close> dom n2 by auto
          have n1rep: "g4 \<turnstile> n\<^sub>1 \<simeq> ConditionalExpr ce te fe"
            by (metis (no_types, lifting) ConditionalNodeNew.hyps(1) ConditionalNodeNew.hyps(3) ConditionalNodeNew.hyps(5) ConditionalNodeNew.prems(1) Diff_iff IRGraph.true_ids_def add_preserves_rep n1 n1rep' n2_def n2rep' repDet repn unchanged unrep_preserves_closure)
          then have n1in: "n\<^sub>1 \<in> ids g4"
            using no_encoding by metis
          (*have inputs_true: "c \<in> true_ids g4 \<and> t \<in> true_ids g4 \<and> f \<in> true_ids g4"
            sorry
          have rep: "(g4 \<turnstile> c \<simeq> ce) \<and> (g4 \<turnstile> t \<simeq> te) \<and> (g4 \<turnstile> f \<simeq> fe)"
            by (metis ConditionalNodeNew.hyps(1) ConditionalNodeNew.hyps(3) ConditionalNodeNew.hyps(5) not_in_no_rep term_graph_reconstruction unrep_unchanged)
          have cuni: "\<forall>n' \<in> true_ids g4. (g4 \<turnstile> n' \<simeq> ce) \<and> stamp g4 n' = stamp g4 c \<longrightarrow> n' = c"
            using max_g4 unfolding maximal_sharing using inputs_true
            by (meson local.rep)
          have tuni: "\<forall>n' \<in> true_ids g4. (g4 \<turnstile> n' \<simeq> te) \<and> stamp g4 n' = stamp g4 t \<longrightarrow> n' = t"
            using max_g4 unfolding maximal_sharing using inputs_true
            by (meson local.rep)
          have funi: "\<forall>n' \<in> true_ids g4. (g4 \<turnstile> n' \<simeq> fe) \<and> stamp g4 n' = stamp g4 f \<longrightarrow> n' = f"
            using max_g4 unfolding maximal_sharing using inputs_true
            by (meson local.rep)
          then obtain cx tx fx where k: "kind g4 n\<^sub>1 = ConditionalNode cx tx fx"
            by (metis (mono_tags, lifting) ConditionalNodeE IRNode.discI(51) TreeToGraphThms.true_ids_def mem_Collect_eq n1 n1rep)
          have "c = cx"
            using cuni rep inputs_true sorry
          have s: "stamp g4 n\<^sub>1 = s'"
            by (metis ConditionalNodeNew.hyps(10) ConditionalNodeNew.hyps(9) \<open>stamp g' n = s'\<close> fresh_ids fresh_node_subset n1rep n2_def stmp subset_stamp)*)
          have rep: "(g4 \<turnstile> c \<simeq> ce) \<and> (g4 \<turnstile> t \<simeq> te) \<and> (g4 \<turnstile> f \<simeq> fe)"
            by (meson ConditionalNodeNew.hyps(1) ConditionalNodeNew.hyps(3) ConditionalNodeNew.hyps(5) subset_implies_evals term_graph_reconstruction)
          have not_ref: "\<not>(\<exists>n'. kind g4 n\<^sub>1 = RefNode n')"
            using TreeToGraphThms.true_ids_def n1 by fastforce
          then have "kind g4 n\<^sub>1 = ConditionalNode c t f"
            using conditional_rep_kind
            using local.rep n1rep by presburger
          then show ?thesis
            using find_none ConditionalNodeNew.hyps(8) n1in
            by (metis ConditionalNodeNew.hyps(10) ConditionalNodeNew.hyps(9) \<open>stamp g' n = s'\<close> fresh_ids fresh_node_subset n1rep n2_def stmp subset_stamp)
        qed
      next
        case n1: False
        then show "g' \<turnstile> n\<^sub>1 \<simeq> e \<Longrightarrow> g' \<turnstile> n\<^sub>2 \<simeq> e \<Longrightarrow> stamp g' n\<^sub>1 = stamp g' n\<^sub>2 \<Longrightarrow> n\<^sub>1 = n\<^sub>2"
        proof (cases "n\<^sub>2 \<in> true_ids g4")
          case n2: True
          assume n1rep': "g' \<turnstile> n\<^sub>1 \<simeq> e"
          assume n2rep': "g' \<turnstile> n\<^sub>2 \<simeq> e"
          assume "stamp g' n\<^sub>1 = stamp g' n\<^sub>2"
          have new_n1: "n\<^sub>1 = n"
            using \<open>n\<^sub>1 \<in> true_ids g'\<close> dom n1 by auto
          then have ne: "n\<^sub>1 \<notin> ids g4"
            using new n1
            using ConditionalNodeNew.hyps(9) fresh_ids by blast
          have unrep_cond: "g4 \<turnstile> n\<^sub>2 \<simeq> ConditionalExpr ce te fe"
            using n1rep' kind_eq stamp_eq new_def add_preserves_rep
            using ConditionalNodeNew.prems(1) IRGraph.true_ids_def n2 unchanged
            by (metis (no_types, lifting) ConditionalNodeNew.hyps(1) ConditionalNodeNew.hyps(3) ConditionalNodeNew.hyps(5) DiffD1 n2rep' new_n1 repDet repn unrep_preserves_closure)
          have rep: "(g4 \<turnstile> c \<simeq> ce) \<and> (g4 \<turnstile> t \<simeq> te) \<and> (g4 \<turnstile> f \<simeq> fe)"
            by (meson ConditionalNodeNew.hyps(1) ConditionalNodeNew.hyps(3) ConditionalNodeNew.hyps(5) subset_implies_evals term_graph_reconstruction)
          have not_ref: "\<not>(\<exists>n'. kind g4 n\<^sub>2 = RefNode n')"
            using TreeToGraphThms.true_ids_def n2 by fastforce
          then have "kind g4 n\<^sub>2 = ConditionalNode c t f"
            using conditional_rep_kind
            using local.rep unrep_cond by presburger
          then show ?thesis using find_none ConditionalNodeNew.hyps(8)
            by (metis ConditionalNodeNew.hyps(10) \<open>stamp g' n = s'\<close> \<open>stamp g' n\<^sub>1 = stamp g' n\<^sub>2\<close> encodes_contains fresh_node_subset ne new_n1 not_in_g subset_stamp unrep_cond)
        next
          case n2: False
          assume n1rep': "g' \<turnstile> n\<^sub>1 \<simeq> e"
          assume n2rep': "g' \<turnstile> n\<^sub>2 \<simeq> e"
          assume "stamp g' n\<^sub>1 = stamp g' n\<^sub>2"
          have "n\<^sub>1 = n \<and> n\<^sub>2 = n"
            using \<open>n\<^sub>1 \<in> true_ids g'\<close> dom n1
            using \<open>n\<^sub>2 \<in> true_ids g'\<close> n2
            by simp
          then show ?thesis
            by simp
        qed
      qed
    qed
  next
    case (UnaryNodeSame g xe g2 x s' op n)
    then show ?case by blast
  next
    case (UnaryNodeNew g xe g2 x s' op n g')
    then have k: "kind g' n = unary_node op x"
      using find_new_kind
      by (metis add_node_lookup fresh_ids ids_some)
    have "stamp g' n = s'"
      by (metis UnaryNodeNew.hyps(6) empty_iff find_new_stamp ids_some insertI1 k not_in_g_inputs unary_inputs)
    then have repn: "g' \<turnstile> n \<simeq> UnaryExpr op xe"
      using k
      using UnaryNodeNew.hyps(1) UnaryNodeNew.hyps(3) UnaryNodeNew.hyps(4) UnaryNodeNew.hyps(5) UnaryNodeNew.hyps(6) term_graph_reconstruction unrep.UnaryNodeNew by blast
    from ConstantNodeNew have "\<not>(is_RefNode (unary_node op x)) \<and> unary_node op x \<noteq> NoNode"
      by (cases op; auto)
    then have dom: "true_ids g' = true_ids g2 \<union> {n}"
      using UnaryNodeNew.hyps(5) UnaryNodeNew.hyps(6) fresh_ids true_ids_add_update by presburger
    have new: "n \<notin> ids g"
      using fresh_ids
      by (meson UnaryNodeNew.hyps(1) UnaryNodeNew.hyps(5) unrep_preserves_contains)
    obtain new where "new = true_ids g' - true_ids g2"
      by simp
    then have new_def: "new = {n}"
      using dom
      by (metis Diff_cancel Diff_iff Un_insert_right UnaryNodeNew.hyps(5) fresh_ids insert_Diff_if sup_bot.right_neutral true_ids)
    then have unchanged: "(new \<unlhd> as_set g') = as_set g2"
      using new add_node_as_set_eq
      using UnaryNodeNew.hyps(5) UnaryNodeNew.hyps(6) fresh_ids by presburger
    then have kind_eq: "\<forall>n' . n' \<notin> new \<longrightarrow> kind g2 n' = kind g' n'"
      by (metis UnaryNodeNew.hyps(6) add_node_as_set equalityD1 local.new_def not_excluded_keep_type not_in_g)
    from unchanged have stamp_eq: "\<forall>n' \<in> ids g . n' \<notin> new \<longrightarrow> stamp g2 n' = stamp g' n'"
      using not_excluded_keep_type new_def new
      by (metis UnaryNodeNew.hyps(1) UnaryNodeNew.hyps(6) add_node_as_set unrep_preserves_contains)
    have max_g2: "maximal_sharing g2"
      by (simp add: UnaryNodeNew.hyps(2) UnaryNodeNew.prems(1) UnaryNodeNew.prems(2))
    show ?case unfolding maximal_sharing apply (rule allI; rule allI; rule impI)
      using max_g2 unfolding maximal_sharing apply auto
      proof -
      fix n\<^sub>1 n\<^sub>2 e
      assume 1: "\<forall>n\<^sub>1 n\<^sub>2.
          n\<^sub>1 \<in> true_ids g2 \<and> n\<^sub>2 \<in> true_ids g2 \<longrightarrow>
          (\<exists>e. (g2 \<turnstile> n\<^sub>1 \<simeq> e) \<and> (g2 \<turnstile> n\<^sub>2 \<simeq> e) \<and> stamp g2 n\<^sub>1 = stamp g2 n\<^sub>2) \<longrightarrow> n\<^sub>1 = n\<^sub>2"
      assume "n\<^sub>1 \<in> true_ids g'"
      assume "n\<^sub>2 \<in> true_ids g'"
      show "g' \<turnstile> n\<^sub>1 \<simeq> e \<Longrightarrow> g' \<turnstile> n\<^sub>2 \<simeq> e \<Longrightarrow> stamp g' n\<^sub>1 = stamp g' n\<^sub>2 \<Longrightarrow> n\<^sub>1 = n\<^sub>2" 
      proof (cases "n\<^sub>1 \<in> true_ids g2")
        case n1: True
        then show "g' \<turnstile> n\<^sub>1 \<simeq> e \<Longrightarrow> g' \<turnstile> n\<^sub>2 \<simeq> e \<Longrightarrow> stamp g' n\<^sub>1 = stamp g' n\<^sub>2 \<Longrightarrow> n\<^sub>1 = n\<^sub>2"
        proof (cases "n\<^sub>2 \<in> true_ids g2")
          case n2: True
          assume n1rep': "g' \<turnstile> n\<^sub>1 \<simeq> e"
          assume n2rep': "g' \<turnstile> n\<^sub>2 \<simeq> e"
          assume "stamp g' n\<^sub>1 = stamp g' n\<^sub>2"
          have n1rep: "g2 \<turnstile> n\<^sub>1 \<simeq> e"
            using n1rep' kind_eq stamp_eq new_def add_preserves_rep
            using Diff_iff IRGraph.true_ids_def UnaryNodeNew.hyps(1) UnaryNodeNew.prems(1) n1 unchanged unrep_preserves_closure by auto
          have n2rep: "g2 \<turnstile> n\<^sub>2 \<simeq> e"
            using n2rep' kind_eq stamp_eq new_def add_preserves_rep
            by (metis (no_types, lifting) Diff_iff IRGraph.true_ids_def UnaryNodeNew.hyps(1) UnaryNodeNew.prems(1) n2 unchanged unrep_preserves_closure)
          have "stamp g2 n\<^sub>1 = stamp g2 n\<^sub>2"
            by (metis UnaryNodeNew.hyps(5) UnaryNodeNew.hyps(6) \<open>stamp g' n\<^sub>1 = stamp g' n\<^sub>2\<close> fresh_ids fresh_node_subset n1rep n2rep subset_stamp)
          then show ?thesis using 1
            using n1 n2
            using n1rep n2rep by blast
        next
          case n2: False
          assume n1rep': "g' \<turnstile> n\<^sub>1 \<simeq> e"
          assume n2rep': "g' \<turnstile> n\<^sub>2 \<simeq> e"
          assume "stamp g' n\<^sub>1 = stamp g' n\<^sub>2"
          have new_n2: "n\<^sub>2 = n"
            using \<open>n\<^sub>2 \<in> true_ids g'\<close> dom n2 by auto
          then have ne: "n\<^sub>2 \<notin> ids g2"
            using new n2
            using UnaryNodeNew.hyps(5) fresh_ids by blast
          have unrep_un: "g2 \<turnstile> n\<^sub>1 \<simeq> UnaryExpr op xe"
            using n1rep' kind_eq stamp_eq new_def add_preserves_rep
            by (metis (no_types, lifting) Diff_iff IRGraph.true_ids_def UnaryNodeNew.hyps(1) UnaryNodeNew.prems(1) n1 n2rep' new_n2 repDet repn unchanged unrep_preserves_closure)
          have rep: "(g2 \<turnstile> x \<simeq> xe)"
            using UnaryNodeNew.hyps(1) term_graph_reconstruction by auto
          have not_ref: "\<not>(\<exists>n'. kind g2 n\<^sub>1 = RefNode n')"
            using TreeToGraphThms.true_ids_def n1 by force
          then have "kind g2 n\<^sub>1 = unary_node op x"
            using unrep_un unary_rep_kind rep by simp
            (*apply (frule ConditionalNodeE[where ?g = g4 and ?n = n\<^sub>1 and ?ce = ce and ?te = te and ?fe = fe])*)
          then show ?thesis using find_none UnaryNodeNew.hyps(4)
            by (metis UnaryNodeNew.hyps(6) \<open>stamp g' n = s'\<close> \<open>stamp g' n\<^sub>1 = stamp g' n\<^sub>2\<close> fresh_node_subset ne new_n2 no_encoding subset_stamp unrep_un)
        qed
      next
        case n1: False
        then show "g' \<turnstile> n\<^sub>1 \<simeq> e \<Longrightarrow> g' \<turnstile> n\<^sub>2 \<simeq> e \<Longrightarrow> stamp g' n\<^sub>1 = stamp g' n\<^sub>2 \<Longrightarrow> n\<^sub>1 = n\<^sub>2"
        proof (cases "n\<^sub>2 \<in> true_ids g2")
          case n2: True
          assume n1rep': "g' \<turnstile> n\<^sub>1 \<simeq> e"
          assume n2rep': "g' \<turnstile> n\<^sub>2 \<simeq> e"
          assume "stamp g' n\<^sub>1 = stamp g' n\<^sub>2"
          have new_n1: "n\<^sub>1 = n"
            using \<open>n\<^sub>1 \<in> true_ids g'\<close> dom n1 by auto
          then have ne: "n\<^sub>1 \<notin> ids g2"
            using new n1
            using UnaryNodeNew.hyps(5) fresh_ids by blast
          have unrep_un: "g2 \<turnstile> n\<^sub>2 \<simeq> UnaryExpr op xe"
            using n1rep' kind_eq stamp_eq new_def add_preserves_rep
            by (metis (no_types, lifting) Diff_iff IRGraph.true_ids_def UnaryNodeNew.hyps(1) UnaryNodeNew.prems(1) n2 n2rep' new_n1 repDet repn unchanged unrep_preserves_closure)
          have rep: "(g2 \<turnstile> x \<simeq> xe)"
            using UnaryNodeNew.hyps(1) term_graph_reconstruction by presburger
          have not_ref: "\<not>(\<exists>n'. kind g2 n\<^sub>2 = RefNode n')"
            using TreeToGraphThms.true_ids_def n2 by fastforce
          then have "kind g2 n\<^sub>2 = unary_node op x"
            using unary_rep_kind
            using local.rep unrep_un by presburger
          then show ?thesis using find_none UnaryNodeNew.hyps(4)
            by (metis UnaryNodeNew.hyps(6) \<open>stamp g' n = s'\<close> \<open>stamp g' n\<^sub>1 = stamp g' n\<^sub>2\<close> fresh_node_subset ne new_n1 no_encoding subset_stamp unrep_un)
        next
          case n2: False
          assume n1rep': "g' \<turnstile> n\<^sub>1 \<simeq> e"
          assume n2rep': "g' \<turnstile> n\<^sub>2 \<simeq> e"
          assume "stamp g' n\<^sub>1 = stamp g' n\<^sub>2"
          have "n\<^sub>1 = n \<and> n\<^sub>2 = n"
            using \<open>n\<^sub>1 \<in> true_ids g'\<close> dom n1
            using \<open>n\<^sub>2 \<in> true_ids g'\<close> n2
            by simp
          then show ?thesis
            by simp
        qed
      qed
    qed
  next
    case (BinaryNodeSame g xe g2 x ye g3 y s' op n)
    then show ?case
      using unrep_preserves_closure by blast
  next
    case (BinaryNodeNew g xe g2 x ye g3 y s' op n g')
    then have k: "kind g' n = bin_node op x y"
      using find_new_kind
      by (metis add_node_lookup fresh_ids ids_some)
    have "stamp g' n = s'"
      by (metis BinaryNodeNew.hyps(1) BinaryNodeNew.hyps(3) BinaryNodeNew.hyps(5) BinaryNodeNew.hyps(6) BinaryNodeNew.hyps(7) BinaryNodeNew.hyps(8) find_new_stamp ids_some k unrep.BinaryNodeNew unrep_contains)
    then have repn: "g' \<turnstile> n \<simeq> BinaryExpr op xe ye"
      using k
      using BinaryNodeNew.hyps(1) BinaryNodeNew.hyps(3) BinaryNodeNew.hyps(5) BinaryNodeNew.hyps(6) BinaryNodeNew.hyps(7) BinaryNodeNew.hyps(8) term_graph_reconstruction unrep.BinaryNodeNew by blast
    from BinaryNodeNew have "\<not>(is_RefNode (bin_node op x y)) \<and> bin_node op x y \<noteq> NoNode"
      by (cases op; auto) (* slow *)
    then have dom: "true_ids g' = true_ids g3 \<union> {n}"
      using BinaryNodeNew.hyps(7) BinaryNodeNew.hyps(8) fresh_ids true_ids_add_update by presburger
    have new: "n \<notin> ids g"
      using fresh_ids
      by (meson BinaryNodeNew.hyps(1) BinaryNodeNew.hyps(3) BinaryNodeNew.hyps(7) unrep_preserves_contains)
    obtain new where "new = true_ids g' - true_ids g3"
      by simp
    then have new_def: "new = {n}"
      using dom
      by (metis BinaryNodeNew.hyps(7) Diff_cancel Diff_iff Un_insert_right fresh_ids insert_Diff_if sup_bot.right_neutral true_ids)
    then have unchanged: "(new \<unlhd> as_set g') = as_set g3"
      using new add_node_as_set_eq
      using BinaryNodeNew.hyps(7) BinaryNodeNew.hyps(8) fresh_ids by presburger
    then have kind_eq: "\<forall>n' . n' \<notin> new \<longrightarrow> kind g3 n' = kind g' n'"
      by (metis BinaryNodeNew.hyps(8) add_node_as_set equalityD1 local.new_def not_excluded_keep_type not_in_g)
    from unchanged have stamp_eq: "\<forall>n' \<in> ids g . n' \<notin> new \<longrightarrow> stamp g3 n' = stamp g' n'"
      using not_excluded_keep_type new_def new
      by (metis BinaryNodeNew.hyps(1) BinaryNodeNew.hyps(3) BinaryNodeNew.hyps(8) add_node_as_set unrep_preserves_contains)
    have max_g3: "maximal_sharing g3"
      using BinaryNodeNew.hyps(1) BinaryNodeNew.hyps(2) BinaryNodeNew.hyps(4) BinaryNodeNew.prems(1) BinaryNodeNew.prems(2) unrep_preserves_closure by blast
    show ?case unfolding maximal_sharing apply (rule allI; rule allI; rule impI)
      using max_g3 unfolding maximal_sharing apply auto
      proof -
      fix n\<^sub>1 n\<^sub>2 e
      assume 1: "\<forall>n\<^sub>1 n\<^sub>2.
          n\<^sub>1 \<in> true_ids g3 \<and> n\<^sub>2 \<in> true_ids g3 \<longrightarrow>
          (\<exists>e. (g3 \<turnstile> n\<^sub>1 \<simeq> e) \<and> (g3 \<turnstile> n\<^sub>2 \<simeq> e) \<and> stamp g3 n\<^sub>1 = stamp g3 n\<^sub>2) \<longrightarrow> n\<^sub>1 = n\<^sub>2"
      assume "n\<^sub>1 \<in> true_ids g'"
      assume "n\<^sub>2 \<in> true_ids g'"
      show "g' \<turnstile> n\<^sub>1 \<simeq> e \<Longrightarrow> g' \<turnstile> n\<^sub>2 \<simeq> e \<Longrightarrow> stamp g' n\<^sub>1 = stamp g' n\<^sub>2 \<Longrightarrow> n\<^sub>1 = n\<^sub>2" 
      proof (cases "n\<^sub>1 \<in> true_ids g3")
        case n1: True
        then show "g' \<turnstile> n\<^sub>1 \<simeq> e \<Longrightarrow> g' \<turnstile> n\<^sub>2 \<simeq> e \<Longrightarrow> stamp g' n\<^sub>1 = stamp g' n\<^sub>2 \<Longrightarrow> n\<^sub>1 = n\<^sub>2"
        proof (cases "n\<^sub>2 \<in> true_ids g3")
          case n2: True
          assume n1rep': "g' \<turnstile> n\<^sub>1 \<simeq> e"
          assume n2rep': "g' \<turnstile> n\<^sub>2 \<simeq> e"
          assume "stamp g' n\<^sub>1 = stamp g' n\<^sub>2"
          have n1rep: "g3 \<turnstile> n\<^sub>1 \<simeq> e"
            using n1rep' kind_eq stamp_eq new_def add_preserves_rep
            by (metis (no_types, lifting) BinaryNodeNew.hyps(1) BinaryNodeNew.hyps(3) BinaryNodeNew.prems(1) Diff_iff IRGraph.true_ids_def n1 unchanged unrep_preserves_closure)
          have n2rep: "g3 \<turnstile> n\<^sub>2 \<simeq> e"
            using n2rep' kind_eq stamp_eq new_def add_preserves_rep
            by (metis BinaryNodeNew.hyps(1) BinaryNodeNew.hyps(3) BinaryNodeNew.prems(1) DiffE n2 true_ids unchanged unrep_preserves_closure)
          have "stamp g3 n\<^sub>1 = stamp g3 n\<^sub>2"
            by (metis BinaryNodeNew.hyps(7) BinaryNodeNew.hyps(8) \<open>stamp g' n\<^sub>1 = stamp g' n\<^sub>2\<close> fresh_ids fresh_node_subset n1rep n2rep subset_stamp)
          then show ?thesis using 1
            using n1 n2
            using n1rep n2rep by blast
        next
          case n2: False
          assume n1rep': "g' \<turnstile> n\<^sub>1 \<simeq> e"
          assume n2rep': "g' \<turnstile> n\<^sub>2 \<simeq> e"
          assume "stamp g' n\<^sub>1 = stamp g' n\<^sub>2"
          have new_n2: "n\<^sub>2 = n"
            using \<open>n\<^sub>2 \<in> true_ids g'\<close> dom n2 by auto
          then have ne: "n\<^sub>2 \<notin> ids g3"
            using new n2
            using BinaryNodeNew.hyps(7) fresh_ids by presburger
          have unrep_bin: "g3 \<turnstile> n\<^sub>1 \<simeq> BinaryExpr op xe ye"
            using n1rep' kind_eq stamp_eq new_def add_preserves_rep
            by (metis BinaryNodeNew.hyps(1) BinaryNodeNew.hyps(3) BinaryNodeNew.prems(1) DiffE \<open>new = true_ids g' - true_ids g3\<close> encodes_contains ids_some n1 n2rep' new_n2 repDet repn unchanged unrep_preserves_closure)
          have rep: "(g3 \<turnstile> x \<simeq> xe) \<and> (g3 \<turnstile> y \<simeq> ye)"
            by (meson BinaryNodeNew.hyps(1) BinaryNodeNew.hyps(3) term_graph_reconstruction unrep_contains unrep_unchanged)
          have not_ref: "\<not>(\<exists>n'. kind g3 n\<^sub>1 = RefNode n')"
            using TreeToGraphThms.true_ids_def n1 by force
          then have "kind g3 n\<^sub>1 = bin_node op x y"
            using unrep_bin binary_rep_kind rep by simp
          then show ?thesis using find_none BinaryNodeNew.hyps(6)
            by (metis BinaryNodeNew.hyps(8) \<open>stamp g' n = s'\<close> \<open>stamp g' n\<^sub>1 = stamp g' n\<^sub>2\<close> fresh_node_subset ne new_n2 no_encoding subset_stamp unrep_bin)
        qed
      next
        case n1: False
        then show "g' \<turnstile> n\<^sub>1 \<simeq> e \<Longrightarrow> g' \<turnstile> n\<^sub>2 \<simeq> e \<Longrightarrow> stamp g' n\<^sub>1 = stamp g' n\<^sub>2 \<Longrightarrow> n\<^sub>1 = n\<^sub>2"
        proof (cases "n\<^sub>2 \<in> true_ids g3")
          case n2: True
          assume n1rep': "g' \<turnstile> n\<^sub>1 \<simeq> e"
          assume n2rep': "g' \<turnstile> n\<^sub>2 \<simeq> e"
          assume "stamp g' n\<^sub>1 = stamp g' n\<^sub>2"
          have new_n1: "n\<^sub>1 = n"
            using \<open>n\<^sub>1 \<in> true_ids g'\<close> dom n1 by auto
          then have ne: "n\<^sub>1 \<notin> ids g3"
            using new n1
            using BinaryNodeNew.hyps(7) fresh_ids by blast
          have unrep_bin: "g3 \<turnstile> n\<^sub>2 \<simeq> BinaryExpr op xe ye"
            using n1rep' kind_eq stamp_eq new_def add_preserves_rep
            by (metis (mono_tags, lifting) BinaryNodeNew.hyps(1) BinaryNodeNew.hyps(3) BinaryNodeNew.prems(1) Diff_iff IRGraph.true_ids_def n2 n2rep' new_n1 repDet repn unchanged unrep_preserves_closure)
          have rep: "(g3 \<turnstile> x \<simeq> xe) \<and> (g3 \<turnstile> y \<simeq> ye)"
            using BinaryNodeNew.hyps(1) BinaryNodeNew.hyps(3) term_graph_reconstruction unrep_contains unrep_unchanged by blast
          have not_ref: "\<not>(\<exists>n'. kind g3 n\<^sub>2 = RefNode n')"
            using TreeToGraphThms.true_ids_def n2 by fastforce
          then have "kind g3 n\<^sub>2 = bin_node op x y"
            using unrep_bin binary_rep_kind rep by simp
          then show ?thesis using find_none BinaryNodeNew.hyps(6)
            by (metis BinaryNodeNew.hyps(8) \<open>stamp g' n = s'\<close> \<open>stamp g' n\<^sub>1 = stamp g' n\<^sub>2\<close> fresh_node_subset ne new_n1 no_encoding subset_stamp unrep_bin)
        next
          case n2: False
          assume n1rep': "g' \<turnstile> n\<^sub>1 \<simeq> e"
          assume n2rep': "g' \<turnstile> n\<^sub>2 \<simeq> e"
          assume "stamp g' n\<^sub>1 = stamp g' n\<^sub>2"
          have "n\<^sub>1 = n \<and> n\<^sub>2 = n"
            using \<open>n\<^sub>1 \<in> true_ids g'\<close> dom n1
            using \<open>n\<^sub>2 \<in> true_ids g'\<close> n2
            by simp
          then show ?thesis
            by simp
        qed
      qed
    qed
  next
    case (AllLeafNodes g n s)
    then show ?case by blast
  qed
*)

end
