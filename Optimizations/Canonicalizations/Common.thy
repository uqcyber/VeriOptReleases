section \<open>Canonicalization Optimizations\<close>

theory Common
  imports 
    OptimizationDSL.Canonicalization
    Semantics.IRTreeEvalThms
begin

lemma size_pos[size_simps]: "0 < size y"
  apply (induction y; auto?)
  by (smt (z3) One_nat_def gr0I n_not_Suc_n pos2 size.elims trans_less_add2)

lemma size_non_add[size_simps]: "size (BinaryExpr op a b) = size a + size b + 2 \<longleftrightarrow> \<not>(is_ConstantExpr b)"
  by (induction b; induction op; auto simp: is_ConstantExpr_def)

lemma size_non_const[size_simps]:
  "\<not> is_ConstantExpr y \<Longrightarrow> 1 < size y"
  using size_pos apply (induction y; auto)
  by (metis Suc_lessI add_is_1 is_ConstantExpr_def le_less linorder_not_le n_not_Suc_n numeral_2_eq_2 pos2 size.simps(2) size_non_add)

lemma size_binary_const[size_simps]:
  "size (BinaryExpr op a b) = size a + 2 \<longleftrightarrow> (is_ConstantExpr b)"
  by (induction b; auto simp: is_ConstantExpr_def size_pos)

lemma size_flip_binary[size_simps]:
  "\<not>(is_ConstantExpr y) \<longrightarrow> size (BinaryExpr op (ConstantExpr x) y) > size (BinaryExpr op y (ConstantExpr x))"
  by (metis add_Suc not_less_eq order_less_asym plus_1_eq_Suc size.simps(2,11) size_non_add)

lemma size_binary_lhs_a[size_simps]:
  "size (BinaryExpr op (BinaryExpr op' a b) c) > size a"
  by (metis add_lessD1 less_add_same_cancel1 pos2 size_binary_const size_non_add)

lemma size_binary_lhs_b[size_simps]:
  "size (BinaryExpr op (BinaryExpr op' a b) c) > size b"
  by (metis IRExpr.disc(42) One_nat_def add.left_commute add.right_neutral is_ConstantExpr_def less_add_Suc2 numeral_2_eq_2 plus_1_eq_Suc size.simps(11) size_binary_const size_non_add size_non_const trans_less_add1)

lemma size_binary_lhs_c[size_simps]:
  "size (BinaryExpr op (BinaryExpr op' a b) c) > size c"
  by (metis IRExpr.disc(42) add.left_commute add.right_neutral is_ConstantExpr_def less_Suc_eq numeral_2_eq_2 plus_1_eq_Suc size.simps(11) size_non_add size_non_const trans_less_add2)

lemma size_binary_rhs_a[size_simps]:
  "size (BinaryExpr op c (BinaryExpr op' a b)) > size a"
  apply auto
  by (metis trans_less_add2 less_Suc_eq less_add_same_cancel1 linorder_neqE_nat not_add_less1 pos2
      order_less_trans size_binary_const size_non_add)

lemma size_binary_rhs_b[size_simps]:
  "size (BinaryExpr op c (BinaryExpr op' a b)) > size b"
  by (metis add.left_commute add.right_neutral is_ConstantExpr_def lessI numeral_2_eq_2 plus_1_eq_Suc size.simps(4,11) size_non_add trans_less_add2)

lemma size_binary_rhs_c[size_simps]:
  "size (BinaryExpr op c (BinaryExpr op' a b)) > size c"
  by simp

lemma size_binary_lhs[size_simps]:
  "size (BinaryExpr op x y) > size x"
  by (metis One_nat_def Suc_eq_plus1 add_Suc_right less_add_Suc1 numeral_2_eq_2 size_binary_const size_non_add)

lemma size_binary_rhs[size_simps]:
  "size (BinaryExpr op x y) > size y"
  by (metis IRExpr.disc(42) add_strict_increasing is_ConstantExpr_def linorder_not_le not_add_less1 size.simps(11) size_non_add size_non_const size_pos)

lemmas arith[size_simps] = Suc_leI add_strict_increasing order_less_trans trans_less_add2

definition well_formed_equal :: "Value \<Rightarrow> Value \<Rightarrow> bool" 
  (infix "\<approx>" 50) where
  "well_formed_equal v\<^sub>1 v\<^sub>2 = (v\<^sub>1 \<noteq> UndefVal \<longrightarrow> v\<^sub>1 = v\<^sub>2)"

lemma well_formed_equal_defn [simp]:
  "well_formed_equal v\<^sub>1 v\<^sub>2 = (v\<^sub>1 \<noteq> UndefVal \<longrightarrow> v\<^sub>1 = v\<^sub>2)"
  unfolding well_formed_equal_def by simp


subsection \<open>Condition Properties\<close>

inductive_cases cond_Unary: "stampConditions (Unary op e) v"
inductive_cases cond_Binary: "stampConditions (Binary op x y) v"
inductive_cases cond_Const: "stampConditions (Constant x) y"
inductive_cases cond_Value: "stampConditions (Value x) y"
inductive_cases cond_ExprL: "stampConditions (Expr x) y"
inductive_cases cond_ExprR: "stampConditions x (Expr y)"
inductive_cases cond_Stamp: "stampConditions (Stamp x) y"
inductive_cases cond_Combine: "stampConditions (Combine x y) v"
inductive_cases cond_InstanceOf: "stampConditions (InstanceOf e c) y"
inductive_cases cond_Method: "stampConditions (Method obj n p) y"
inductive_cases cond_Method_stamp: "stampConditions (Method obj STR ''stamp'' p) y"
inductive_cases cond_Method_upMask: "stampConditions (Method obj STR ''upMask'' p) y"
inductive_cases cond_Method_mayBeSet: "stampConditions (Method obj STR ''mayBeSet'' p) y"
inductive_cases cond_Method_downMask: "stampConditions (Method obj STR ''downMask'' p) y"
inductive_cases cond_Method_mustBeSet: "stampConditions (Method obj STR ''mustBeSet'' p) y"
inductive_cases cond_Method_lowerBound: "stampConditions (Method obj STR ''lowerBound'' p) y"
inductive_cases cond_Method_upperBound: "stampConditions (Method obj STR ''upperBound'' p) y"
lemmas cond_Method_cases = cond_Method_stamp cond_Method_upMask cond_Method_mayBeSet cond_Method_downMask cond_Method_mustBeSet cond_Method_lowerBound cond_Method_upperBound
inductive_cases coerce_True: "coerce_to_bool c True"

lemma logic_negation_bool:
  assumes "is_IntVal val"
  assumes "val_to_bool (unary_eval UnaryLogicNegation val)"
  shows "\<not>(val_to_bool val)"
  using assms unfolding unary_eval.simps intval_logic_negation.simps apply (cases val; auto)
  by (metis logic_negate_def take_bit_of_0)

lemma coerce_to_bool_det:
  assumes "coerce_to_bool x c"
  assumes "coerce_to_bool x c'"
  shows "c = c'"
  using assms apply (induction x c arbitrary: c' rule: coerce_to_bool.induct)
  using coerce_to_bool.simps by blast+

lemma stampConditions_det:
  assumes "stampConditions x c"
  assumes "stampConditions x c'"
  shows "c = c'"
  using assms apply (induction x c arbitrary: c' rule: stampConditions.induct) 
  apply (metis Condition.inject(4) cond_Unary)
  apply (metis Condition.inject(4) cond_Binary)
  using cond_Const apply blast
  using cond_Value apply blast 
  using cond_ExprL apply blast 
  using cond_Stamp apply blast 
             apply (metis cond_Combine)
            apply (smt (verit, best) Condition.distinct(71) Condition.inject(6) cond_InstanceOf)
           apply (smt (verit, best) Condition.distinct(71) Condition.inject(6) cond_InstanceOf)
  apply (smt (verit, best) Condition.inject(7) Condition.simps(82) cond_InstanceOf)
  apply (smt (verit, best) Condition.inject(7) Condition.simps(82) cond_InstanceOf)
  by (metis cond_Method_cases)+

lemma instance_of_const:
  assumes "evalCondition (InstanceOf (Expr x) STR ''ConstantNode'')"
  shows "is_ConstantExpr x"
proof -
  obtain c' where c': "stampConditions (InstanceOf (Expr x) STR ''ConstantNode'') c' \<and> coerce_to_bool c' True"
    using assms evalCondition_def by blast
  then have "c' = (Value (IntVal 32 1))"
    using assms coerce_True
    by (smt (verit, ccfv_SIG) coerce_to_bool.intros(1) coerce_to_bool_det cond_InstanceOf val_to_bool.simps(1))
  then have "class_name x = Some STR ''ConstantNode''"
    using assms c'
    by (meson Condition.inject(4) Value.inject(1) stampConditions.intros(5) stampConditions.intros(9) stampConditions_det zero_neq_one)
  then show ?thesis
    apply (cases x; auto)
    subgoal for op e by (cases op; auto)
    subgoal for op x y by (cases op; auto)
    done
qed

lemma instance_of_not_const:
  assumes "evalCondition (Unary UnaryLogicNegation (InstanceOf (Expr x) STR ''ConstantNode''))"
  shows "\<not>(is_ConstantExpr x)"
proof -
  obtain val where val: "stampConditions (InstanceOf (Expr x) STR ''ConstantNode'') (Value val)"
    using assms evalCondition_def
    by (meson cond_Unary)
  obtain c' where c': "stampConditions (Unary UnaryLogicNegation (InstanceOf (Expr x) STR ''ConstantNode'')) c' \<and> coerce_to_bool c' True"
    using assms evalCondition_def by blast
  then have "c' = Value (unary_eval UnaryLogicNegation val)"
    by (meson stampConditions.intros(1) stampConditions_det val)
  then have "val_to_bool (unary_eval UnaryLogicNegation val)"
    using assms coerce_True c'
    by (metis coerce_to_bool.intros(1) coerce_to_bool_det)
  then have "\<not>(val_to_bool val)"
    using logic_negation_bool
    by (metis Value.disc(2) val_to_bool.elims(2))
  then have "class_name x \<noteq> Some STR ''ConstantNode''"
    using assms
    using val stampConditions.intros(5) stampConditions.intros(8) stampConditions_det by fastforce
  then show ?thesis
    by (cases x; auto)
qed

lemma combine_cond_lhs:
  assumes "evalCondition (x; y)"
  shows "evalCondition x"
  using assms using cond_Combine evalCondition_def
  by (smt (z3) Condition.distinct(43) Condition.distinct(55) Condition.inject(8) coerce_to_bool.cases)

lemma combine_cond_rhs:
  assumes "evalCondition (x; y)"
  shows "evalCondition y"
  using assms using cond_Combine evalCondition_def
  by (smt (z3) Condition.distinct(43) Condition.distinct(55) Condition.inject(8) coerce_to_bool.cases)

abbreviation StampUnder :: "Condition \<Rightarrow> Condition \<Rightarrow> Condition" where
  "StampUnder u v \<equiv> cond[((u..stamp() instanceof IntegerStamp); 
                          (v..stamp() instanceof IntegerStamp)); 
                          ((u..stamp()..upperBound()) < (v..stamp()..lowerBound()))]"

lemma stamp_Method:
  shows "stampConditions ((Expr u)..stamp()) (Stamp (stamp_expr u))"
  using stampConditions.intros(12) stampConditions.intros(5) stampConditions.intros(6) stamp_semantics by fastforce

lemma stamp_upper_Method:
  shows "stampConditions ((Stamp s)..upperBound()) (Value (IntVal 64 (stpi_upper s)))"
  using stampConditions.intros(18) stampConditions.intros(3,6)
  by (metis upperBound_of.simps upperBound_semantics)

lemma stamp_lower_Method:
  shows "stampConditions ((Stamp s)..lowerBound()) (Value (IntVal 64 (stpi_lower s)))"
  using stampConditions.intros(17) stampConditions.intros(3,6)
  by (metis lowerBound_of.simps lowerBound_semantics)

lemma stamp_instanceof_IntegerStamp:
  assumes "evalCondition cond[((Expr u)..stamp() instanceof IntegerStamp)]"
  shows "is_IntegerStamp (stamp_expr u)"
proof -
  have "evalCondition cond[(Stamp (stamp_expr u)) instanceof IntegerStamp]"
    using assms
    by (smt (z3) evalCondition_def stampConditions.intros(10) stampConditions.intros(11) stampConditions.intros(6) stampConditions_det stamp_Method)
  then have "stamp_class_name (stamp_expr u) = STR ''IntegerStamp''"
    by (smt (verit, ccfv_threshold) assms coerce_to_bool.intros(1) coerce_to_bool_det evalCondition_def stampConditions.intros(11) stampConditions_det stamp_Method val_to_bool.simps(1))
  then show ?thesis by (cases "stamp_expr u"; auto)
qed


lemma lower_bound:
  "((- (2 ^ b div 2))::int) \<le> hi \<Longrightarrow> 0 < b \<and> b \<le> 64 \<Longrightarrow> (2 ^ 64 div 2 * - 1) \<le> hi"
  by (smt (verit, best) power_increasing zdiv_mono1)

lemma upper_bound:
  "hi \<le> ((2 ^ b div 2 - 1)::int) \<Longrightarrow> 0 < b \<and> b \<sqsubseteq> 64 \<Longrightarrow> hi \<le> (2 ^ 64 div 2 - 1)"
  by (smt (verit, best) power_increasing zdiv_mono1)

(*\<open>signed_take_bit n k = k \<longleftrightarrow> - (2 ^ n) \<le> k \<and> k < 2 ^ n\<close>*)

lemma stamp_upper_in_bounds:
  assumes "valid_stamp u"
  assumes "is_IntegerStamp u"
  shows "(stpi_upper u) = (take_bit 64 (stpi_upper u))"
  using assms
  by (metis JavaWords.size64 take_bit_length_eq wsst_TYs(3))
(*
proof -
  obtain lo hi b where sdef: "u = IntegerStamp b lo hi"
    using assms(2) is_IntegerStamp_def by auto
  have bbound: "0 < b \<and> b \<le> 64"
    using assms(1) sdef valid_stamp.simps(1) by blast  
  have "fst (bit_bounds b) \<le> hi"
    using assms unfolding valid_stamp.simps
    using sdef valid_stamp.simps(1) by blast
  then have "(2 ^ 64 div 2 * - 1) \<le> hi"
    using bbound unfolding bit_bounds.simps using lower_bound by auto 
  then have lb: "- (2 ^ 63) \<le> hi"
    by fastforce
  have "hi \<le> snd (bit_bounds b)"
    using assms unfolding valid_stamp.simps
    using sdef valid_stamp.simps(1) by blast
  then have "hi \<le> (2 ^ 64 div 2 - 1)"
    using bbound unfolding bit_bounds.simps using upper_bound by auto
  then have hb: "hi < 2 ^ 63"
    by auto
  from lb hb have tbid: "signed_take_bit 63 hi = hi"
    using signed_take_bit_int_eq_self by blast
  have "sint ((word_of_int hi)::64 word) = signed_take_bit (64 - 1) hi"
    using Word.sint_sbintrunc'
    by (metis JavaWords.size64 wsst_TYs(3))
  then have "sint ((word_of_int hi)::64 word) = hi"
    using tbid
    by simp
  (*have lb':"- (2 ^ 63) \<le> ((word_of_int hi)::64 word)"
    using lb hb word_of_int_less_eq_iff sorry
  have hb':"((word_of_int hi)::64 word) < 2 ^ 63"
    using lb hb word_of_int_less_eq_iff sorry
  have "signed_take_bit 63 ((word_of_int hi)::64 word) = ((word_of_int hi)::64 word)"
    using signed_take_bit_int_eq_self_iff sledgehammer
    apply (rule signed_take_bit_int_eq_self)
    using lb' hb' *)
  then have "hi = sint (signed_take_bit (63) ((word_of_int hi)::64 word))"
    using tbid sorry
  then show ?thesis
    using sdef by auto
  qed
*)

lemma stamp_lower_in_bounds:
  assumes "valid_stamp u"
  assumes "is_IntegerStamp u"
  shows "(stpi_lower u) = (take_bit 64 (stpi_lower u))"
  using assms
  by (metis JavaWords.size64 take_bit_length_eq wsst_TYs(3))

lemma stamp_under:
  assumes "valid_stamp (stamp_expr u) \<and> valid_stamp (stamp_expr v)"
  assumes "evalCondition cond[StampUnder (Expr u) (Expr v)]"
  shows "64 \<turnstile> stpi_upper (stamp_expr u) <j stpi_lower (stamp_expr v)"
proof -
  have ec: "evalCondition cond[Value (IntVal 64 (stpi_upper (stamp_expr u))) < Value (IntVal 64 (stpi_lower (stamp_expr v)))]" (is "evalCondition ?lowCond")
    using assms combine_cond_lhs combine_cond_rhs
    by (smt (z3) BinaryCool cond_Method_lowerBound cond_Method_upperBound cond_Stamp evalCondition_def stampConditions.intros(2) stampConditions.intros(4) stampConditions_det stamp_Method stamp_lower_Method stamp_upper_Method)
  obtain val where val1: "stampConditions ?lowCond val \<and> coerce_to_bool val True"
    using ec evalCondition_def by blast
  have val2: "val = Value (bin_eval BinIntegerLessThan (IntVal 64 (stpi_upper (stamp_expr u))) (IntVal 64 (stpi_lower (stamp_expr v))))"
    by (smt (verit, best) Condition.inject(4) cond_Binary stampConditions.intros(4) stampConditions_det val1)
  have "... = Value (if (int_signed_value 64 (stpi_upper (stamp_expr u))) < (int_signed_value 64 (stpi_lower (stamp_expr v))) then IntVal 32 1 else IntVal 32 0)"
    unfolding bin_eval.simps intval_less_than.simps bool_to_val_bin.simps using bool_to_val.simps by auto
  also have "val = Value (IntVal 32 1)"
    using calculation coerce_True val1 val2 by fastforce
  ultimately have lt: "(int_signed_value 64 (stpi_upper (stamp_expr u))) < (int_signed_value 64 (stpi_lower (stamp_expr v)))"
    using Value.inject(1) val2 by fastforce
  have isu: "is_IntegerStamp (stamp_expr u)"
    by (meson assms(2) combine_cond_lhs stamp_instanceof_IntegerStamp)
  have isv: "is_IntegerStamp (stamp_expr v)"
    using assms(2) combine_cond_lhs combine_cond_rhs stamp_instanceof_IntegerStamp by blast
  (*have ueq: "stpi_upper (stamp_expr u) = int_signed_value 64 (stpi_upper (stamp_expr u))"
    using assms(1) isu stamp_upper_in_bounds by blast
  have veq: "stpi_lower (stamp_expr v) = int_signed_value 64 (stpi_lower (stamp_expr v))"
    using assms(1) isv stamp_lower_in_bounds by blast*)
  from lt show ?thesis
    by blast
qed

lemma take_bit_trans:
  assumes "0 < b \<and> b' \<le> 64"
  assumes "b < b'"
  assumes "take_bit b x = x"
  shows "take_bit b' x = x"
  using assms
  by (metis min_def not_less take_bit_take_bit)

context includes bit_operations_syntax begin
lemma
  assumes "take_bit b x = x"
  shows "signed_take_bit b x = x"
  using assms
  by (metis (full_types) dual_order.refl signed_take_bit_take_bit)

lemma signed_take_bit_iffpos:
  assumes "\<not>(bit x (b-1))"
  shows "signed_take_bit (b-1) x = take_bit b x"
  using assms
  by (smt (verit, best) Common.arith(3) One_nat_def Suc_pred bit_take_bit_iff gr_zeroI signed_take_bit_code signed_take_bit_eq_if_positive zero_less_diff)

thm_oracles signed_take_bit_iffpos

value "max_int 1"

value "signed_take_bit 1 0::int64"
value "signed_take_bit 1 1::int64"
value "signed_take_bit 1 2::int64"
value "signed_take_bit 1 3::int64"
value "signed_take_bit 1 4::int64"
value "sint (signed_take_bit 1 0::int64)"
value "sint (signed_take_bit 1 1::int64)"
value "sint (signed_take_bit 1 2::int64)"
value "sint (signed_take_bit 1 3::int64)"
value "sint (signed_take_bit 1 4::int64)"

(*
lemma signed_take_bit_iffneg:
  assumes "0 < (b-1)"
  assumes "bit x (b-1)"
  shows "(signed_take_bit (b-1) x) = -((max_int (b)) + 1 - take_bit (b-1) x)" (is "?lhs = ?rhs")
proof -
  have "?lhs = take_bit (b-1) x OR (of_bool (bit x (b-1)) * NOT (mask (b-1)))"
    using signed_take_bit_def by blast
  then have "... = take_bit (b-1) x OR (NOT (mask (b-1)))"
    using assms by auto
  then have "... = take_bit (b-1) x 
  then have "... = -((mask (b-1)) + 1 - take_bit (b-1) x)"
    using assms(2) sledgehammer
    using assms sledgehammer

signed_take_bit n a = take_bit n a OR (of_bool (bit a n) * NOT (mask n))

lemma signed_lt_trans:
  assumes "0 < b \<and> b' \<le> 64"
  assumes "b < b'"
  assumes "take_bit b x = x"
  assumes "take_bit b y = y"
  assumes "b' \<turnstile> x <j y"
  shows "b \<turnstile> x <j y"
proof -
  have tbx: "take_bit b' x = x"
    using assms(1) assms(2) assms(3) take_bit_trans by blast
  have tby: "take_bit b' y = y"
    using assms(1) assms(2) assms(4) take_bit_trans by blast
  have tbxe: "take_bit b x = take_bit b' x"
    using tbx assms(3) by simp
  have tbye: "take_bit b y = take_bit b' y"
    using tby assms(4) by simp
  from tbxe tbye assms(5) show ?thesis sorry
qed
*)

lemma stamp_under_lower:
  assumes "valid_stamp (stamp_expr u) \<and> valid_stamp (stamp_expr v)"
  assumes "evalCondition (StampUnder (Expr u) (Expr v))"
  shows "stamp_under (stamp_expr u) (stamp_expr v)"
proof -
  obtain b lu hu du uu where su: "stamp_expr u = IntegerStamp b lu hu du uu"
    by (meson assms(2) combine_cond_lhs is_IntegerStamp_def stamp_instanceof_IntegerStamp)
  then have tbu: "signed_take_bit (b-1) hu = hu"
    using assms(1) by auto
  obtain b' lv hv dv uv where sv: "stamp_expr v = IntegerStamp b' lv hv dv uv"
    by (meson assms(2) combine_cond_lhs combine_cond_rhs is_IntegerStamp_def stamp_instanceof_IntegerStamp)
  then have tbv: "signed_take_bit (b'-1) lv = lv"
    using assms(1) by auto
  have lt64: "64 \<turnstile> hu <j lv"
    using su sv assms stamp_under
    by (metis Stamp.sel(2) Stamp.sel(3))
  have "b = b'"
    sorry
  then have "b \<turnstile> hu <j lv"
    using tbu tbv lt64
    by (smt (verit, ccfv_SIG) assms(1) int_signed_value.simps raise_lt signed_word_eqI sv valid_stamp.simps(1))
  then show ?thesis
    by (simp add: \<open>b = b'\<close> su sv)
qed

end

end