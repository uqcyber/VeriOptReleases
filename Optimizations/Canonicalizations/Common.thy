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
    by (smt (verit, ccfv_SIG) coerce_to_bool.intros(2) coerce_to_bool_det cond_InstanceOf val_to_bool.simps(1))
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
    by (metis coerce_to_bool.intros(2) coerce_to_bool_det)
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

abbreviation StampUnder :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> Condition" where
  "StampUnder u v \<equiv> cond[(((Expr u)..stamp() instanceof IntegerStamp); 
                          ((Expr v)..stamp() instanceof IntegerStamp)); 
                          (((Expr u)..stamp()..upperBound()) < ((Expr v)..stamp()..lowerBound()))]"

lemma stamp_Method:
  shows "stampConditions ((Expr u)..stamp()) (Stamp (stamp_expr u))"
  using stampConditions.intros(12) stampConditions.intros(5) stampConditions.intros(6) stamp_semantics by fastforce

lemma stamp_upper_Method:
  shows "stampConditions ((Stamp s)..upperBound()) (Value (IntVal 64 (word_of_int (stpi_upper s))))"
  using stampConditions.intros(18) stampConditions.intros(3,6)
  by (metis upperBound_of.simps upperBound_semantics)

lemma stamp_lower_Method:
  shows "stampConditions ((Stamp s)..lowerBound()) (Value (IntVal 64 (word_of_int (stpi_lower s))))"
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
    by (smt (verit, ccfv_threshold) assms coerce_to_bool.intros(2) coerce_to_bool_det evalCondition_def stampConditions.intros(11) stampConditions_det stamp_Method val_to_bool.simps(1))
  then show ?thesis by (cases "stamp_expr u"; auto)
qed

no_notation ExclusiveOr ("_ ^ _")
(*
lemma stamp_upper_in_bounds:
  assumes "valid_stamp u"
  assumes "is_IntegerStamp u"
  shows "(stpi_upper u) = (int_signed_value 64 (word_of_int (stpi_upper u)))"
proof -
  have "0 < stp_bits u \<and> stp_bits u \<le> 64"
    by (metis Stamp.collapse(1) assms(1) assms(2) valid_stamp.simps(1))
  then have "stpi_upper u \<ge> 2 ^ 64 div 2 * - 1"
    using assms apply (induction "stp_bits u") 
    apply simp using valid_stamp.simps bit_bounds.simps
    using assms using valid_stamp.simps apply auto sorry
    then show ?thesis
      sorry
  qed

lemma stamp_lower_in_bounds:
  assumes "valid_stamp u"
  assumes "is_IntegerStamp u"
  shows "(stpi_lower u) = (int_signed_value 64 (word_of_int (stpi_lower u)))"
  sorry

lemma stamp_under:
  assumes "valid_stamp (stamp_expr u) \<and> valid_stamp (stamp_expr v)"
  assumes "evalCondition cond[StampUnder u v]"
  shows "stpi_upper (stamp_expr u) < stpi_lower (stamp_expr v)"
proof -
  have ec: "evalCondition cond[Value (IntVal 64 (word_of_int (stpi_upper (stamp_expr u)))) < Value (IntVal 64 (word_of_int (stpi_lower (stamp_expr v))))]" (is "evalCondition ?lowCond")
    using assms combine_cond_lhs combine_cond_rhs
    by (smt (z3) cond_Binary cond_Const cond_Method_lowerBound cond_Method_upperBound evalCondition_def lowerBound_of.simps lowerBound_semantics stampConditions.intros(2) stampConditions.intros(5) stampConditions_det stamp_Method upperBound_of.simps upperBound_semantics)
  obtain val where val1: "stampConditions ?lowCond val \<and> coerce_to_bool val True"
    using ec evalCondition_def by blast
  have val2: "val = Value (bin_eval BinIntegerLessThan (IntVal 64 (word_of_int (stpi_upper (stamp_expr u)))) (IntVal 64 (word_of_int (stpi_lower (stamp_expr v)))))"
    by (metis (no_types, lifting) BinaryCool Condition.inject(5) cond_Value val1)
  have "... = Value (if (int_signed_value 64 (word_of_int (stpi_upper (stamp_expr u)))) < (int_signed_value 64 (word_of_int (stpi_lower (stamp_expr v)))) then IntVal 32 1 else IntVal 32 0)"
    unfolding bin_eval.simps intval_less_than.simps bool_to_val_bin.simps using bool_to_val.simps by auto
  also have "val = Value (IntVal 32 1)"
    using calculation coerce_True val1 val2 by fastforce
  ultimately have lt: "(int_signed_value 64 (word_of_int (stpi_upper (stamp_expr u)))) < (int_signed_value 64 (word_of_int (stpi_lower (stamp_expr v))))"
    using Value.inject(1) val2 by fastforce
  have isu: "is_IntegerStamp (stamp_expr u)"
    by (meson assms(2) combine_cond_lhs stamp_instanceof_IntegerStamp)
  have isv: "is_IntegerStamp (stamp_expr v)"
    using assms(2) combine_cond_lhs combine_cond_rhs stamp_instanceof_IntegerStamp by blast
  have ueq: "stpi_upper (stamp_expr u) = int_signed_value 64 (word_of_int (stpi_upper (stamp_expr u)))"
    using assms(1) isu stamp_upper_in_bounds by blast
  have veq: "stpi_lower (stamp_expr v) = int_signed_value 64 (word_of_int (stpi_lower (stamp_expr v)))"
    using assms(1) isv stamp_lower_in_bounds by blast
  from lt show ?thesis
    using ueq veq assms by argo
qed

lemma stamp_under_lower:
  assumes "valid_stamp (stamp_expr u) \<and> valid_stamp (stamp_expr v)"
  assumes "evalCondition (StampUnder u v)"
  shows "stamp_under (stamp_expr u) (stamp_expr v)"
  using assms
  by (smt (verit, best) Stamp.collapse(1) combine_cond_lhs combine_cond_rhs stamp_instanceof_IntegerStamp stamp_under stamp_under.simps(1))
*)

end