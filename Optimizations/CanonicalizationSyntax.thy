theory CanonicalizationSyntax
  imports 
    OptimizationDSL.Canonicalization
    CanonicalizationTreeProofs 
begin

(* TODO: rename this to a more general name now it is not 32-bit specific. *)
typedef i32exp = "{e . (\<forall>m p v . ([m,p] \<turnstile> e \<mapsto> v) \<longrightarrow> (is_IntVal v))}"
  by auto

lemma i32e_eval:
  "\<forall>v. \<exists>b vv. ([m, p] \<turnstile> (Rep_i32exp e) \<mapsto> v) \<longrightarrow> ([m, p] \<turnstile> (Rep_i32exp e) \<mapsto> IntVal b vv)"
  using Rep_i32exp is_IntVal_def by fastforce

lemma int32_binary:
  assumes "[m, p] \<turnstile> BinaryExpr op (Rep_i32exp x) (Rep_i32exp y) \<mapsto> v"
  shows "\<exists>b xv yv. v = bin_eval op (IntVal b xv) (IntVal b yv)"
  using assms apply auto using Rep_i32exp is_IntVal_def
  sorry
(* WAS:
  by (metis (mono_tags, lifting) mem_Collect_eq)
*)

typedef intexp = "{e . (\<forall>m p v . ([m,p] \<turnstile> e \<mapsto> v) \<longrightarrow> is_IntVal v)}"
  by auto

declare
  [[coercion_enabled]]
  [[coercion Rep_intexp, coercion Rep_i32exp]]

fun size :: "IRExpr \<Rightarrow> nat" where
  "size (UnaryExpr op e) = (size e) + 1" |
  "size (BinaryExpr BinAdd x y) = (size x) + (2 * (size y))" |
  "size (BinaryExpr op x y) = (size x) + (size y)" |
  "size (ConditionalExpr cond t f) = (size cond) + (size t) + (size f) + 2" |
  "size (ConstantExpr c) = 1" |
  "size (ParameterExpr ind s) = 2" |
  "size (LeafExpr nid s) = 2" |
  "size (ConstantVar c) = 2" |
  "size (VariableExpr x s) = 2"

lemma size_gt_0: "size e > 0"
proof (induction e)
case (UnaryExpr x1 e)
  then show ?case
    by auto
next
case (BinaryExpr x1 e1 e2)
  then show ?case
    by (cases x1; auto)
next
  case (ConditionalExpr e1 e2 e3)
  then show ?case
    by auto
next
  case (ParameterExpr x1 x2)
  then show ?case
    by auto
next
  case (LeafExpr x1 x2)
  then show ?case
    by auto
next
  case (ConstantExpr x)
  then show ?case
    by auto
next
  case (ConstantVar x)
  then show ?case
    by auto
next
  case (VariableExpr x1 x2)
  then show ?case
    by auto
qed

lemma binary_expr_size_gte_2: "size (BinaryExpr op x y) \<ge> 2"
  apply (induction "BinaryExpr op x y"; cases op; auto)
  apply (simp add: Suc_leI trans_le_add2 size_gt_0)
  by (metis Suc_leI add_2_eq_Suc' add_Suc_shift add_mono numeral_2_eq_2 size_gt_0)+

lemma size_eq_1: "(size e = 1) = is_ConstantExpr e"
  apply (cases e; auto)
  by (metis binary_expr_size_gte_2 lessI not_less numeral_2_eq_2 size_gt_0)+

lemma nonconstants_gt_one: "\<not> (is_ConstantExpr e) \<Longrightarrow> size e > 1"
  apply (cases e; auto)
  using binary_expr_size_gte_2 by (simp add: numeral_2_eq_2 Suc_le_eq size_gt_0)+

lemma size_det: "x = y \<Longrightarrow> size x = size y"
  by auto

lemma size_non_add: "op \<noteq> BinAdd \<Longrightarrow> size (BinaryExpr op a b) = size a + size b"
  by (induction op; auto)

value "exp[abs e]"
ML_val \<open>@{term "abs e"}\<close>
ML_val \<open>@{term "x & x"}\<close>
ML_val \<open>@{term "cond ? tv : fv"}\<close>
ML_val \<open>@{term "x < y"}\<close>
ML_val \<open>@{term "c < y"}\<close>
ML_val \<open>@{term "a \<Longrightarrow> c < y"}\<close>
ML_val \<open>@{term "x << y"}\<close>

value "exp[(const v1) + y]"

datatype Type =
  Integer |
  Float |
  Object |
  Unknown

definition type :: "IRExpr \<Rightarrow> Type" where
  "type e = (case (stamp_expr e) of
    IntegerStamp _ _ _ \<Rightarrow> Integer
    | ObjectStamp _ _ _ _ \<Rightarrow> Object
    | _ \<Rightarrow> Unknown)"

lemma unfold_type[simp]:
  "(type x = Integer) = is_IntegerStamp (stamp_expr x)"
  by (simp add: Stamp.case_eq_if type_def)

definition type_safe :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" where
  "type_safe e1 e2 = 
    ((type e1 = type e2) 
    \<and> (is_IntegerStamp (stamp_expr e1) 
        \<longrightarrow> (stp_bits (stamp_expr e1) = stp_bits (stamp_expr e2))))"

fun int_and_equal_bits :: "Value \<Rightarrow> Value \<Rightarrow> bool" where
  "int_and_equal_bits (IntVal b1 e1) (IntVal b2 e2) = (b1 = b2 \<and> 0 < b1 \<and> b1 \<le> 64)" |
  "int_and_equal_bits _ _ = False"

lemma unfold_int_typesafe[simp]:
  assumes "type e1 = Integer"
  shows "type_safe e1 e2 = 
    ((type e1 = type e2) \<and>
    (stp_bits (stamp_expr e1) = stp_bits (stamp_expr e2)))"
proof -
  have "is_IntegerStamp (stamp_expr e1)"
    using assms by simp
  then show ?thesis
    by (simp add: type_safe_def)
qed

lemma uminus_intstamp_prop:
  assumes "type x = Integer"
  shows "type exp[-x] = Integer"
proof -
  obtain b lo hi where "stamp_expr x = IntegerStamp b lo hi"
    using assms by (auto simp add: is_IntegerStamp_def)
  then show ?thesis
    by simp
qed

lemma "(size exp[x + (-y)]) > (size exp[x - y])"
  using size.simps(1,2) by force

datatype RewriteResult =
  success IRExpr |
  fail

ML_val \<open>@{term "(case n of
    (BinaryExpr BinAdd (ConstantExpr c_val) e) \<Rightarrow>
      if (\<not>(is_ConstantExpr e) \<and> type e = Integer) then
        success (BinaryExpr BinAdd e (ConstantExpr c_val))
      else
        fail |
    _ \<Rightarrow> fail)"}\<close>


(*(app "_case_syntax"
            (Ast.Variable "x",
             foldr1 (app \<^syntax_const>\<open>_case2\<close>) (map_index (case1 constraint authentic) spec)),
           capp (capps (case_constant, map_index arg1 spec), Ast.Variable "x"))*)

ML \<open>
val test = Conditional
            (@{term \<open>BinaryExpr BinAdd (ConstantExpr c_val) e\<close>},
            @{term \<open>BinaryExpr BinAdd e (ConstantExpr c_val)\<close>},
            @{term \<open>\<not>(is_ConstantExpr e) \<and> type e = Integer\<close>})

fun generate_cases p e ctxt =
  let
  val x =
    Free (singleton (Name.variant_list (fold Term.add_free_names [p, e] [])) "x", dummyT);
  
  val NilC = Syntax.const @{const_name "Nil"};
  val ConsC = Syntax.const @{const_name "Cons"};
  val dummyC = Syntax.const @{const_name "Pure.dummy_pattern"};
  
  fun single x = ConsC $ x $ NilC;
  
  val case1 = Syntax.const \<^syntax_const>\<open>_case1\<close> $ p $ single e;
  val case2 =
    Syntax.const \<^syntax_const>\<open>_case1\<close> $ dummyC $ NilC;
  val cs = Syntax.const \<^syntax_const>\<open>_case2\<close> $ case1 $ case2;
  
  val res = Case_Translation.case_tr false ctxt [x, cs];
  val _ = @{print} res;

  val plz = Syntax.const @{syntax_const "_case_syntax"}
  in             
    single e $ dummyC
  end;

fun rewrite_to_code bind rewrite ctxt =
  case rewrite of
    Conditional (pre, post, cond) => 
        @{const Trueprop} $
        (Const ("HOL.eq", @{typ "(IRExpr \<Rightarrow> RewriteResult) \<Rightarrow> (IRExpr \<Rightarrow> RewriteResult) \<Rightarrow> bool"})
        $ (Free (bind ^ "_code", @{typ "IRExpr \<Rightarrow> RewriteResult"}))
        $ (Const ("IRTreeEval.IRExpr.case_IRExpr",
          @{typ \<open>(IRUnaryOp \<Rightarrow> IRExpr \<Rightarrow> RewriteResult)
           \<Rightarrow> (IRBinaryOp \<Rightarrow> IRExpr \<Rightarrow> IRExpr \<Rightarrow> RewriteResult)
              \<Rightarrow> (IRExpr \<Rightarrow> IRExpr \<Rightarrow> IRExpr \<Rightarrow> RewriteResult)
                 \<Rightarrow> (nat \<Rightarrow> Stamp \<Rightarrow> RewriteResult)
                    \<Rightarrow> (nat \<Rightarrow> Stamp \<Rightarrow> RewriteResult)
                       \<Rightarrow> (Value \<Rightarrow> RewriteResult)
                          \<Rightarrow> (char list \<Rightarrow> RewriteResult)
                             \<Rightarrow> (char list \<Rightarrow> Stamp \<Rightarrow> RewriteResult)
                                \<Rightarrow> IRExpr \<Rightarrow> RewriteResult\<close>})
        $ @{term "(\<lambda> (_::IRUnaryOp) \<Rightarrow> \<lambda> (_::IRExpr) \<Rightarrow> fail)"}
        $ @{term "(\<lambda> (_::IRBinaryOp) \<Rightarrow> \<lambda> (_::IRExpr) \<Rightarrow> \<lambda> (_::IRExpr) \<Rightarrow> fail)"}
        $ @{term "(\<lambda> (_::IRExpr) \<Rightarrow> \<lambda> (_::IRExpr) \<Rightarrow> \<lambda> (_::IRExpr) \<Rightarrow> fail)"}
        $ @{term "(\<lambda> (_::nat) \<Rightarrow> \<lambda> (_::Stamp) \<Rightarrow> fail)"}
        $ @{term "(\<lambda> (_::ID) \<Rightarrow> \<lambda> (_::Stamp) \<Rightarrow> fail)"}
        $ @{term "(\<lambda> (_::Value) \<Rightarrow> fail)"}
        $ @{term "(\<lambda> (_::string) \<Rightarrow> fail)"}
        $ @{term "(\<lambda> (_::string) \<Rightarrow> \<lambda> (_::Stamp) \<Rightarrow> fail)"}))
 |
   (* Transform (pre, post) => 
        @{const Trueprop}
        $ (Const ("HOL.eq", @{typ "(IRExpr \<Rightarrow> RewriteResult) \<Rightarrow> (IRExpr \<Rightarrow> RewriteResult) \<Rightarrow> bool"})
           $ Free (bind ^ "_code", @{typ "IRExpr \<Rightarrow> RewriteResult"})
           $ generate_cases pre post ctxt
          )
 | *)
    _ => @{const Trueprop} $ 
        (Const ("HOL.eq", @{typ "(IRExpr \<Rightarrow> RewriteResult) \<Rightarrow> (IRExpr \<Rightarrow> RewriteResult) \<Rightarrow> bool"})
        $ (Free (bind ^ "_code", @{typ "IRExpr \<Rightarrow> RewriteResult"}))
        $ @{term \<open>\<lambda> (x::IRExpr) \<Rightarrow> fail\<close>});
\<close>

fun bad_trm :: "IRExpr \<Rightarrow> nat" where
  "bad_trm x = 0"

definition test where
  "test n = (case n of
    (BinaryExpr BinAdd (ConstantExpr c_val) e) \<Rightarrow>
      if (\<not>(is_ConstantExpr e) \<and> type e = Integer) then
        success (BinaryExpr BinAdd e (ConstantExpr c_val))
      else
        fail |
    _ \<Rightarrow> fail)"

ML_val \<open>@{term "(case n of
    (BinaryExpr BinAdd (ConstantExpr c_val) e) \<Rightarrow>
      if (\<not>(is_ConstantExpr e) \<and> type e = Integer) then
        success (BinaryExpr BinAdd e (ConstantExpr c_val))
      else
        fail |
    _ \<Rightarrow> fail)"}\<close>

print_phases

ML_val \<open>@{term "case_IRExpr"}
        $ @{term "(\<lambda> (_::IRUnaryOp) \<Rightarrow> \<lambda> (_::IRExpr) \<Rightarrow> fail)"}
        $ @{term "(\<lambda> (_::IRBinaryOp) \<Rightarrow> \<lambda> (_::IRExpr) \<Rightarrow> \<lambda> (_::IRExpr) \<Rightarrow> fail)"}
        $ @{term "(\<lambda> (_::IRExpr) \<Rightarrow> \<lambda> (_::IRExpr) \<Rightarrow> \<lambda> (_::IRExpr) \<Rightarrow> fail)"}
        $ @{term "(\<lambda> (_::nat) \<Rightarrow> \<lambda> (_::Stamp) \<Rightarrow> fail)"}
        $ @{term "(\<lambda> (_::ID) \<Rightarrow> \<lambda> (_::Stamp) \<Rightarrow> fail)"}
        $ @{term "(\<lambda> (_::Value) \<Rightarrow> fail)"}
        $ @{term "(\<lambda> (_::string) \<Rightarrow> fail)"}
        $ @{term "(\<lambda> (_::string) \<Rightarrow> \<lambda> (_::Stamp) \<Rightarrow> fail)"}\<close>

ML_val \<open>@{term "hello = case_IRExpr
    (\<lambda> _ \<Rightarrow> \<lambda> _ \<Rightarrow> fail)
    (\<lambda> _ \<Rightarrow> \<lambda> _ \<Rightarrow> \<lambda> _ \<Rightarrow> fail)
    (\<lambda> _ \<Rightarrow> \<lambda> _ \<Rightarrow> \<lambda> _ \<Rightarrow> fail)
    (\<lambda> _ \<Rightarrow> \<lambda> _ \<Rightarrow> fail)
    (\<lambda> _ \<Rightarrow> \<lambda> _ \<Rightarrow> fail)
    (\<lambda> _ \<Rightarrow> fail)
    (\<lambda> _ \<Rightarrow> fail)
    (\<lambda> _ \<Rightarrow> \<lambda> _ \<Rightarrow> fail)"}\<close>


phase Canonicalization
  terminating size
begin

(*
optimization constant_fold:
  "(const(c\<^sub>1) \<oplus>\<^sub>x const(c\<^sub>2)) \<mapsto> (bin_eval c\<^sub>1 x c\<^sub>2)"

optimization constant_add:
  "(e1 + e2) \<mapsto> r when (e1 = ConstantExpr v1 \<and> e2 = ConstantExpr v2 \<and> r = ConstantExpr (intval_add v1 v2))"
  unfolding le_expr_def apply (cases; auto) using evaltree.ConstantExpr defer
   apply simp
  sorry
*)


(*
value "constant_add_code (BinaryExpr BinAdd (ConstantExpr (IntVal32 0)) (ConstantExpr (IntVal32 0)))"
*)

print_context

optimization constant_shift:
  "((const c) + (e::intexp)) \<longmapsto> (e + (const c)) when (\<not>(is_ConstantExpr e))"
  using nonconstants_gt_one by (auto simp add: intval_add_sym)

print_context

thm constant_shift

optimization neutral_zero:
  "((e::i32exp) + const(IntVal b 0)) \<longmapsto> e"
  apply auto
  by (metis (no_types, lifting) add.right_neutral evalDet eval_unused_bits_zero intval_add.simps(1)
      i32e_eval)

ML_val \<open>@{term "(e1 - e2) + e2 \<longmapsto> e1"}\<close>

lemma neutral_left_add_sub_val:
  assumes "val[(e1 - e2) + e2] \<noteq> UndefVal"
  shows "val[(e1 - e2) + e2] = e1"
  using assms apply (cases e1; cases e2; auto)
  sorry
(* TODO: need to derive information about the values being well-formed? *)

optimization neutral_left_add_sub:
  "((e1::intexp) - (e2::intexp)) + e2 \<longmapsto> e1"
  apply (simp add: size_gt_0)+
  apply ((rule allI)+; rule impI)
  subgoal premises p for m p v
  proof -
    obtain xv where xv: "[m,p] \<turnstile> Rep_intexp e1 \<mapsto> xv"
      using p by auto
    obtain yv where yv: "[m,p] \<turnstile> Rep_intexp e2 \<mapsto> yv"
      using p by blast
    then have lhsEval: "[m,p] \<turnstile> exp[(e1 - e2) + e2] \<mapsto> val[(xv - yv) + yv]"
      by (smt (verit, best) BinaryExprE bin_eval.simps(1) bin_eval.simps(3) evalDet p xv)
    then have defined: "val[(xv - yv) + yv] \<noteq> UndefVal"
      using evaltree_not_undef by auto
    then have rearrange: "val[(xv - yv) + yv] = val[(xv - yv + yv)]"
      by auto
    then have simplify: "... = val[xv]"
      using defined neutral_left_add_sub_val by blast
    then show ?thesis
      by (metis evalDet lhsEval p xv)
  qed
  done

lemma neutral_right_add_sub_val:
  assumes "val[e1 + (e2 - e1)] \<noteq> UndefVal"
  shows "val[e1 + (e2 - e1)] = e2"
  using assms apply (cases e1; cases e2; auto)
  sorry
(* TODO: need to derive information about the values being well-formed? *)

optimization neutral_right_add_sub:
  "(e1::intexp) + ((e2::intexp) - e1) \<longmapsto> e2"
  apply (simp add: size_gt_0)+
  by (smt (verit) BinaryExprE bin_eval.simps(1,3) evalDet neutral_right_add_sub_val)

optimization add_ynegate:
  "((x::i32exp) + (-(y::i32exp))) \<longmapsto> (x - y)"
  defer apply simp
  using Groups.group_add_class.add_uminus_conv_diff sorry
  (*by (metis BinaryExpr bin_eval.simps(3) evalDet i32e_eval intval_add.simps(1) intval_negate.simps(1) intval_sub.simps(1))*)
  
print_context

end

print_context

phase DirectTranslationTest
  terminating size
begin

(*
value "intval_abs (IntVal32 (0))"
value "intval_abs (intval_abs (IntVal32 (0)))"
value "intval_abs (IntVal32 (2147483648))"
value "intval_abs (intval_abs (IntVal32 (2147483648)))"
value "intval_abs (IntVal32 (-2147483648))"
value "intval_abs (intval_abs (IntVal32 (-2147483648)))"
value "intval_abs (IntVal32 (4294967295))"
value "intval_abs (intval_abs (IntVal32 (4294967295)))"

lemma helper: "intval_abs (IntVal32 e) = intval_abs (intval_abs (IntVal32 e))" (is ?thesis)
  sorry

optimization AbsIdempotence: "abs(abs(Rep_int32 e)) \<mapsto> abs(Rep_int32 e)"
  apply auto using helper
  using Rep_int32
  by (metis UnaryExpr evalDet int32_eval unary_eval.simps(1))

optimization AbsNegate: "abs(-e) \<mapsto> abs(e) when is_IntegerStamp (stamp_expr e)"
  apply auto
  by (metis UnaryExpr abs_neg_is_neg stamp_implies_valid_value is_IntegerStamp_def unary_eval.simps(1))
*)

(* NOTE: I had to add assms 2-3 to this.  It is similar to validDefIntConst. *)
lemma int_constants_valid:
  assumes "is_IntVal val"
  assumes "0 < intval_bits val \<and> intval_bits val \<le> 64"
  assumes "take_bit (intval_bits val) (intval_word val) = (intval_word val)"
  shows "valid_value val (constantAsStamp val)"
proof - 
  obtain ival where ival: "val = IntVal (intval_bits val) ival"
    using assms is_IntVal_def by force
  then show ?thesis
    by (metis intval_word.simps validDefIntConst assms(2,3))
qed  

(*
lemma unary_eval_preserves_validity:
  assumes "is_int_val c"
  shows "valid_value (unary_eval op c) (constantAsStamp (unary_eval op c))"
  using assms apply (cases c) apply simp
     defer defer apply simp+
  apply (cases op)
  using int_constants_valid intval_abs.simps(1) is_int_val.simps(1) unary_eval.simps(1) apply presburger
  using int_constants_valid intval_negate.simps(1) is_int_val.simps(1) unary_eval.simps(2) apply presburger
  using int_constants_valid intval_not.simps(1) is_int_val.simps(1) unary_eval.simps(3) apply presburger
  using int_constants_valid intval_logic_negation.simps(1) is_int_val.simps(1) unary_eval.simps(4) apply presburger
     defer defer defer
     apply (cases op)
  using int_constants_valid intval_abs.simps(2) is_int_val.simps(2) unary_eval.simps(1) apply presburger
  using int_constants_valid intval_negate.simps(2) is_int_val.simps(2) unary_eval.simps(2) apply presburger
  using int_constants_valid intval_not.simps(2) is_int_val.simps(2) unary_eval.simps(3) apply presburger
  sorry (* WARNING: TODO: WARNING: a whole bunch of unary operations aren't implemented making this false *)

optimization UnaryConstantFold: "UnaryExpr op c \<mapsto> ConstantExpr (unary_eval op val_c) when is_int_val val_c"
  apply (auto simp: int_constants_valid)
  using evaltree.ConstantExpr int_constants_valid unary_eval_preserves_validity by simp
*)

optimization AndEqual: "((x::intexp) & x) \<longmapsto> x"
  using size_gt_0 apply auto
  by (smt (verit) and.idem eval_unused_bits_zero new_int.simps new_int_bin.elims intval_and.simps 
      constantAsStamp.elims evalDet)

optimization AndShiftConstantRight: "((const x) + y) \<longmapsto> y + (const x) when ~(is_ConstantExpr y)"
  using nonconstants_gt_one apply simp_all
  by (smt (verit, ccfv_threshold) BinaryExprE bin_eval.simps(1) evaltree.simps intval_add_sym
      IRExpr.inject(6) evalDet unfold_binary)

(*
optimization AndRightFallthrough: "x & y \<mapsto> y when (canBeZero x.stamp & canBeOne y.stamp) = 0" sorry
optimization AndLeftFallthrough: "x & y \<mapsto> x when (canBeZero y.stamp & canBeOne x.stamp) = 0" sorry
*)

lemma neutral_and:
  assumes "valid_value x (IntegerStamp 32 lox hix)"
  shows "bin_eval BinAnd x (IntVal 32 (neg_one 32)) = x"
  using assms apply (cases x; auto) by (metis take_bit_eq_mask)+

context
  includes bit_operations_syntax
begin

optimization AndNeutral: "((x::i32exp) & (const (IntVal 32 (neg_one 32)))) \<longmapsto> x"
  apply auto
  by (smt (verit, del_insts) evalDet i32e_eval intval_and.simps(1) new_int_bin.simps Value.inject(1) 
      take_bit_eq_mask eval_unused_bits_zero new_int.elims new_int_bin.elims)

end

optimization ConditionalEqualBranches: "(b ? v : v) \<longmapsto> v" .

optimization ConditionalEqualIsRHS: "((x eq y) ? x : y) \<longmapsto> y when (type x = Integer \<and> type_safe x y)"
  apply auto
  subgoal premises p for m p v true false xa ya
  proof-
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p(9) by auto
    obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> yv"
      using p(10) by auto
    have notUndef: "xv \<noteq> UndefVal \<and> yv \<noteq> UndefVal"
      using evaltree_not_undef xv yv by blast
    have evalNotUndef: "intval_equals xv yv \<noteq> UndefVal"
      by (metis evalDet p(2,9,10) xv yv)
    obtain xb xvv where xvv: "xv = IntVal xb xvv"
      by (metis Value.exhaust evalNotUndef intval_equals.simps(3,4,5) notUndef)
    obtain yb yvv where yvv: "yv = IntVal yb yvv"
      by (metis evalNotUndef intval_equals.simps(7,8,9) intval_logic_negation.cases notUndef)
    have unfoldEqual: "(intval_equals xv yv) = bool_to_val (xvv = yvv)"
      using evalNotUndef xvv yvv by auto
    then show ?thesis
      by (smt (verit) p yvv evalDet bool_to_val_bin.simps bool_to_val.simps(2) val_to_bool.simps(1)
          yv intval_equals.simps(1) xv xvv)
  qed
  done

(*
optimization ConditionalEliminateKnownLess: "(x < y ? x : y) \<mapsto> x when (x.stamp.upper <= y.stamp.lower)" sorry
optimization ConditionalEliminateKnownLess: "(x < y ? y : x) \<mapsto> y when (x.stamp.upper <= y.stamp.lower)" sorry
*)

lemma bool_is_int_val:
  "is_IntVal (bool_to_val x)"
  by (metis (full_types) is_IntVal_def bool_to_val.simps)

text \<open>Not all binary operators require equal bits, but these results hold for those that do.\<close>

lemma bin_eval_defined:
  assumes "int_and_equal_bits c1 c2"
  assumes "val = bin_eval op c1 c2"
  shows "val \<noteq> UndefVal \<and> is_IntVal val"
  using assms bool_is_int_val apply (cases c1; cases c2; cases op; simp) defer
  apply (smt (verit) Value.disc(2) Value.distinct(1) new_int.simps)
  prefer 5 defer
  apply blast apply blast apply blast apply blast apply blast sorry

(* TODO: this needs refining, as there are three groups of binary operators,
  each with different resulting bit widths.  Maybe we need lemmas about the
  result size for each group? 
*)
lemma bin_eval_preserves_validity:
  assumes "int_and_equal_bits c1 c2"
  assumes "val = bin_eval op c1 c2"
  shows "valid_value val (constantAsStamp val)"
proof -
  obtain b ival where val: "val = IntVal b ival"
    using bin_eval_defined assms is_IntVal_def by force
  then have "valid_stamp (constantAsStamp val)"
    using assms validStampIntConst valid_stamp.elims sorry
  then show ?thesis
    using val by (auto simp add: bin_eval_unused_bits_zero assms(2))
qed

optimization BinaryFoldConstant: "BinaryExpr op (const e1) (const e2) \<longmapsto>
                                  ConstantExpr (bin_eval op e1 e2) when int_and_equal_bits e1 e2"
  using nonconstants_gt_one apply auto
  by (simp add: wf_value_def ConstantExpr bin_eval_preserves_validity)

optimization AddShiftConstantRight: "((const c) + y) \<longmapsto> y + (const c) when ~(is_ConstantExpr y)"
  using nonconstants_gt_one apply simp_all
  by (smt (verit, del_insts) BinaryExprE bin_eval.simps(1) evaltree.simps intval_add_sym)

(*
optimization RedundantSubAdd: "isAssociative + => (a - b) + b \<mapsto> a" sorry
optimization RedundantAddSub: "isAssociative + => (b + a) - b \<mapsto> a" sorry
*)
lemma neutral_add:
  assumes "valid_value x (IntegerStamp 32 lox hix)"
  shows "bin_eval BinAdd x (IntVal 32 (0)) = x"
  using assms by (cases x; auto; presburger)

(* TODO: this one can be false if e is malformed.  E.g. 32-bits but with upper bits set. *)
lemma AddNeutralVal:
  assumes "val[e + const 0] \<noteq> UndefVal"
  shows "val[e + const 0] = e"
  using assms apply (cases e; auto)
  sorry

optimization AddNeutral: "(e + (const (IntVal 32 0))) \<longmapsto> e when (stamp_expr e = IntegerStamp 32 l u)"
  apply (simp; (rule impI)+; (rule allI)+) using AddNeutralVal by fastforce

lemma intval_negateadd_equals_sub_left: "bin_eval BinAdd (unary_eval UnaryNeg e) y = bin_eval BinSub y e"
  by (cases e; auto; cases y; auto)

lemma intval_negateadd_equals_sub_right: "bin_eval BinAdd x (unary_eval UnaryNeg e) = bin_eval BinSub x e"
  by (cases e; auto; cases x; auto)

lemma mulNeutral_Exp:
  shows "exp[(x * const(IntVal b 1))] \<ge> x"
  apply auto
  subgoal premises p for m p xa
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p(1) by auto
    obtain xb xvv where xvv: "xv = IntVal xb xvv"
      by (metis (no_types, opaque_lifting) constantAsStamp.cases evalDet evaltree_not_undef p(1,2)
          intval_mul.simps(3,4,5) xv)
    then have width: "xb = b"
      by (metis evalDet intval_mul.simps(1) new_int_bin.elims xv p(1,2))
    then have constEval: "[m,p] \<turnstile> exp[const(IntVal b 1)] \<mapsto> IntVal b 1"
      by (simp add: ConstantExpr p(3))
    then have lhsEval: "[m,p] \<turnstile> exp[(x * const(IntVal b 1))] \<mapsto> val[xv * (IntVal b 1)]"
      by (metis bin_eval.simps(2) evalDet unfold_binary p(1,2) xv)
    then have mulEq: "val[xv * (IntVal b 1)] = xv"
       using eval_unused_bits_zero width xv xvv by auto
     then have "[m,p] \<turnstile> exp[(x * const(IntVal b 1))] \<mapsto> val[xv]"
       using lhsEval by auto
    then show ?thesis
      by (metis evalDet lhsEval p(1) xv)
  qed
  done

optimization AddLeftNegateToSub: "-e + y \<longmapsto> y - e"
  defer apply simp using intval_negateadd_equals_sub_left
  by (metis BinaryExpr BinaryExprE UnaryExprE)

optimization AddRightNegateToSub: "x + -e \<longmapsto> x - e"
  apply simp
  by (metis BinaryExpr BinaryExprE UnaryExprE intval_negateadd_equals_sub_right)

optimization MulEliminator: "((x::i32exp) * const(IntVal 32 0)) \<longmapsto> const(IntVal 32 0)"
  apply (simp add: size_gt_0)
  apply auto
  using Rings.mult_zero_class.mult_zero_right
  using ConstantExpr bin_eval.simps(3) bin_eval_preserves_validity cancel_comm_monoid_add_class.diff_cancel evalDet i32e_eval int_and_equal_bits.simps(1) intval_mul.simps(1) intval_sub.simps(1)
  sorry

lemma "(x::('a::len) word) * 1 = x"
  by simp

optimization MulNeutral: "(x * const(IntVal 32 1)) \<longmapsto> x"
  using mulNeutral_Exp by blast

(*
optimization MulNegate: "(x * const (-1) ) \<mapsto> -x when (stamp_expr x = IntegerStamp 32 l u)"
  apply simp
  apply (metis BinaryExprE ConstantExprE bin_eval.simps(2) neutral_rewrite_helper(1) stamp_implies_valid_value)
  unfolding size.simps by simp
*)
end

(*
experiment begin
value "(3::32 word) mod 32"

lemma "(x::nat) \<ge> 0 \<and> x < base \<Longrightarrow> x mod base = x"
  by simp

lemma word_mod_less: "(x::('a::len) word) < base \<Longrightarrow> x mod base = x"
  by (metis mod_less not_le unat_arith_simps(2) unat_arith_simps(7) unat_mono word_le_less_eq)

value "4294967298::32 word"

lemma shift_equality: "((v1::32 word) << unat ((v2::32 word) mod 32)) = v1 * ((2 ^ (unat v2))::32 word)"
proof -
  have "size_class.size (2 ^ (unat v2)) = 32" sorry
  then have "(2 ^ (unat v2)) < 2 ^ 32"
    using uint_range_size sorry
  then have "unat v2 < 32"
    using nat_power_less_imp_less zero_less_numeral by blast
  then show ?thesis
    using \<open>2 ^ unat v2 < 2 ^ 32\<close> numeral_Bit0 power2_eq_square power_add sorry
qed
end
*)

end
