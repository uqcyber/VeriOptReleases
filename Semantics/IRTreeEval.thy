section \<open>Data-flow Semantics\<close>

theory IRTreeEval
  imports
    Graph.Stamp
begin

text \<open>
We define a tree representation of data-flow nodes, as an abstraction of the graph view.

Data-flow trees are evaluated in the context of a method state
(currently called MapState in the theories for historical reasons).

The method state consists of the values for each method parameter, references to
method parameters use an index of the parameter within the parameter list, as such
we store a list of parameter values which are looked up at parameter references.

The method state also stores a mapping of node ids to values. The contents of this
mapping is calculates during the traversal of the control flow graph.

As a concrete example, as the @{term SignedDivNode} can have side-effects
(during division by zero), it is treated as part of the control-flow, since
the data-flow phase is specified to be side-effect free.
As a result, the control-flow semantics for @{term SignedDivNode} calculates the
value of a node and maps the node identifier to the value within the method state.
The data-flow semantics then just reads the value stored in the method state for the node.
\<close>

type_synonym ID = nat
type_synonym MapState = "ID \<Rightarrow> Value"
type_synonym Params = "Value list"

definition new_map_state :: "MapState" where
  "new_map_state = (\<lambda>x. UndefVal)"

(* ======================== START OF NEW TREE STUFF ==========================*)
subsection \<open>Data-flow Tree Representation\<close>

datatype IRUnaryOp =
    UnaryAbs
  | UnaryNeg
  | UnaryNot
  | UnaryLogicNegation
  | UnaryNarrow (ir_inputBits: nat) (ir_resultBits: nat)
  | UnarySignExtend (ir_inputBits: nat) (ir_resultBits: nat)
  | UnaryZeroExtend (ir_inputBits: nat) (ir_resultBits: nat)
  | UnaryIsNull
  | UnaryReverseBytes
  | UnaryBitCount

datatype IRBinaryOp =
    BinAdd
  | BinSub
  | BinMul
  | BinDiv
  | BinMod
  | BinAnd
  | BinOr
  | BinXor
  | BinShortCircuitOr
  | BinLeftShift
  | BinRightShift
  | BinURightShift
  | BinIntegerEquals
  | BinIntegerLessThan
  | BinIntegerBelow
  | BinIntegerTest
  | BinIntegerNormalizeCompare
  | BinIntegerMulHigh

datatype (discs_sels) IRExpr =
    UnaryExpr (ir_uop: IRUnaryOp) (ir_value: IRExpr)
  | BinaryExpr (ir_op: IRBinaryOp) (ir_x: IRExpr) (ir_y: IRExpr)
  | ConditionalExpr (ir_condition: IRExpr) (ir_trueValue: IRExpr) (ir_falseValue: IRExpr)
(* TODO
  | IsNullNode (ir_value: IRExpr) 
  | RefNode ?
*)
  | ParameterExpr (ir_index: nat) (ir_stamp: Stamp)
(* Not needed?
  | PiNode (ir_object: IRExpr) (ir_guard_opt: "IRExpr option")
  | ShortCircuitOrNode (ir_x: IRExpr) (ir_y: IRExpr)
*)
(* Not needed?
  | UnwindNode (ir_exception: IRExpr) 
  | ValueProxyNode (ir_value: IRExpr) (ir_loopExit: IRExpr) 
*)
  | LeafExpr (ir_nid: ID) (ir_stamp: Stamp)
  (* LeafExpr is for pre-evaluated nodes, like LoadFieldNode, SignedDivNode. *) 
  | ConstantExpr (ir_const: Value) (* Ground constant *)
  | ConstantVar (ir_name: String.literal)  (* Pattern variable for constant *)
  | VariableExpr (ir_name: String.literal) (ir_stamp: Stamp) (* Pattern variable for expression *)

fun is_ground :: "IRExpr \<Rightarrow> bool" where
  "is_ground (UnaryExpr op e) = is_ground e" |
  "is_ground (BinaryExpr op e1 e2) = (is_ground e1 \<and> is_ground e2)" |
  "is_ground (ConditionalExpr b e1 e2) = (is_ground b \<and> is_ground e1 \<and> is_ground e2)" |
  "is_ground (ParameterExpr i s) = True" |
  "is_ground (LeafExpr n s) = True" |
  "is_ground (ConstantExpr v) = True" |
  "is_ground (ConstantVar name) = False" |
  "is_ground (VariableExpr name s) = False"

typedef GroundExpr = "{ e :: IRExpr . is_ground e }"
  using is_ground.simps(6) by blast

subsection \<open>Functions for re-calculating stamps\<close> 

text \<open>Note: in Java all integer calculations are done as 32 or 64 bit calculations.
  However, here we generalise the operators to allow any size calculations.
  Many operators have the same output bits as their inputs.
  However, the unary integer operators that are not $normal\_unary$ are narrowing 
  or widening operators, so the result bits is specified by the operator.
  The binary integer operators are divided into three groups:
  (1) $binary\_fixed\_32$ operators always output 32 bits,
  (2) $binary\_shift\_ops$ operators output size is determined by their left argument,
  and (3) other operators output the same number of bits as both their inputs.
\<close>

abbreviation binary_normal :: "IRBinaryOp set" where
  "binary_normal \<equiv> {BinAdd, BinMul, BinDiv, BinMod, BinSub, BinAnd, BinOr, BinXor}"

abbreviation binary_fixed_32_ops :: "IRBinaryOp set" where
  "binary_fixed_32_ops \<equiv> {BinShortCircuitOr, BinIntegerEquals, BinIntegerLessThan, BinIntegerBelow, BinIntegerTest, BinIntegerNormalizeCompare}"

abbreviation binary_shift_ops :: "IRBinaryOp set" where
  "binary_shift_ops \<equiv> {BinLeftShift, BinRightShift, BinURightShift}"

(* TODO add a note into the text above about this?

  Describes operators whose output width matches the input (for 32 or 64), otherwise the output is
  UndefVal.
*)
abbreviation binary_fixed_ops :: "IRBinaryOp set" where
  "binary_fixed_ops \<equiv> {BinIntegerMulHigh}"

abbreviation normal_unary :: "IRUnaryOp set" where
  "normal_unary \<equiv> {UnaryAbs, UnaryNeg, UnaryNot, UnaryLogicNegation, UnaryReverseBytes}"

(* TODO add a note into the text above about this ? *)
abbreviation unary_fixed_32_ops :: "IRUnaryOp set" where
  "unary_fixed_32_ops \<equiv> {UnaryBitCount}"

(* TODO add a note into the text above about this ? *)
abbreviation boolean_unary :: "IRUnaryOp set" where
  "boolean_unary \<equiv> {UnaryIsNull}"

(* Helpful set lemmas *)

lemma binary_ops_all:
  shows "op \<in> binary_normal \<or> op \<in> binary_fixed_32_ops \<or> op \<in> binary_fixed_ops \<or> op \<in> binary_shift_ops"
  by (cases op; auto)

lemma binary_ops_distinct_normal:
  shows "op \<in> binary_normal \<Longrightarrow> op \<notin> binary_fixed_32_ops \<and> op \<notin> binary_fixed_ops \<and> op \<notin> binary_shift_ops"
  by auto

lemma binary_ops_distinct_fixed_32:
  shows "op \<in> binary_fixed_32_ops \<Longrightarrow> op \<notin> binary_normal \<and> op \<notin> binary_fixed_ops \<and> op \<notin> binary_shift_ops"
  by auto

lemma binary_ops_distinct_fixed:
  shows "op \<in> binary_fixed_ops \<Longrightarrow> op \<notin> binary_fixed_32_ops \<and> op \<notin> binary_normal \<and> op \<notin> binary_shift_ops"
  by auto

lemma binary_ops_distinct_shift:
  shows  "op \<in> binary_shift_ops \<Longrightarrow> op \<notin> binary_fixed_32_ops \<and> op \<notin> binary_fixed_ops \<and> op \<notin> binary_normal"
  by auto

lemma unary_ops_distinct:
  shows "op \<in> normal_unary \<Longrightarrow> op \<notin> boolean_unary \<and> op \<notin> unary_fixed_32_ops"
  and   "op \<in> boolean_unary \<Longrightarrow> op \<notin> normal_unary \<and> op \<notin> unary_fixed_32_ops"
  and   "op \<in> unary_fixed_32_ops \<Longrightarrow> op \<notin> boolean_unary \<and> op \<notin> normal_unary"
  by auto

fun stamp_unary :: "IRUnaryOp \<Rightarrow> Stamp \<Rightarrow> Stamp" where
(* WAS:
  "stamp_unary op (IntegerStamp b lo hi) =
    (let bits = (if op \<in> normal_unary 
                 then (if b=64 then 64 else 32)
                 else (ir_resultBits op)) in
    unrestricted_stamp (IntegerStamp bits lo hi))" |
*)
(* TODO update to generalise all boolean_unary operators to return IntegerStamp 32 0 1 *)
  "stamp_unary UnaryIsNull _ = (IntegerStamp 32 0 1)" |
  "stamp_unary op (IntegerStamp b lo hi) =
     unrestricted_stamp (IntegerStamp 
                        (if op \<in> normal_unary       then b  else
                         if op \<in> boolean_unary      then 32 else
                         if op \<in> unary_fixed_32_ops then 32 else
                          (ir_resultBits op)) lo hi)" |
  (* for now... *)
  "stamp_unary op _ = IllegalStamp"

fun stamp_binary :: "IRBinaryOp \<Rightarrow> Stamp \<Rightarrow> Stamp \<Rightarrow> Stamp" where
  "stamp_binary op (IntegerStamp b1 lo1 hi1) (IntegerStamp b2 lo2 hi2) =
    (if op \<in> binary_shift_ops then unrestricted_stamp (IntegerStamp b1 lo1 hi1)
     else if b1 \<noteq> b2 then IllegalStamp else
      (if op \<in> binary_fixed_32_ops
       then unrestricted_stamp (IntegerStamp 32 lo1 hi1)
       else unrestricted_stamp (IntegerStamp b1 lo1 hi1)))" |
  (* for now... *)
  "stamp_binary op _ _ = IllegalStamp"

fun stamp_expr :: "IRExpr \<Rightarrow> Stamp" where
  "stamp_expr (UnaryExpr op x) = stamp_unary op (stamp_expr x)" |
  "stamp_expr (BinaryExpr bop x y) = stamp_binary bop (stamp_expr x) (stamp_expr y)" |
  "stamp_expr (ConstantExpr val) = constantAsStamp val" |
  "stamp_expr (LeafExpr i s) = s" |
  "stamp_expr (ParameterExpr i s) = s" |
  "stamp_expr (ConditionalExpr c t f) = meet (stamp_expr t) (stamp_expr f)"

export_code stamp_unary stamp_binary stamp_expr

subsection \<open>Data-flow Tree Evaluation\<close>

fun unary_eval :: "IRUnaryOp \<Rightarrow> Value \<Rightarrow> Value" where
  "unary_eval UnaryAbs v = intval_abs v" |
  "unary_eval UnaryNeg v = intval_negate v" |
  "unary_eval UnaryNot v = intval_not v" |
  "unary_eval UnaryLogicNegation v = intval_logic_negation v" |
  "unary_eval (UnaryNarrow inBits outBits) v = intval_narrow inBits outBits v" |
  "unary_eval (UnarySignExtend inBits outBits) v = intval_sign_extend inBits outBits v" |
  "unary_eval (UnaryZeroExtend inBits outBits) v = intval_zero_extend inBits outBits v" |
  "unary_eval UnaryIsNull v = intval_is_null v" |
  "unary_eval UnaryReverseBytes v = intval_reverse_bytes v" |
  "unary_eval UnaryBitCount v = intval_bit_count v"
(*  "unary_eval op v1 = UndefVal" *)

fun bin_eval :: "IRBinaryOp \<Rightarrow> Value \<Rightarrow> Value \<Rightarrow> Value" where
  "bin_eval BinAdd v1 v2 = intval_add v1 v2" |
  "bin_eval BinSub v1 v2 = intval_sub v1 v2" |
  "bin_eval BinMul v1 v2 = intval_mul v1 v2" |
  "bin_eval BinDiv v1 v2 = intval_div v1 v2" |
  "bin_eval BinMod v1 v2 = intval_mod v1 v2" |
  "bin_eval BinAnd v1 v2 = intval_and v1 v2" |
  "bin_eval BinOr  v1 v2 = intval_or v1 v2" |
  "bin_eval BinXor v1 v2 = intval_xor v1 v2" |
  "bin_eval BinShortCircuitOr v1 v2 = intval_short_circuit_or v1 v2" |
  "bin_eval BinLeftShift v1 v2 = intval_left_shift v1 v2" |
  "bin_eval BinRightShift v1 v2 = intval_right_shift v1 v2" |
  "bin_eval BinURightShift v1 v2 = intval_uright_shift v1 v2" |
  "bin_eval BinIntegerEquals v1 v2 = intval_equals v1 v2" |
  "bin_eval BinIntegerLessThan v1 v2 = intval_less_than v1 v2" |
  "bin_eval BinIntegerBelow v1 v2 = intval_below v1 v2" |
  "bin_eval BinIntegerTest v1 v2 = intval_test v1 v2" |
  "bin_eval BinIntegerNormalizeCompare v1 v2 = intval_normalize_compare v1 v2" |
  "bin_eval BinIntegerMulHigh v1 v2 = intval_mul_high v1 v2"
(*  "bin_eval op v1 v2 = UndefVal" *)

lemma defined_eval_is_intval:
  shows "bin_eval op x y \<noteq> UndefVal \<Longrightarrow> (is_IntVal x \<and> is_IntVal y)"
  by (cases op; cases x; cases y; auto)

lemmas eval_thms =
  intval_abs.simps intval_negate.simps intval_not.simps
  intval_logic_negation.simps intval_narrow.simps
  intval_sign_extend.simps intval_zero_extend.simps
  intval_add.simps intval_mul.simps intval_sub.simps
  intval_and.simps intval_or.simps intval_xor.simps
  intval_left_shift.simps intval_right_shift.simps
  intval_uright_shift.simps intval_equals.simps
  intval_less_than.simps intval_below.simps

inductive not_undef_or_fail :: "Value \<Rightarrow> Value \<Rightarrow> bool" where
  "\<lbrakk>value \<noteq> UndefVal\<rbrakk> \<Longrightarrow> not_undef_or_fail value value"

notation (latex output) (* we can pretend intval_* are partial functions *)
  not_undef_or_fail ("_ = _")

inductive
  evaltree :: "MapState \<Rightarrow> Params \<Rightarrow> IRExpr \<Rightarrow> Value \<Rightarrow> bool" ("[_,_] \<turnstile> _ \<mapsto> _" 55)
  for m p where

  ConstantExpr:
  "\<lbrakk>wf_value c\<rbrakk>
    \<Longrightarrow> [m,p] \<turnstile> (ConstantExpr c) \<mapsto> c" |

  ParameterExpr:
  "\<lbrakk>i < length p; valid_value (p!i) s\<rbrakk>
    \<Longrightarrow> [m,p] \<turnstile> (ParameterExpr i s) \<mapsto> p!i" |

  (* We need to add this to prove certain optimizations
     but it also requires more work to show monotonicity of refinement.
  compatible (stamp_expr te) (stamp_expr fe);*)
  ConditionalExpr:
  "\<lbrakk>[m,p] \<turnstile> ce \<mapsto> cond;
    cond \<noteq> UndefVal;
    branch = (if val_to_bool cond then te else fe);
    [m,p] \<turnstile> branch \<mapsto> result;
    result \<noteq> UndefVal;

    [m,p] \<turnstile> te \<mapsto> true;  true  \<noteq> UndefVal;
    [m,p] \<turnstile> fe \<mapsto> false; false \<noteq> UndefVal\<rbrakk>
    \<Longrightarrow> [m,p] \<turnstile> (ConditionalExpr ce te fe) \<mapsto> result" |

  UnaryExpr:
  "\<lbrakk>[m,p] \<turnstile> xe \<mapsto> x;
    result = (unary_eval op x);
    result \<noteq> UndefVal\<rbrakk>
    \<Longrightarrow> [m,p] \<turnstile> (UnaryExpr op xe) \<mapsto> result" |

  BinaryExpr:
  "\<lbrakk>[m,p] \<turnstile> xe \<mapsto> x;
    [m,p] \<turnstile> ye \<mapsto> y;
    result = (bin_eval op x y);
    result \<noteq> UndefVal\<rbrakk>
    \<Longrightarrow> [m,p] \<turnstile> (BinaryExpr op xe ye) \<mapsto> result" |

  LeafExpr:
  "\<lbrakk>val = m n;
    valid_value val s\<rbrakk>
    \<Longrightarrow> [m,p] \<turnstile> LeafExpr n s \<mapsto> val"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as evalT)
  [show_steps,show_mode_inference,show_intermediate_results] 
  evaltree .

inductive
  evaltrees :: "MapState \<Rightarrow> Params \<Rightarrow> IRExpr list \<Rightarrow> Value list \<Rightarrow> bool" ("[_,_] \<turnstile> _ \<mapsto>\<^sub>L _" 55)
  for m p where

  EvalNil:
  "[m,p] \<turnstile> [] \<mapsto>\<^sub>L []" |

  EvalCons:
  "\<lbrakk>[m,p] \<turnstile> x \<mapsto> xval;
    [m,p] \<turnstile> yy \<mapsto>\<^sub>L yyval\<rbrakk>
    \<Longrightarrow> [m,p] \<turnstile> (x#yy) \<mapsto>\<^sub>L (xval#yyval)"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as evalTs)
  evaltrees .

definition sq_param0 :: IRExpr where
  "sq_param0 = BinaryExpr BinMul 
    (ParameterExpr 0 (IntegerStamp 32 (- 2147483648) 2147483647))
    (ParameterExpr 0 (IntegerStamp 32 (- 2147483648) 2147483647))"

values "{v. evaltree new_map_state [IntVal 32 5] sq_param0 v}"

(* We add all the inductive rules as unsafe intro rules. *)
declare evaltree.intros [intro]
declare evaltrees.intros [intro]

(* We derive a safe elimination (forward) reasoning rule for each case.
  Note that each pattern is as general as possible. *)
inductive_cases ConstantExprE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[m,p] \<turnstile> (ConstantExpr c) \<mapsto> val"
inductive_cases ParameterExprE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[m,p] \<turnstile> (ParameterExpr i s) \<mapsto> val"
inductive_cases ConditionalExprE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[m,p] \<turnstile> (ConditionalExpr c t f) \<mapsto> val"
inductive_cases UnaryExprE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[m,p] \<turnstile> (UnaryExpr op xe) \<mapsto> val"
inductive_cases BinaryExprE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[m,p] \<turnstile> (BinaryExpr op xe ye) \<mapsto> val"
inductive_cases LeafExprE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[m,p] \<turnstile> (LeafExpr n s) \<mapsto> val"
inductive_cases ConstantVarE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[m,p] \<turnstile> (ConstantVar x) \<mapsto> val"
inductive_cases VariableExprE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[m,p] \<turnstile> (VariableExpr x s) \<mapsto> val"
inductive_cases EvalNilE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[m,p] \<turnstile> [] \<mapsto>\<^sub>L vals"
inductive_cases EvalConsE[elim!]:\<^marker>\<open>tag invisible\<close>
  "[m,p] \<turnstile> (x#yy) \<mapsto>\<^sub>L vals"

(* group these forward rules into a named set *)
lemmas EvalTreeE\<^marker>\<open>tag invisible\<close> = 
  ConstantExprE
  ParameterExprE
  ConditionalExprE
  UnaryExprE
  BinaryExprE
  LeafExprE
  ConstantVarE
  VariableExprE
  EvalNilE
  EvalConsE

subsection \<open>Data-flow Tree Refinement\<close>

text \<open>We define the induced semantic equivalence relation between expressions.
  Note that syntactic equality implies semantic equivalence, but not vice versa.
\<close>
definition equiv_exprs :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" ("_ \<doteq> _" 55) where
  "(e1 \<doteq> e2) = (\<forall> m p v. (([m,p] \<turnstile> e1 \<mapsto> v) \<longleftrightarrow> ([m,p] \<turnstile> e2 \<mapsto> v)))"

text \<open>We also prove that this is a total equivalence relation (@{term "equivp equiv_exprs"})
  (HOL.Equiv\_Relations), so that we can reuse standard results about equivalence relations.
\<close>
lemma "equivp equiv_exprs"
  apply (auto simp add: equivp_def equiv_exprs_def) by (metis equiv_exprs_def)+

text \<open>We define a refinement ordering over IRExpr and show that it is a preorder.
  Note that it is asymmetric because e2 may refer to fewer variables than e1.
\<close>
instantiation IRExpr :: preorder begin

notation less_eq (infix "\<sqsubseteq>" 65)

definition
  le_expr_def [simp]:
    "(e\<^sub>2 \<le> e\<^sub>1) \<longleftrightarrow> (\<forall> m p v. (([m,p] \<turnstile> e\<^sub>1 \<mapsto> v) \<longrightarrow> ([m,p] \<turnstile> e\<^sub>2 \<mapsto> v)))"

definition
  lt_expr_def [simp]:
    "(e\<^sub>1 < e\<^sub>2) \<longleftrightarrow> (e\<^sub>1 \<le> e\<^sub>2 \<and> \<not> (e\<^sub>1 \<doteq> e\<^sub>2))"

instance proof 
  fix x y z :: IRExpr
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> (y \<le> x)" by (simp add: equiv_exprs_def; auto)
  show "x \<le> x" by simp
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by simp 
qed

end

abbreviation (output) Refines :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" (infix "\<sqsupseteq>" 64)
  where "e\<^sub>1 \<sqsupseteq> e\<^sub>2 \<equiv> (e\<^sub>2 \<le> e\<^sub>1)"

subsection \<open>Stamp Masks\<close>

text \<open>
A stamp can contain additional range information in the form of masks.
A stamp has an up mask and a down mask,
corresponding to a the bits that may be set and the bits that must be set.

Examples:
  A stamp where no range information is known will have;
    an up mask of -1 as all bits may be set, and
    a down mask of 0 as no bits must be set.

  A stamp known to be one should have;
    an up mask of 1 as only the first bit may be set, no others, and
    a down mask of 1 as the first bit must be set and no others.

We currently don't carry mask information in stamps,
and instead assume correct masks to prove optimizations.
\<close>

locale stamp_mask =
  fixes up :: "IRExpr \<Rightarrow> int64" ("\<up>")
  fixes down :: "IRExpr \<Rightarrow> int64" ("\<down>")
  assumes up_spec: "[m, p] \<turnstile> e \<mapsto> IntVal b v \<Longrightarrow> (and v (not ((ucast (\<up>e))))) = 0"
      and down_spec: "[m, p] \<turnstile> e \<mapsto> IntVal b v \<Longrightarrow> (and (not v) (ucast (\<down>e))) = 0"
begin

lemma may_implies_either:
  "[m, p] \<turnstile> e \<mapsto> IntVal b v \<Longrightarrow> bit (\<up>e) n \<Longrightarrow> bit v n = False \<or> bit v n = True"
  by simp

lemma not_may_implies_false:
  "[m, p] \<turnstile> e \<mapsto> IntVal b v \<Longrightarrow> \<not>(bit (\<up>e) n) \<Longrightarrow> bit v n = False"
  by (metis (no_types, lifting) bit.double_compl up_spec bit_and_iff bit_not_iff bit_unsigned_iff 
      down_spec)

lemma must_implies_true:
  "[m, p] \<turnstile> e \<mapsto> IntVal b v \<Longrightarrow> bit (\<down>e) n \<Longrightarrow> bit v n = True"
  by (metis bit.compl_one bit_and_iff bit_minus_1_iff bit_not_iff impossible_bit ucast_id down_spec)

lemma not_must_implies_either:
  "[m, p] \<turnstile> e \<mapsto> IntVal b v \<Longrightarrow> \<not>(bit (\<down>e) n) \<Longrightarrow> bit v n = False \<or> bit v n = True"
  by simp

lemma must_implies_may:
  "[m, p] \<turnstile> e \<mapsto> IntVal b v \<Longrightarrow> n < 32 \<Longrightarrow> bit (\<down>e) n \<Longrightarrow> bit (\<up>e) n"
  by (meson must_implies_true not_may_implies_false)

lemma up_mask_and_zero_implies_zero:
  assumes "and (\<up>x) (\<up>y) = 0"
  assumes "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
  assumes "[m, p] \<turnstile> y \<mapsto> IntVal b yv"
  shows "and xv yv = 0"
  by (smt (z3) assms and.commute and.right_neutral bit.compl_zero bit.conj_cancel_right ucast_id
      bit.conj_disj_distribs(1) up_spec word_bw_assocs(1) word_not_dist(2) word_ao_absorbs(8)
      and_eq_not_not_or)

lemma not_down_up_mask_and_zero_implies_zero:
  assumes "and (not (\<down>x)) (\<up>y) = 0"
  assumes "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
  assumes "[m, p] \<turnstile> y \<mapsto> IntVal b yv"
  shows "and xv yv = yv"
  by (metis (no_types, opaque_lifting) assms bit.conj_cancel_left bit.conj_disj_distribs(1,2)
      bit.de_Morgan_disj ucast_id down_spec or_eq_not_not_and up_spec word_ao_absorbs(2,8)
      word_bw_lcs(1) word_not_dist(2))

end

definition IRExpr_up :: "IRExpr \<Rightarrow> int64" where
  "IRExpr_up e = not 0"

definition IRExpr_down :: "IRExpr \<Rightarrow> int64" where
  "IRExpr_down e = 0"

lemma ucast_zero: "(ucast (0::int64)::int32) = 0"
  by simp

lemma ucast_minus_one: "(ucast (-1::int64)::int32) = -1"
  apply transfer by auto

interpretation simple_mask: stamp_mask
  "IRExpr_up :: IRExpr \<Rightarrow> int64"
  "IRExpr_down :: IRExpr \<Rightarrow> int64"
  apply unfold_locales
  by (simp add: ucast_minus_one IRExpr_up_def IRExpr_down_def)+

end
