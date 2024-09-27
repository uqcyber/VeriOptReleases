theory WellFormedExpr
  imports IRTreeEval
begin

fun wf_value :: "Value \<Rightarrow> bool" where
  "wf_value (IntVal b v) = (take_bit b v = v)" |
  "wf_value UndefVal = False" |
  "wf_value (ObjRef ref) = True" |
  "wf_value (ObjStr s) = True" |
  "wf_value (ArrayVal len vs) = (size vs = len)"

definition wf_convert_op :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_convert_op i r = (0 < r \<and> r \<le> i \<and> i \<le> 64)"

fun wf_expr :: "IRExpr \<Rightarrow> bool" where
  "wf_expr (UnaryExpr op e) = wf_expr e" |
  "wf_expr (BinaryExpr op e1 e2) = (wf_expr e1 \<and> wf_expr e2)" |
  "wf_expr (ConditionalExpr c t f) = (wf_expr c \<and> wf_expr t \<and> wf_expr f)" |
  "wf_expr (ConstantExpr c) = wf_value c" |
  "wf_expr (ParameterExpr i s) = valid_stamp s" |
  "wf_expr (LeafExpr i s) = valid_stamp s" |
  "wf_expr (ConstantVar n) = False" |
  "wf_expr (VariableExpr n s) = False"

datatype Type =
  Integer nat |
  Obj |
  Invalid

(*| UnaryNarrow (ir_inputBits: nat) (ir_resultBits: nat)
  | UnarySignExtend (ir_inputBits: nat) (ir_resultBits: nat)
  | UnaryZeroExtend (ir_inputBits: nat) (ir_resultBits: nat)*)



fun type_of :: "IRExpr \<Rightarrow> Type" where
  "type_of (UnaryExpr (UnaryNarrow i r) e) =
    (case (type_of e) of
      Integer n \<Rightarrow> Integer r |
      _ \<Rightarrow> Invalid)" |
  "type_of (UnaryExpr (UnarySignExtend i r) e) =
    (case (type_of e) of
      Integer n \<Rightarrow> Integer r |
      _ \<Rightarrow> Invalid)" |
  "type_of (UnaryExpr (UnaryZeroExtend i r) e) =
    (case (type_of e) of
      Integer n \<Rightarrow> Integer r |
      _ \<Rightarrow> Invalid)" |
  "type_of (UnaryExpr UnaryIsNull e) =
    (case (type_of e) of
      Integer n \<Rightarrow> Integer 32 |
      _ \<Rightarrow> Invalid)" |
  "type_of (UnaryExpr UnaryBitCount e) =
    (case (type_of e) of
      Integer n \<Rightarrow> Integer 32 |
      _ \<Rightarrow> Invalid)" |
  "type_of (UnaryExpr _ e) = type_of e" |
  "type_of (BinaryExpr BinShortCircuitOr e1 e2) =
    (case (type_of e1) of
      Integer n \<Rightarrow> Integer 32 |
      _ \<Rightarrow> Invalid)" |
  "type_of (BinaryExpr BinIntegerEquals e1 e2) =
    (case (type_of e1) of
      Integer n \<Rightarrow> Integer 32 |
      _ \<Rightarrow> Invalid)" |
  "type_of (BinaryExpr BinIntegerLessThan e1 e2) =
    (case (type_of e1) of
      Integer n \<Rightarrow> Integer 32 |
      _ \<Rightarrow> Invalid)" |
  "type_of (BinaryExpr BinIntegerBelow e1 e2) =
    (case (type_of e1) of
      Integer n \<Rightarrow> Integer 32 |
      _ \<Rightarrow> Invalid)" |
  "type_of (BinaryExpr BinIntegerTest e1 e2) =
    (case (type_of e1) of
      Integer n \<Rightarrow> Integer 32 |
      _ \<Rightarrow> Invalid)" |
  "type_of (BinaryExpr BinIntegerNormalizeCompare e1 e2) =
    (case (type_of e1) of
      Integer n \<Rightarrow> Integer 32 |
      _ \<Rightarrow> Invalid)"

fun wf_expr_ctxt :: "MapState \<Rightarrow> Params \<Rightarrow> IRExpr \<Rightarrow> bool" where
  "wf_expr_ctxt m p (UnaryExpr op e) = wf_expr_ctxt m p e" |
  "wf_expr_ctxt m p (BinaryExpr op e1 e2) = (wf_expr_ctxt m p e1 \<and> wf_expr_ctxt m p e2)" |
  "wf_expr_ctxt m p (ConditionalExpr c t f) = (wf_expr_ctxt m p c \<and> wf_expr_ctxt m p t \<and> wf_expr_ctxt m p f)" |
  "wf_expr_ctxt m p (ConstantExpr c) = wf_value c" |
  "wf_expr_ctxt m p (ParameterExpr i s) = valid_stamp s" |
  "wf_expr_ctxt m p (LeafExpr i s) = valid_stamp s" |
  "wf_expr_ctxt m p (ConstantVar n) = False" |
  "wf_expr_ctxt m p (VariableExpr n s) = False"

end