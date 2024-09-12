theory ConditionDSL
  imports JavaAST
  keywords
    "register_method" :: thy_decl and
    "define_semantics" :: thy_decl
begin

type_synonym ClassName = String.literal

fun unary_op_class :: "IRUnaryOp \<Rightarrow> ClassName" where
  "unary_op_class UnaryAbs = STR ''AbsNode''" |
  "unary_op_class UnaryNeg = STR ''NegateNode''" |
  "unary_op_class UnaryNot = STR ''NotNode''" |
  "unary_op_class UnaryLogicNegation = STR ''LogicNegationNode''" |
  "unary_op_class (UnaryNarrow _ _) = STR ''NarrowNode''" |
  "unary_op_class (UnarySignExtend _ _) = STR ''SignExtendNode''" |
  "unary_op_class (UnaryZeroExtend _ _) = STR ''ZeroExtendNode''" |
  "unary_op_class UnaryIsNull = STR ''IsNullNode''" |
  "unary_op_class UnaryReverseBytes = STR ''ReverseBytesNode''" |
  "unary_op_class UnaryBitCount = STR ''BitCountNode''"

fun binary_op_class :: "IRBinaryOp \<Rightarrow> ClassName" where
  "binary_op_class BinAdd = STR ''AddNode''" |
  "binary_op_class BinMul = STR ''MulNode''" |
  "binary_op_class BinSub = STR ''SubNode''" |
  "binary_op_class BinAnd = STR ''AndNode''" |
  "binary_op_class BinOr = STR ''OrNode''" |
  "binary_op_class BinXor = STR ''XorNode''" |
  "binary_op_class BinShortCircuitOr = STR ''ShortCircuitOrNode''" |
  "binary_op_class BinLeftShift = STR ''LeftShiftNode''" |
  "binary_op_class BinRightShift = STR ''RightShiftNode''" |
  "binary_op_class BinURightShift = STR ''UnaryRightShiftNode''" |
  "binary_op_class BinIntegerEquals = STR ''IntegerEqualsNode''" |
  "binary_op_class BinIntegerLessThan = STR ''IntegerLessThanNode''" |
  "binary_op_class BinIntegerBelow = STR ''IntegerBelowNode''" |
  "binary_op_class BinIntegerTest = STR ''IntegerTestNode''" |
  "binary_op_class BinIntegerNormalizeCompare = STR ''IntegerNormalizeCompareNode''" |
  "binary_op_class BinIntegerMulHigh = STR ''IntegerMulHighNode''"

fun class_name :: "IRExpr \<Rightarrow> ClassName option" where
  "class_name (UnaryExpr op v) = Some (unary_op_class op)" |
  "class_name (BinaryExpr op v1 v2) = Some (binary_op_class op)" |
  "class_name (ConditionalExpr v1 v2 v3) = Some (STR ''ConditionalNode'')" |
  "class_name (ConstantExpr _) = Some (STR ''ConstantNode'')" |
  "class_name _ = None"

fun stamp_class_name :: "Stamp \<Rightarrow> ClassName" where
  "stamp_class_name (IntegerStamp b l h) = STR ''IntegerStamp''" |
  "stamp_class_name (VoidStamp) = STR ''VoidStamp''" |
  "stamp_class_name (KlassPointerStamp x y) = STR ''KlassPointerStamp''" |
  "stamp_class_name (MethodCountersPointerStamp x y) = STR ''MethodCountersPointerStamp''" |
  "stamp_class_name (MethodPointersStamp x y) = STR ''MethodPointersStamp''" |
  "stamp_class_name (ObjectStamp _ _ _ _) = STR ''ObjectStamp''" |
  "stamp_class_name (RawPointerStamp _ _) = STR ''RawPointerStamp''" |
  "stamp_class_name (IllegalStamp) = STR ''IllegalStamp''"

datatype Condition =
  Unary IRUnaryOp Condition |
  Binary IRBinaryOp Condition Condition |
  Constant int |
  Value Value |
  Variable String.literal |
  Expr IRExpr |
  Stamp Stamp |

  Combine Condition Condition (infixl ";" 86) |

  InstanceOf Condition String.literal |
  Method Condition String.literal "Condition list"

inductive coerce_to_bool :: "Condition \<Rightarrow> bool \<Rightarrow> bool" where
  "coerce_to_bool (Constant num) (num > 0)" |
  "coerce_to_bool (Value val) (val_to_bool val)" |
  "coerce_to_bool lhs lhs' \<and> coerce_to_bool rhs rhs' \<Longrightarrow> coerce_to_bool (Combine lhs rhs) (lhs' \<and> rhs')"

inductive base_semantics :: "Condition \<Rightarrow> Condition \<Rightarrow> bool" where
  "base_semantics e (Value v) \<and> res = (unary_eval op v) \<Longrightarrow> base_semantics (Unary op e) (Value res)" |
  "base_semantics x (Value xv) \<and> base_semantics y (Value yv) \<and> res = (bin_eval op xv yv) 
    \<Longrightarrow> base_semantics (Binary op x y) (Value res)" |
  "base_semantics (Constant v') (Value (IntVal 64 (word_of_int v')))" |
  "base_semantics (Value v) (Value v)" |
  "base_semantics (Expr e) (Expr e)" |
  "base_semantics (Stamp s) (Stamp s)" |
  "base_semantics lhs lhs' \<and> base_semantics rhs rhs' \<Longrightarrow> base_semantics (Combine lhs rhs) (Combine lhs' rhs')" |
  "base_semantics e (Expr e') \<and> class_name e' = Some class \<Longrightarrow> base_semantics (InstanceOf e class) (Value (IntVal 32 1))" |
  "base_semantics e (Expr e') \<and> class_name e' \<noteq> Some class \<Longrightarrow> base_semantics (InstanceOf e class) (Value (IntVal 32 0))" |
  "base_semantics e (Stamp s) \<and> stamp_class_name s = class \<Longrightarrow> base_semantics (InstanceOf e class) (Value (IntVal 32 1))" |
  "base_semantics e (Stamp s) \<and> stamp_class_name s \<noteq> class \<Longrightarrow> base_semantics (InstanceOf e class) (Value (IntVal 32 0))"

syntax
  "_method" :: "Condition \<Rightarrow> any \<Rightarrow> args => Condition" ("_.._'(_')" 45)
  "_method_empty" :: "Condition \<Rightarrow> any => Condition" ("_.._'(')" 45)
  "_method_syntax" :: "Condition \<Rightarrow> any \<Rightarrow> args => Condition"

translations
  "i..m(x, xs)" \<rightharpoonup> "_method_syntax i m (x#[xs])"
  "i..m(x)" \<rightharpoonup> "_method_syntax i m (x#[])"
  "i..m()" \<rightharpoonup> "_method_syntax i m ([])"

ML \<open>
fun first_free trm =
  (case trm of
    (x $ y) => (case (first_free x) of NONE => first_free y | SOME n => SOME n)
    | Free (str, _) => SOME str
    | _ => NONE);

fun isabelle_string ctxt str = Syntax.read_term ctxt ("STR ''" ^  str ^ "''")

fun parse_method ctxt [obj, method, args] =
  let
    val method_name = (case (first_free method) of 
      NONE => raise TERM ("cannot parse method name", [method]) | 
      SOME name => name);
    
    val method_string = (isabelle_string ctxt method_name);
  in
    @{term "Method"} $ obj $ method_string $ args
  end
  | parse_method _ ts = raise TERM ("markup_expr", ts)
\<close>

parse_translation \<open> [( @{syntax_const "_method_syntax"} , parse_method)] \<close>

ML_val \<open>@{term "x..stamp(a, b, c, d)"}\<close>
value "x..stamp(a, b, c)"

syntax
  "_instanceof" :: "Condition \<Rightarrow> id_position => Condition" ("_ instanceof _")

ML \<open>
fun parse_instanceof ctxt [obj, class] =
  let
    val class_name = (case (first_free class) of 
      NONE => raise TERM ("cannot parse class name", [class]) | 
      SOME name => name);
    
    val class_string = (isabelle_string ctxt class_name);
  in
    @{term "InstanceOf"} $ obj $ class_string
  end
  | parse_instanceof _ ts = raise TERM ("markup_expr", ts)
\<close>

parse_translation \<open> [( @{syntax_const "_instanceof"} , parse_instanceof)] \<close>

(*
bundle condition_syntax
begin

notation
  not  (\<open>NOT\<close>)
    and "and"  (infixr \<open>AND\<close> 64)
    and or  (infixr \<open>OR\<close>  59)
    and xor  (infixr \<open>XOR\<close> 59)

end
*)

ML \<open>
fun semantics_code _ name rule =
  @{const Trueprop} 
  $ ((Const ("HOL.eq", @{typ "(Condition \<Rightarrow> Condition list \<Rightarrow> Condition) \<Rightarrow> (Condition \<Rightarrow> Condition list \<Rightarrow> Condition) \<Rightarrow> bool"})
  $ (Free ((Binding.name_of (name)) ^ "_semantics", @{typ "(Condition \<Rightarrow> Condition list \<Rightarrow> Condition)"}))
  $ rule))

fun translation_code _ name rule =
  @{const Trueprop} 
  $ ((Const ("HOL.eq", @{typ "(string \<Rightarrow> string list \<Rightarrow> string) \<Rightarrow> (string \<Rightarrow> string list \<Rightarrow> string) \<Rightarrow> bool"})
  $ (Free ((Binding.name_of (name)) ^ "_translation", @{typ "(string \<Rightarrow> string list \<Rightarrow> string)"}))
  $ rule))

structure MethodData = Theory_Data
(
  type T = string list;
  val empty = [];
  fun merge (lhs, rhs) = lhs @ rhs
);

val state = MethodData.get;

fun register_method_cmd name semantics translation thy =
  let
    val semantics_term = (Syntax.parse_term thy semantics);
    val (_, thy') = Specification.definition
      NONE [] []
      ((Binding.suffix_name "_semantics" (fst name), []), (semantics_code thy (fst name) semantics_term))
      thy

    val translation_term = (Syntax.parse_term thy translation);
    val (_, thy'') = Specification.definition
      NONE [] []
      ((Binding.suffix_name "_translation" (fst name), []), (translation_code thy (fst name) translation_term))
      thy'

    val register = (fn state => MethodData.put ((MethodData.get state) @ [Binding.name_of (fst name)]) state);
    val thy''' = Local_Theory.background_theory register thy'';
  in
    thy'''
  end

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>register_method\<close>
    "support a new built-in Java/GraalVM method"
    (Parse_Spec.thm_name ":" -- Parse.term -- Parse.term
      >> (fn ((name, semantics), translation) => (register_method_cmd name semantics translation)));
      (*(fn name => Toplevel.theory (fn state => export_phases state name)))*)

fun rename_const n v (Const (x, T)) =
        (if x = n then Free (v, T) else Const (x, T))
    | rename_const n v (Abs (x, T, t)) = (Abs (x, T, rename_const n v t))
    | rename_const n v (t $ u) = (rename_const n v t $ rename_const n v u)
    | rename_const _ _ e = e;

fun define_method_call name ctxt method =
   Const ("Pure.imp", @{typ "prop \<Rightarrow> prop \<Rightarrow> prop"}) $ 
    (Const ("HOL.Trueprop", @{typ "bool \<Rightarrow> prop"}) $ 
      (Const ("HOL.conj", @{typ "bool \<Rightarrow> bool \<Rightarrow> bool"}) $
        (Const ("HOL.conj", @{typ "bool \<Rightarrow> bool \<Rightarrow> bool"}) $
          (Const ("HOL.eq", @{typ "String.literal \<Rightarrow> String.literal \<Rightarrow> bool"}) $ Free ("name", @{typ "String.literal"}) $ isabelle_string ctxt method) $
            (Const ("HOL.conj", @{typ "bool \<Rightarrow> bool \<Rightarrow> bool"}) $
              (Free (name, @{typ "Condition => Condition => bool"}) $ Free ("c", @{typ "Condition"}) $ (Free ("obj", @{typ "Condition"}))) $
              (Const ("HOL.eq", @{typ "Condition \<Rightarrow> Condition \<Rightarrow> bool"}) $ 
                Free ("c'", @{typ "Condition"}) $
                (Const ("ConditionDSL." ^ method ^ "_semantics", @{typ "Condition \<Rightarrow> Condition list \<Rightarrow> Condition"}) 
                $ Free ("obj", @{typ "Condition"}) $ Free ("params", @{typ "Condition list"})))
            )
        ) $
        (Free (name, @{typ "Condition => Condition => bool"}) $ Free ("c'", @{typ "Condition"}) $ (Free ("c''", @{typ "Condition"})))
      )) $
      
    (Const ("HOL.Trueprop", @{typ "bool \<Rightarrow> prop"}) $
      (Free (name, @{typ "Condition => Condition => bool"}) 
        $ (@{term "Method"} $ Free ("c", @{typ "Condition"}) $ Free ("name", @{typ "String.literal"}) $ Free ("params", @{typ "Condition list"}))
         $ (Free ("c''", @{typ "Condition"}))))

fun define_method_calls name ctxt = map (define_method_call name ctxt)

fun define_semantics_cmd name thy =
  let
    val methods = MethodData.get (Proof_Context.theory_of thy);
    val method_calls = (define_method_calls name thy methods);

    val intrs = map Thm.full_prop_of (#intrs (snd (Inductive.the_inductive thy @{term base_semantics})));
    val intrs' = map Term.close_schematic_term intrs;
    val intrs'' = map (rename_const "ConditionDSL.base_semantics" name) intrs';
    val intrs''' = (map (snd o Term.strip_abs_eta 10) intrs'');
    val rules = intrs''' @ method_calls;
    (*val _ = @{print} (Syntax.unparse_term thy intrs''');*)
    val (res, thy') = (Inductive.add_inductive {quiet_mode = true, verbose = false, alt_name = Binding.name name,
           coind = false, no_elim = false, no_ind = false, skip_mono = false}
          (map (fn (s, T) => ((Binding.name s, T), NoSyn)) [(name, @{typ "Condition \<Rightarrow> Condition \<Rightarrow> bool"})])
          (*([] @ vars)[("c", @{typ Condition}), ("v", @{typ Value})]*) []
          (*(map dest_Free [@{term \<open>x y\<close>}])*)
          (map (fn x => (Binding.empty_atts, x)) (rules (*@ [@{term \<open>hello c v \<Longrightarrow> hello (c::Condition) (v::Value)\<close>}]*))) []) thy;
    val pretty = Pretty.big_list name (map (Syntax.pretty_term thy' o Thm.full_prop_of) (#intrs res));
    val _ = (fn _ =>
      Print_Mode.with_modes [] (fn () => writeln (Pretty.string_of pretty)) ()) thy';
    (*val thy'' = Predicate_Compile.preprocess Predicate_Compile_Aux.default_options (Thm.full_prop_of (#induct res)) thy';*)
    
  in
    thy'
  end

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>define_semantics\<close>
    "construct a new inductive definition of condition semantics"
    (Parse.name 
      >> (fn (name) => (define_semantics_cmd name)));
\<close>

define_semantics myCoolSemantics

thm myCoolSemantics.intros

print_inductives

fun stamp_of :: "Condition \<Rightarrow> Condition list \<Rightarrow> Condition" where
  "stamp_of (Expr e) _ = Stamp (stamp_expr e)"

fun generate_stamp :: "string \<Rightarrow> string list \<Rightarrow> string" where
  "generate_stamp e _ = e @ ''.stamp(view)''"

register_method stamp: stamp_of generate_stamp

fun upMask_of :: "Condition \<Rightarrow> Condition list \<Rightarrow> Condition" where
  "upMask_of (Stamp s) _ = (Constant 0)"

fun generate_upMask :: "string \<Rightarrow> string list \<Rightarrow> string" where
  "generate_upMask e _ = e @ ''.mayBeSet()''"

register_method upMask: upMask_of generate_upMask
register_method mayBeSet: upMask_of generate_upMask

fun downMask_of :: "Condition \<Rightarrow> Condition list \<Rightarrow> Condition" where
  "downMask_of (Stamp s) _ = (Constant 0)"

fun generate_downMask :: "string \<Rightarrow> string list \<Rightarrow> string" where
  "generate_downMask e _ = e @ ''.mustBeSet()''"

register_method downMask: downMask_of generate_downMask
register_method mustBeSet: downMask_of generate_downMask

fun lowerBound_of :: "Condition \<Rightarrow> Condition list \<Rightarrow> Condition" where
  "lowerBound_of (Stamp s) _ = Constant (stpi_lower s)"

fun generate_lowerBound :: "string \<Rightarrow> string list \<Rightarrow> string" where
  "generate_lowerBound e _ = e @ ''.lowerBound()''"

register_method lowerBound: lowerBound_of generate_lowerBound

fun upperBound_of :: "Condition \<Rightarrow> Condition list \<Rightarrow> Condition" where
  "upperBound_of (Stamp s) _ = Constant (stpi_upper s)"

fun generate_upperBound :: "string \<Rightarrow> string list \<Rightarrow> string" where
  "generate_upperBound e _ = e @ ''.upperBound()''"

register_method upperBound: upperBound_of generate_upperBound

define_semantics stampConditions

inductive_cases UnaryCool: "stampConditions (Unary op e) c'"
inductive_cases BinaryCool: "stampConditions (Binary op x y) c'"
inductive_cases ConditionalCool: "stampConditions (Conditional c t f) c'"

code_pred (modes: i \<Rightarrow> o \<Rightarrow> bool as execCond) stampConditions .

(*
lemma semdet:
  assumes "myCoolSemantics2 c c'"
  assumes "myCoolSemantics2 c c''"
  shows "c' = c''"
  using assms apply (induction c arbitrary: c' c'')
            apply (metis Condition.inject(5) UnaryCool) 
  apply (metis BinaryCool Condition.inject(5))
          apply (smt (verit, best) Condition.distinct(55) Condition.inject(4) Condition.inject(5) ConditionalCool coerce_to_bool.simps)
  apply (smt (z3) Condition.distinct(59) Condition.distinct(61) Condition.distinct(65) Condition.simps(17) Condition.simps(35) Condition.simps(4) Condition.simps(51) Condition.simps(66) Condition.simps(75) Condition.simps(79) myCoolSemantics2.cases)
  sorry

experiment begin
definition e where "e = (Expr (ConstantExpr (IntVal 32 400)))"

value "stamp_semantics e []"
value "stamp_translation ''e'' []"

values "{c'. myCoolSemantics2 (cond[e..stamp()..upMask()]) c'}"
values "{c'. myCoolSemantics2 (cond[((e..stamp()..upMask()) & (e..stamp()..upMask()))]) c'}"
values "{c'. myCoolSemantics2 (cond[((e..stamp()..upMask()) & (e..stamp()..upMask())) eq (const 0)]) c'}"
value "Predicate.the (execCond (cond[((e..stamp()..upMask()) & (e..stamp()..upMask())) eq (const 0)]))"

values "{c'. myCoolSemantics2 (cond[e..stamp() instanceof IntegerStamp]) c'}"
value "Predicate.the (execCond (cond[e..stamp() instanceof IntegerStamp]))"

definition x where "x = (Expr (LeafExpr 10 default_stamp))"

values "{c'. myCoolSemantics2 (cond[x instanceof ConstantNode; !(e instanceof ConstantNode)]) c'}"
value "Predicate.the (execCond (cond[x instanceof ConstantNode; !(e instanceof ConstantNode)]))"
value "Predicate.the (execCond (cond[e instanceof ConstantNode; !(x instanceof ConstantNode)]))"
value "Predicate.the (execCond (cond[e instanceof ConstantNode]))"


lemma
  (*assumes "s = Stamp (IntegerStamp 32 400 400)"*)
  assumes "e = (Expr (ConstantExpr (IntVal 32 400)))"
  assumes "s = expr_of e []"
  shows "myCoolSemantics2 (e..stamp()) v = myCoolSemantics2 s v"
  using assms using myCoolSemantics2.intros(13) unfolding stamp_semantics sorry

register_method stamp2: stamp_of "\<lambda>e _. e @ ''.stamp(view)''"

value "stamp2_translation ''e'' []"

abbreviation "stampe \<equiv> stamp_translation"

inductive hello where "hello x"

print_commands
end
*)

context includes java_ast_syntax begin
(*
  Unary IRUnaryOp Condition |
  Binary IRBinaryOp Condition Condition |
  Conditional Condition Condition Condition |
  Constant int |
  Value Value |
  Variable String.literal |
  Expr IRExpr |
  Stamp Stamp |

  Combine Condition Condition ("_; _") |

  InstanceOf Condition String.literal |
  Method Condition String.literal "Condition list"*)

fun export :: "Condition \<Rightarrow> Expression" where
  "export (Unary op e) = (JavaUnary op (export e))" |
  "export (Binary op x y) = (JavaBinary op (export x) (export y))" |
  (* Conditional - needed? *)
  "export (Constant v) = (JavaConstant v)" |
  "export (Value (IntVal _ v)) = (JavaConstant (Word.the_int v))" |
  "export (Variable v) = (JavaVariable v)" |
  "export (InstanceOf c cn) = (JavaInstanceOf (export c) cn STR ''_'')" |
  "export (Method obj mn ps) = (JavaMethodCall (export obj) mn (map export ps))" |
  "export (Combine lhs rhs) = (JavaBinary BinAnd (export lhs) (export rhs))"

(*
value "generate_expression (export cond[(Variable STR ''x'') instanceof ConstantNode; !(Variable STR ''y'' instanceof ConstantNode)])"
value "export cond[x..stamp() instanceof IntegerStamp]"
value "export cond[((z..stamp()..upMask()) & (y..stamp()..upMask())) eq (const 0)]"
value "export cond[y..isPowerOf2()]"
*)

end

definition evalCondition :: "Condition \<Rightarrow> bool" where
  "evalCondition c = (\<exists>c'. stampConditions c c' \<and> coerce_to_bool c' True)"

end