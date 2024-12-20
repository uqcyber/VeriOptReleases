(*  Title:      Optimizations/DSL/markup.ML
    Author:     Brae Webb

Lift shorthand expressions to the full type.
*)

structure DSL_Tokens =
struct

datatype Tokens =
    Add
  | Sub
  | Mul
  | Div
  | Rem
  | And
  | Or
  | Xor
  | ShortCircuitOr
  | Less
  | Abs
  | Equals
  | Not
  | Negate
  | LogicNegate
  | LeftShift
  | RightShift
  | UnsignedRightShift
  | Conditional
  | Constant
  | ConstantEval
  | TrueConstant
  | FalseConstant
end

signature DSL_TRANSLATION =
sig
val markup: DSL_Tokens.Tokens -> term
end

signature DSL_MARKUP =
sig
  val const_expr: Proof.context -> term list -> term
  val equals_expr: Proof.context -> term list -> term

  val markup_expr: term list -> Proof.context -> term list -> term

  val rewrite: term list -> Proof.context -> term list -> term
  val conditional_rewrite: term list -> Proof.context -> term list -> term
end;

functor DSL_Markup(Translator: DSL_TRANSLATION): DSL_MARKUP =
struct

fun const_expr _ [c as Const _] =
    @{const ConstantExpr} $ (@{const IntVal} $ c)
  | const_expr _ [x $ y] =
    @{const ConstantExpr} $ (@{const IntVal} $ (x $ y))
  | const_expr _ ts = raise TERM ("const_expr", ts)

fun equals_expr _ [lhs, rhs] =
    Translator.markup DSL_Tokens.Equals $ lhs $ rhs
  | equals_expr _ ts = raise TERM ("equals_expr", ts)


(* Shorthand expressions *)
fun markup_constant (str, typ) =
  case (str, typ) of
    ("\<^const>Markup.ExtraNotation.ConditionalNotation", _) => Translator.markup DSL_Tokens.Conditional
    | ("Markup.ExtraNotation.ConditionalNotation", _) => Translator.markup DSL_Tokens.Conditional
    | ("\<^const>Markup.ExtraNotation.EqualsNotation", _) => Translator.markup DSL_Tokens.Equals
    | ("Markup.ExtraNotation.EqualsNotation", _) => Translator.markup DSL_Tokens.Equals
    | ("\<^const>Markup.ExtraNotation.ConstantNotation", _) => Translator.markup DSL_Tokens.Constant
    | ("Markup.ExtraNotation.ConstantNotation", _) => Translator.markup DSL_Tokens.Constant
    | ("\<^const>CodeGenAltAlt.PatternExpr.ConstantLiteralPattern", _) => Translator.markup DSL_Tokens.ConstantEval
    | ("CodeGenAltAlt.PatternExpr.ConstantLiteralPattern", _) => Translator.markup DSL_Tokens.ConstantEval
    | ("\<^const>Markup.ExtraNotation.TrueNotation", _) => Translator.markup DSL_Tokens.TrueConstant
    | ("Markup.ExtraNotation.TrueNotation", _) => Translator.markup DSL_Tokens.TrueConstant
    | ("\<^const>Markup.ExtraNotation.FalseNotation", _) => Translator.markup DSL_Tokens.FalseConstant
    | ("Markup.ExtraNotation.FalseNotation", _) => Translator.markup DSL_Tokens.FalseConstant
    | ("\<^const>Markup.ExtraNotation.LogicNegationNotation", _) => Translator.markup DSL_Tokens.LogicNegate
    | ("Markup.ExtraNotation.LogicNegationNotation", _) => Translator.markup DSL_Tokens.LogicNegate
    | ("\<^const>Groups.plus_class.plus", _) => Translator.markup DSL_Tokens.Add
    | ("Groups.plus_class.plus", _) => Translator.markup DSL_Tokens.Add
    | ("\<^const>Groups.minus_class.minus", _) => Translator.markup DSL_Tokens.Sub
    | ("Groups.minus_class.minus", _) => Translator.markup DSL_Tokens.Sub
    | ("\<^const>Groups.times_class.times", _) => Translator.markup DSL_Tokens.Mul
    | ("Groups.times_class.times", _) => Translator.markup DSL_Tokens.Mul
    | ("\<^const>Rings.divide_class.divide", _) => Translator.markup DSL_Tokens.Div
    | ("Rings.divide_class.divide", _) => Translator.markup DSL_Tokens.Div
    | ("\<^const>Fields.inverse_class.inverse_divide", _) => Translator.markup DSL_Tokens.Div
    | ("Fields.inverse_class.inverse_divide", _) => Translator.markup DSL_Tokens.Div
    | ("\<^const>Markup.ExtraNotation.Remainder", _) => Translator.markup DSL_Tokens.Div
    | ("Markup.ExtraNotation.Remainder", _) => Translator.markup DSL_Tokens.Div
    | ("\<^const>HOL.conj", _) => Translator.markup DSL_Tokens.And
    | ("HOL.conj", _) => Translator.markup DSL_Tokens.And
    | ("\<^const>HOL.disj", _) => Translator.markup DSL_Tokens.Or
    | ("HOL.disj", _) => Translator.markup DSL_Tokens.Or
    | ("\<^const>Markup.ExtraNotation.ShortCircuitOr", _) => Translator.markup DSL_Tokens.ShortCircuitOr
    | ("Markup.ExtraNotation.ShortCircuitOr", _) => Translator.markup DSL_Tokens.ShortCircuitOr
    | ("\<^const>Power.power_class.power", _) => Translator.markup DSL_Tokens.Xor
    | ("Power.power_class.power", _) => Translator.markup DSL_Tokens.Xor
    | ("\<^const>Groups.uminus_class.uminus", _) => Translator.markup DSL_Tokens.Negate
    | ("Groups.uminus_class.uminus", _) => Translator.markup DSL_Tokens.Negate
    | ("\<^const>HOL.Not", _) => Translator.markup DSL_Tokens.Not
    | ("HOL.Not", _) => Translator.markup DSL_Tokens.Not
    | ("\<^const>Orderings.ord_class.less", _) => Translator.markup DSL_Tokens.Less
    | ("Orderings.ord_class.less", _) => Translator.markup DSL_Tokens.Less
    | ("\<^const>Groups.abs_class.abs", _) => Translator.markup DSL_Tokens.Abs
    | ("Groups.abs_class.abs", _) => Translator.markup DSL_Tokens.Abs
    | ("\<^const>AbsPhase.abs", _) => Translator.markup DSL_Tokens.Abs
    | ("AbsPhase.abs", _) => Translator.markup DSL_Tokens.Abs
    | ("\<^const>JavaWords.shiftl", _) => Translator.markup DSL_Tokens.LeftShift
    | ("JavaWords.shiftl", _) => Translator.markup DSL_Tokens.LeftShift
    | ("\<^const>Markup.ExtraNotation.SignedRightShiftNotation", _) => Translator.markup DSL_Tokens.RightShift
    | ("Markup.ExtraNotation.SignedRightShiftNotation", _) => Translator.markup DSL_Tokens.RightShift
    | ("\<^const>JavaWords.shiftr", _) => Translator.markup DSL_Tokens.UnsignedRightShift
    | ("JavaWords.shiftr", _) => Translator.markup DSL_Tokens.UnsignedRightShift
    | _ => Const (str, typ)

fun find_free (taken, goal) =
  (singleton
    (Name.variant_list 
      (fold Term.add_tfree_names taken [])) goal)

fun markup_free taken (str, typ) =
  case (str, typ) of
    ("abs", _) => Translator.markup DSL_Tokens.Abs
    | (var, typ) => Free (find_free (taken, var), typ)

fun markup_expr taken ctxt [trm] =
  let
    val res = (case trm of
      Const (str, typ) => markup_constant (str, typ)
    | e as ((Const ("\<^const>IRTreeEval.IRExpr.ConstantExpr",_)) $ _) => e (* ignore within a constant *)
    | e as ((Const ("IRTreeEval.IRExpr.ConstantExpr",_)) $ _) => e (* ignore within a constant *)
    | e as ((Const ("\<^const>CodeGenAltAlt.PatternExpr.ConstantPattern",_)) $ _) => e (* ignore within a constant *)
    | e as ((Const ("CodeGenAltAlt.PatternExpr.ConstantPattern",_)) $ _) => e (* ignore within a constant *)
    | (e as (Const ("\<^const>Markup.Rewrite.Conditional",_))) $ lhs $ rhs $ cond => 
      e $ markup_expr taken ctxt [lhs] $ markup_expr taken ctxt [rhs] $ cond
    | (e as (Const ("Markup.Rewrite.Conditional",_))) $ lhs $ rhs $ cond => 
      e $ markup_expr taken ctxt [lhs] $ markup_expr taken ctxt [rhs] $ cond
    | (e as (Const ("Markup.Rewrite.Transform",_))) $ lhs $ rhs => 
      e $ markup_expr taken ctxt [lhs] $ markup_expr taken ctxt [rhs]
    | (x $ y) => ((let val x' = markup_expr taken ctxt [x] in 
        case x' of 
          ((Const ("IRTreeEval.IRExpr.ConstantExpr",_))) => (x' $ y)
          (*| ((Const ("CodeGenAltAlt.PatternExpr.ConstantPattern",_))) => (x' $ y)*)
          | _ => (x' $ markup_expr taken ctxt [y])
        end))
    | Free (str, typ) => markup_free taken (str, typ)
    | Abs (str, typ, trm) => Abs (str, typ, markup_expr taken ctxt [trm])
    | _ => trm);
  in
    res
  end
  | markup_expr _ _ ts = raise TERM ("markup_expr", ts)


(* Rewrite syntax *)
fun rewrite taken ctxt [pre, post] =
  Const ("Transform", @{typ "'a => 'b \<Rightarrow> ('a, 'b) Rewrite"})
    $ markup_expr taken ctxt [pre]   
    $ markup_expr taken ctxt [post]

  | rewrite _ _ ts = raise TERM ("rewrite", ts)

fun conditional_rewrite taken ctxt [pre, post, cond] =
  Const ("Conditional", @{typ "'a \<Rightarrow> 'b \<Rightarrow> bool \<Rightarrow> ('a, 'b) Rewrite"})
    $ markup_expr taken ctxt [pre]
    $ markup_expr taken ctxt [post]
    $ cond

  | conditional_rewrite _ _ ts = raise TERM ("conditional_rewrite", ts)

end