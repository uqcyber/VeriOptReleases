section \<open>Optization DSL\<close> (* first theory in list, not related to file contents *)

subsection \<open>Markup\<close>

theory Markup
  imports Semantics.TermRewrites Snippets.Snipping
begin

datatype ('a, 'b) Rewrite =
  Transform 'a 'b ("_ \<longmapsto> _" 10) |
  Conditional 'a 'b "SideCondition" ("_ \<longmapsto> _ when _" 11) |
  Sequential "('a, 'b) Rewrite" "('a, 'b) Rewrite" |
  Transitive "('a, 'b) Rewrite"

datatype 'a ExtraNotation =
  ConditionalNotation 'a 'a 'a ("_ ? _ : _" 50) |
  EqualsNotation 'a 'a ("_ eq _") |
  ConstantNotation 'a ("const _" 120) |
  TrueNotation ("true") |
  FalseNotation ("false") |
  ExclusiveOr 'a 'a ("_ \<oplus> _") |
  LogicNegationNotation 'a ("!_") |
  ShortCircuitOr 'a 'a ("_ || _")

definition word :: "('a::len) word \<Rightarrow> 'a word" where
  "word x = x"

ML_file \<open>markup.ML\<close>

subsubsection \<open>Expression Markup\<close>
ML \<open>
structure IRExprTranslator : DSL_TRANSLATION =
struct
fun markup DSL_Tokens.Add = @{term BinaryExpr} $ @{term BinAdd}
  | markup DSL_Tokens.Sub = @{term BinaryExpr} $ @{term BinSub}
  | markup DSL_Tokens.Mul = @{term BinaryExpr} $ @{term BinMul}
  | markup DSL_Tokens.And = @{term BinaryExpr} $ @{term BinAnd}
  | markup DSL_Tokens.Or = @{term BinaryExpr} $ @{term BinOr}
  | markup DSL_Tokens.Xor = @{term BinaryExpr} $ @{term BinXor}
  | markup DSL_Tokens.ShortCircuitOr = @{term BinaryExpr} $ @{term BinShortCircuitOr}
  | markup DSL_Tokens.Abs = @{term UnaryExpr} $ @{term UnaryAbs}
  | markup DSL_Tokens.Less = @{term BinaryExpr} $ @{term BinIntegerLessThan}
  | markup DSL_Tokens.Equals = @{term BinaryExpr} $ @{term BinIntegerEquals}
  | markup DSL_Tokens.Not = @{term UnaryExpr} $ @{term UnaryNot}
  | markup DSL_Tokens.Negate = @{term UnaryExpr} $ @{term UnaryNeg}
  | markup DSL_Tokens.LogicNegate = @{term UnaryExpr} $ @{term UnaryLogicNegation}
  | markup DSL_Tokens.LeftShift = @{term BinaryExpr} $ @{term BinLeftShift}
  | markup DSL_Tokens.RightShift = @{term BinaryExpr} $ @{term BinRightShift}
  | markup DSL_Tokens.UnsignedRightShift = @{term BinaryExpr} $ @{term BinURightShift}
  | markup DSL_Tokens.Conditional = @{term ConditionalExpr}
  | markup DSL_Tokens.Constant = @{term ConstantExpr}
  | markup DSL_Tokens.TrueConstant = @{term "ConstantExpr (IntVal 32 1)"}
  | markup DSL_Tokens.FalseConstant = @{term "ConstantExpr (IntVal 32 0)"}
end
structure IRExprMarkup = DSL_Markup(IRExprTranslator);
\<close>

snipbegin \<open>ir expression translation\<close>
syntax "_expandExpr" :: "term \<Rightarrow> term" ("exp[_]")
parse_translation \<open> [( @{syntax_const "_expandExpr"} , IRExprMarkup.markup_expr [])] \<close>
snipend -

snipbegin \<open>ir expression example\<close>
value "exp[(e\<^sub>1 < e\<^sub>2) ? e\<^sub>1 : e\<^sub>2]"
text \<open>@{term \<open>exp[(e\<^sub>1 < e\<^sub>2) ? e\<^sub>1 : e\<^sub>2]\<close>}\<close>
snipend -

subsubsection \<open>Value Markup\<close>
ML \<open>
structure IntValTranslator : DSL_TRANSLATION =
struct
fun markup DSL_Tokens.Add = @{term intval_add}
  | markup DSL_Tokens.Sub = @{term intval_sub}
  | markup DSL_Tokens.Mul = @{term intval_mul}
  | markup DSL_Tokens.And = @{term intval_and}
  | markup DSL_Tokens.Or = @{term intval_or}
  | markup DSL_Tokens.ShortCircuitOr = @{term intval_short_circuit_or}
  | markup DSL_Tokens.Xor = @{term intval_xor}
  | markup DSL_Tokens.Abs = @{term intval_abs}
  | markup DSL_Tokens.Less = @{term intval_less_than}
  | markup DSL_Tokens.Equals = @{term intval_equals}
  | markup DSL_Tokens.Not = @{term intval_not}
  | markup DSL_Tokens.Negate = @{term intval_negate}
  | markup DSL_Tokens.LogicNegate = @{term intval_logic_negation}
  | markup DSL_Tokens.LeftShift = @{term intval_left_shift}
  | markup DSL_Tokens.RightShift = @{term intval_right_shift}
  | markup DSL_Tokens.UnsignedRightShift = @{term intval_uright_shift}
  | markup DSL_Tokens.Conditional = @{term intval_conditional}
  | markup DSL_Tokens.Constant = @{term "IntVal 32"}
  | markup DSL_Tokens.TrueConstant = @{term "IntVal 32 1"}
  | markup DSL_Tokens.FalseConstant = @{term "IntVal 32 0"}
end
structure IntValMarkup = DSL_Markup(IntValTranslator);
\<close>

snipbegin \<open>value expression translation\<close>
syntax "_expandIntVal" :: "term \<Rightarrow> term" ("val[_]")
parse_translation \<open> [( @{syntax_const "_expandIntVal"} , IntValMarkup.markup_expr [])] \<close>
snipend -

snipbegin \<open>value expression example\<close>
value "val[(e\<^sub>1 < e\<^sub>2) ? e\<^sub>1 : e\<^sub>2]"
text \<open>@{term \<open>val[(e\<^sub>1 < e\<^sub>2) ? e\<^sub>1 : e\<^sub>2]\<close>}\<close>
snipend -

subsubsection \<open>Word Markup\<close>
ML \<open>
structure WordTranslator : DSL_TRANSLATION =
struct
fun markup DSL_Tokens.Add = @{term plus}
  | markup DSL_Tokens.Sub = @{term minus}
  | markup DSL_Tokens.Mul = @{term times}
  | markup DSL_Tokens.And = @{term Bit_Operations.semiring_bit_operations_class.and}
  | markup DSL_Tokens.Or = @{term or}
  | markup DSL_Tokens.Xor = @{term xor}
  | markup DSL_Tokens.Abs = @{term abs}
  | markup DSL_Tokens.Less = @{term less}
  | markup DSL_Tokens.Equals = @{term HOL.eq}
  | markup DSL_Tokens.Not = @{term not}
  | markup DSL_Tokens.Negate = @{term uminus}
  | markup DSL_Tokens.LogicNegate = @{term logic_negate}
  | markup DSL_Tokens.LeftShift = @{term shiftl}
  | markup DSL_Tokens.RightShift = @{term signed_shiftr}
  | markup DSL_Tokens.UnsignedRightShift = @{term shiftr}
  | markup DSL_Tokens.Constant = @{term word}
  | markup DSL_Tokens.TrueConstant = @{term 1}
  | markup DSL_Tokens.FalseConstant = @{term 0}
end
structure WordMarkup = DSL_Markup(WordTranslator);
\<close>

snipbegin \<open>word expression translation\<close>
syntax "_expandWord" :: "term \<Rightarrow> term" ("bin[_]")
parse_translation \<open> [( @{syntax_const "_expandWord"} , WordMarkup.markup_expr [])] \<close>
snipend -

snipbegin \<open>word expression example\<close>
value "bin[x & y | z]"
text \<open>@{term \<open>val[(e\<^sub>1 < e\<^sub>2) ? e\<^sub>1 : e\<^sub>2]\<close>}\<close>
snipend -

value "bin[-x]"
value "val[-x]"
value "exp[-x]"

value "bin[!x]"
value "val[!x]"
value "exp[!x]"

value "bin[\<not>x]"
value "val[\<not>x]"
value "exp[\<not>x]"

value "bin[~x]"
value "val[~x]"
value "exp[~x]"

value "~x"

end