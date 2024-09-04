theory IRExprCodeGen
imports OptimizationDSL.CodeGenAlt Snippets.Snipping
begin

notation (output)
  pattern_refinement ("(_ \<sqsupseteq>\<^bsub>p\<^esub> \<index>)")

snipbegin \<open>expression match\<close>
text \<open>
@{thm[display,margin=75] match_tree.simps(1) [no_vars]}
@{thm[display,margin=70] match_tree.simps(2) [no_vars]}
@{thm[display,margin=70] match_tree.simps(3) [no_vars]}
@{thm[display,margin=70] match_tree.simps(4) [no_vars]}
@{thm[display,margin=70] match_tree.simps(5) [no_vars]}
@{thm[display,margin=70] match_tree.simps(6) [no_vars]}
@{thm[display,margin=70] match_tree.simps(7) [no_vars]}
@{thm[display,margin=70] match_tree.simps(8) [no_vars]}
\<close>
snipend -

snipbegin \<open>rewrite\<close>
text \<open>
@{thm[display,margin=40] rewrite_def [no_vars]}
\<close>
snipend -

snipbegin \<open>isground\<close>
text \<open>
@{thm[display,margin=40] is_ground_IRExpr [no_vars]}
\<close>
snipend -

snipbegin \<open>ground substitution\<close>
text \<open>
@{thm[display,margin=65] ground_substitution_def [no_vars]}
\<close>
snipend -

snipbegin \<open>ground substitution is grounded\<close>
text \<open>
@{thm[display,margin=65] ground_substitution [no_vars]}
\<close>
snipend -

snipbegin \<open>valid pattern preserves freshness\<close>
text \<open>@{thm[display] valid_pattern_preserves_freshness [no_vars]}\<close>
snipend -

snipbegin \<open>lower pattern\<close>
text \<open>
\induct{@{thm[mode=Rule] lower.intros(1) [no_vars]}}{lower:var1}
\induct{@{thm[mode=Rule] lower.intros(2) [no_vars]}}{lower:var2}
\induct{@{thm[mode=Rule] lower.intros(3) [no_vars]}}{lower:const}
\induct{@{thm[mode=Rule] lower.intros(4) [no_vars]}}{lower:unary}
\induct{@{thm[mode=Rule] lower.intros(5) [no_vars]}}{lower:binary}
\induct{@{thm[mode=Rule] lower.intros(6) [no_vars]}}{lower:conditional}
\induct{@{thm[mode=Rule] lower.intros(9) [no_vars]}}{lower:param}
\induct{@{thm[mode=Rule] lower.intros(10) [no_vars]}}{lower:leaf}
\<close>
snipend -

snipbegin \<open>lower pattern sound\<close>
text \<open>@{thm[mode=Rule] lower_sound [no_vars]}\<close>
snipend -

snipbegin \<open>lower rule\<close>
text \<open>@{thm[mode=Rule] generate.intros(1) [no_vars]}\<close>
snipend -

snipbegin \<open>lower rule sound\<close>
text \<open>@{thm[mode=Rule] generate_sound [no_vars]}\<close>
snipend -

snipbegin \<open>unify\<close>
text \<open>
\induct{@{thm[mode=Rule] unify.intros(1) [no_vars]}}{unify:empty}
\induct{@{thm[mode=Rule] unify.intros(2) [no_vars]}}{unify:exists}
\induct{@{thm[mode=Rule] unify.intros(3) [no_vars]}}{unify:new}
\<close>
snipend -

snipbegin \<open>match semantics\<close>
text \<open>
\induct{@{thm[mode=Rule] eval_match.intros(1) [no_vars]}}{eval-match:unary}
\induct{@{thm[mode=Rule] eval_match.intros(2) [no_vars]}}{eval-match:binary}
\induct{@{thm[mode=Rule] eval_match.intros(3) [no_vars]}}{eval-match:conditional}
\induct{@{thm[mode=Rule] eval_match.intros(4) [no_vars]}}{eval-match:constant}
\induct{@{thm[mode=Rule] eval_match.intros(5) [no_vars]}}{eval-match:param}
\induct{@{thm[mode=Rule] eval_match.intros(6) [no_vars]}}{eval-match:leaf}
\induct{@{thm[mode=Rule] eval_match.intros(7) [no_vars]}}{eval-match:equality}
\induct{@{thm[mode=Rule] eval_match.intros(8) [no_vars]}}{eval-match:andthen}
\induct{@{thm[mode=Rule] eval_match.intros(9) [no_vars]}}{eval-match:noop}
\<close>
snipend -

snipbegin \<open>groundof\<close>
text \<open>
\induct{@{thm[mode=Rule] groundof.intros(1) [no_vars]}}{groundof:unary}
\induct{@{thm[mode=Rule] groundof.intros(2) [no_vars]}}{groundof:binary}
\induct{@{thm[mode=Rule] groundof.intros(3) [no_vars]}}{groundof:conditional}
\induct{@{thm[mode=Rule] groundof.intros(4) [no_vars]}}{groundof:param}
\induct{@{thm[mode=Rule] groundof.intros(5) [no_vars]}}{groundof:leaf}
\induct{@{thm[mode=Rule] groundof.intros(6) [no_vars]}}{groundof:constant}
\induct{@{thm[mode=Rule] groundof.intros(8) [no_vars]}}{groundof:var}
\<close>
snipend -

(*
snipbegin \<open>ground substitution\<close>
text \<open>
@{thm[display,margin=40] ground_substitution_def [no_vars]}
\<close>
snipend -
*)

snipbegin \<open>pattern refinement\<close>
text \<open>
@{thm[display,margin=60] pattern_refinement_def [no_vars]}
\<close>
snipend -

snipbegin \<open>ground refinement\<close>
text \<open>
@{thm[mode=Rule] ground_refinement [no_vars]}
\<close>
snipend -

snipbegin \<open>match ground substitution\<close>
text \<open>
@{thm[mode=Rule] match_tree_ground [no_vars]}
\<close>
snipend -

snipbegin \<open>grounded is groundof\<close>
text \<open>
@{thm[mode=Rule] ground_groundof [no_vars]}
\<close>
snipend -

snipbegin \<open>match is groundof\<close>
text \<open>
@{thm[mode=Rule] match_tree_groundof [no_vars]}
\<close>
snipend -

snipbegin \<open>pattern refinement refines expressions\<close>
text \<open>
@{thm[mode=Rule] sound_exec [no_vars]}
\<close>
snipend -

snipbegin \<open>lowered patterns refine expressions\<close>
text \<open>
@{thm[mode=Rule] sound_rules [no_vars]}
\<close>
snipend -

(*

notation cond (infixr "?" 52)
notation seq (infixl "\<then>" 50)
notation andthen (infixl "&&" 50)

(*
phase IRExprCodeGen 
  terminating size
begin
snipbegin \<open>IdentityRule\<close>
optimization Identity: "a * (const (IntVal 32 1)) \<longmapsto> a"
snipend -
*)

definition IdentityRule :: Rules where
  "IdentityRule = 
    match STR ''e'' (BinaryPattern BinMul STR ''a'' STR ''b'') ?
      match STR ''b'' (ConstantPattern (IntVal 32 1)) ?
        base (ExpressionResult (VariableExpr STR ''a'' default_stamp))"

definition EvaluateRule :: Rules where
  "EvaluateRule = 
    match STR ''e'' (BinaryPattern BinMul STR ''a'' STR ''b'') ?
      match STR ''a'' (ConstantVarPattern STR ''x'') ?
        match STR ''b'' (ConstantVarPattern STR ''y'') ?
          base (ExpressionResult 
          (BinaryExpr BinMul (VariableExpr STR ''x'' default_stamp) (VariableExpr STR ''y'' default_stamp)))"

(* TODO: FIX *)
definition ShiftRule :: Rules where
  "ShiftRule = 
    match STR ''e'' (BinaryPattern BinMul STR ''a'' STR ''b'') ?
      match STR ''b'' (ConstantVarPattern STR ''y'') ?
        condition (PowerOf2 (VariableExpr STR ''y'' default_stamp)) ?
          base (ExpressionResult 
          (BinaryExpr BinLeftShift (VariableExpr STR ''a'' default_stamp) (VariableExpr STR ''y'' default_stamp)))"

definition LeftConstRule :: Rules where
  "LeftConstRule = 
    match STR ''e'' (BinaryPattern BinMul STR ''a'' STR ''b'') ?
      match STR ''a'' (ConstantVarPattern STR ''x'') ?
        condition (Not (IsConstantExpr (VariableExpr STR ''b'' default_stamp))) ?
          base (ExpressionResult 
          (BinaryExpr BinMul (VariableExpr STR ''b'' default_stamp) (VariableExpr STR ''a'' default_stamp)))"


notation (output)
  cond ("(4_ ?//_)")
notation (output)
  else ("(_ //else//_)")

nonterminal Mul and LeftShift and Var and Const and IntSyntax and Hide
syntax
  "_mul_syntax" :: "Mul \<Rightarrow> 'a \<Rightarrow> 'a" ("_ * _")
  "_left_shift_syntax" :: "LeftShift \<Rightarrow> 'a \<Rightarrow> 'a" ("_ << _")
  "_var_syntax" :: "Var \<Rightarrow> 'a" ("_")
  "_const_syntax" :: "Const \<Rightarrow> 'a" ("const _")
  "_int_syntax" :: "IntSyntax \<Rightarrow> 'a \<Rightarrow> 'a" ("_\<^bsub>_\<^esub>")
  "_hide_constructor" :: "Hide \<Rightarrow> 'a" ("_")
translations
  "s" <= "_Literal s"
  "s" <= "_String s"
  "_mul_syntax x y" <= "CONST BinaryPattern (CONST BinMul) x y"
  "_mul_syntax x y" <= "CONST BinaryExpr (CONST BinMul) x y"
  "_left_shift_syntax x y" <= "CONST BinaryExpr (CONST BinLeftShift) x y"
  "_var_syntax x" <= "CONST VariableExpr x s"
  "_const_syntax x" <= "CONST ConstantPattern x"
  "_const_syntax x" <= "CONST ConstantVarPattern x"
  "_int_syntax y x" <= "CONST IntVal x y"
  "_hide_constructor x" <= "CONST ExpressionResult x"

value IdentityRule
snipbegin \<open>IdentityRule\<close>
text "@{value[display, margin=40] IdentityRule}"
snipend -
value EvaluateRule
snipbegin \<open>EvaluateRule\<close>
text "@{value[display, margin=40] EvaluateRule}"
snipend -
value ShiftRule
snipbegin \<open>ShiftRule\<close>
text "@{value[display, margin=40] ShiftRule}"
snipend -
value LeftConstRule
snipbegin \<open>LeftConstRule\<close>
text "@{value[display] LeftConstRule}"
snipend -


snipbegin \<open>IRExpr\<close>
datatype BinOp = BinAdd | BinSub | BinMul | Etc
datatype UnaryOp = UnaryNeg | UnaryNot | Etc
datatype IRExpr =
  BinaryExpr BinOp IRExpr IRExpr
  | UnaryExpr UnaryOp IRExpr
  | ConditionalExpr IRExpr IRExpr IRExpr
  | ConstantExpr "64 word"
  | VariableExpr string
snipend -
hide_type IRExpr
hide_const BinaryExpr UnaryExpr ConditionalExpr ConstantExpr VariableExpr



snipbegin \<open>PatternExpr\<close>
type_synonym VarName = string
datatype PatternExpr =
  BinaryPattern BinOp VarName VarName
  | UnaryPattern UnaryOp VarName
  | ConditionalPattern VarName VarName VarName
  | VariablePattern VarName
  | ConstantPattern Value
  | ConstantVarpattern VarName
snipend -
hide_type PatternExpr
hide_const BinaryPattern UnaryPattern ConditionalPattern VariablePattern ConstantPattern ConstantVarPattern

hide_type BinOp UnaryOp
hide_const BinAdd BinSub BinMul Etc
hide_const UnaryNeg UnaryNot Etc


thm eval_match.simps
(*value eval_match*)
snipbegin \<open>EvalMatch\<close>
text "@{thm[display] eval_match.simps}"
snipend -

snipbegin \<open>MatchPattern\<close>
text "@{thm[display,margin=40] match_pattern.simps}"
snipend -

snipbegin \<open>GroundResult\<close>
text "@{thm[display] ground_result.simps}"
snipend -

snipbegin \<open>Generate\<close>
text "@{thm[display,margin=40] generate.simps}"
snipend -

snipbegin \<open>NaiveCombination\<close>
text "@{term[display] \<open>choice [Identity, Evaluate, Shift, LeftConst]\<close>}"
snipend -

(*snipbegin \<open>StrategicCombination\<close>
text "@{term[display] \<open>LeftConst \<then> ((choice [Evaluate, Identity]) else Shift)\<close>}"
snipend -*)

snipbegin \<open>rules-semantics\<close>
text \<open>
@{term_type[mode=type_def] eval_rules}

\induct{@{thm[mode=Rule] eval_rules.intros(1) [no_vars]}}{evalrules:base}
\induct{@{thm[mode=Rule] eval_rules.intros(2) [no_vars]}}{evalrules:cond-some}
\induct{@{thm[mode=Rule] eval_rules.intros(3) [no_vars]}}{evalrules:cond-none}
\induct{@{thm[mode=Rule] eval_rules.intros(4) [no_vars]}}{evalrules:else-some}
\induct{@{thm[mode=Rule] eval_rules.intros(5) [no_vars]}}{evalrules:else-none}
\induct{@{thm[mode=Rule] eval_rules.intros(6) [no_vars]}}{evalrules:choice-some}
\induct{@{thm[mode=Rule] eval_rules.intros(7) [no_vars]}}{evalrules:choice-none}
\induct{@{thm[mode=Rule] eval_rules.intros(8) [no_vars]}}{evalrules:choice-empty}
\induct{@{thm[mode=Rule] eval_rules.intros(9) [no_vars]}}{evalrules:seq-some}
\induct{@{thm[mode=Rule] eval_rules.intros(10) [no_vars]}}{evalrules:seq-none}
\<close>
snipend -

definition preprocess :: "Rules \<Rightarrow> Rules" where
  "preprocess = lift_match o eliminate_noop"

snipbegin \<open>CombineElseExample\<close>
text \<open>@{term "Evaluate else LeftConst"} =\<close>
text \<open>@{value[display] "preprocess (Evaluate else LeftConst)"}\<close>


text \<open>@{term "lift_common (Evaluate else LeftConst)"} =\<close>
text \<open>@{value[display] "lift_common (preprocess (Evaluate else LeftConst))"}\<close>
snipend -
*)

end