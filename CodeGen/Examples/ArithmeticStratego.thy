theory ArithmeticStratego
  imports Arithmetic "../Stratego"
begin

setup \<open>Locale_Code.open_block\<close>
interpretation Arithmetic: Rewritable
  size_Arithmetic
  
  eval_condition ground_condition is_ground_condition
  eval_transformer ground_transformer is_ground_transformer

  subexprs_Arithmetic chain_Arithmetic rewrite_Arithmetic
  match_Arithmetic

  varof_Arithmetic var_Arithmetic
proof
  fix c :: ArithmeticCondition
  fix a' a :: "(string \<rightharpoonup> Arithmetic)"
  assume sub: "a' \<subseteq>\<^sub>m a"
  assume ground: "is_ground_condition (ground_condition c a')"
  show "ground_condition c a' = ground_condition c a"
    using sub ground 
    apply (induction c a rule: ground_condition.induct)
    defer defer apply simp+
    subgoal premises prem for e f
    proof (cases "a' e")
      case None
      then have "\<not>(is_ground_condition (case a' e of None \<Rightarrow> IsSub (Variable e) | Some x \<Rightarrow> IsSub x))"
        by simp
      then show ?thesis using prem by blast
    next
      case (Some a)
      then have "a' e = f e" using prem(1)
        by (metis domIff map_le_def option.distinct(1))
      then show ?thesis by simp
    qed
    apply simp
    subgoal premises prem for e f
    proof (cases "a' e")
      case None
      then have "\<not>(is_ground_condition (case a' e of None \<Rightarrow> IsNumber (Variable e) | Some x \<Rightarrow> IsNumber x))"
        by simp
      then show ?thesis using prem by blast
    next
      case (Some a)
      then have "a' e = f e" using prem(1)
        by (metis domIff map_le_def option.distinct(1))
      then show ?thesis by simp
    qed
    done
next
  fix e :: Arithmetic
  show "\<forall>e' \<in> set (subexprs_Arithmetic e). size_Arithmetic e > size_Arithmetic e'"
    by (cases e; simp)
next
  fix f :: "Arithmetic \<Rightarrow> Arithmetic"
  fix e :: Arithmetic
  show "map f (subexprs_Arithmetic e) = subexprs_Arithmetic (snd (chain_Arithmetic (\<lambda>e a. (plus a 1, f e)) e 0))"
    by (cases e; simp)
next
  fix f :: "Arithmetic \<Rightarrow> Arithmetic"
  fix e :: Arithmetic
  show "length (subexprs_Arithmetic e) = fst (chain_Arithmetic (\<lambda>e a. (plus a 1, f e)) e 0)"
    by (cases e; simp)
next
  fix c :: "ArithmeticCondition"
  have lhs: "eval_condition c = None \<Longrightarrow> (\<not> is_ground_condition c)"
  subgoal premises e
  proof (cases c)
    case (IsSub x1)
    then show ?thesis using e by (cases x1; auto) 
  next
    case (IsNumber x2)
    then show ?thesis using e by (cases x2; auto)
  qed
  done
  have rhs: "(\<not> is_ground_condition c) \<Longrightarrow> eval_condition c = None"
  subgoal premises e
  proof (cases c)
    case (IsSub x1)
    then show ?thesis using e by (cases x1; auto) 
  next
    case (IsNumber x2)
    then show ?thesis using e by (cases x2; auto)
  qed
  done
  from lhs rhs show "eval_condition c = None \<equiv> (\<not> is_ground_condition c)"
    by linarith
qed
setup \<open>Locale_Code.close_block\<close>

subsubsection "Stratego Rules"

definition "eval = Arithmetic.eval"
definition "var = var_Arithmetic"

notation Arithmetic.conditional_rewrite_to ("_ \<rightarrow> _ where _")

type_synonym StrategyRule = "(Arithmetic, ArithmeticCondition, Transformer) Strategy"

export_code "eval" checking SML

definition RedundantAdd :: "StrategyRule" where
  "RedundantAdd = ((Add (var ''b'') (Number 0)) \<rightarrow> (var ''b''))"

value "eval (RedundantAdd) ((Add (Number 10) (Number 10)), fmempty)"

definition RedundantSub :: "StrategyRule" where
  "RedundantSub = ((Sub (var ''a'') (Number 0)) \<rightarrow> (var ''a'') where condition (IsSub (var ''a'')))"

value "eval (RedundantSub) ((Sub (Number 10) (Number 0)), fmempty)"
value "eval (RedundantSub) ((Sub (Sub (Number 100) (Number 1000)) (Number 0)), fmempty)"


definition ShiftConstRight :: "StrategyRule" where
  "ShiftConstRight = 
    ((Add (var ''a'') (var ''b'')) \<rightarrow> (Add (var ''b'') (var ''a''))
      where ((var ''a'')!; not (Number 0?)))"

definition ShiftConstRight2 :: "StrategyRule" where
  "ShiftConstRight2 = 
    ((Add (var ''a'') (var ''b'')) \<rightarrow> (Add (var ''b'') (var ''a''))
      where (condition (IsNumber (var ''a''))))"

definition EvalMinus :: "StrategyRule" where
  "EvalMinus = 
    ((UMinus (Variable ''a'')) \<rightarrow> ((Variable ''b''))
      where (condition (IsNumber (Variable ''a'')); func (UnaryMinus (Variable ''a'')); (Variable ''b'')?))"

definition EvalMinus1 :: "StrategyRule" where
  "EvalMinus1 =
    (UMinus (Variable ''a'')) \<rightarrow> Variable ''b''
      where (condition (IsNumber (Variable ''a'')); (Variable ''b'') := (func (UnaryMinus (Variable ''a''))))"

definition EvalAdd :: "StrategyRule" where
  "EvalAdd =
    ((Add (Variable ''a'') (Variable ''b'')) \<rightarrow> ((Variable ''c''))
      where (
        (condition (IsNumber (Variable ''a'')));
        (condition (IsNumber (Variable ''a'')));
        ((Variable ''c'') := (func (Plus (Variable ''a'') (Variable ''b''))))
      ))"

subsubsection "Rewrite Application"

text "
The combination of @{term RedundantAdd} and @{term RedundantSub}
provides us a rule that will eliminate zero in either add or sub expressions.
It is defined as @{term \<open>RedundantAdd <+ RedundantSub\<close>}.
The expanded version of this rule is:

@{value \<open>RedundantAdd <+ RedundantSub\<close>}"

\<comment> \<open>Failing to apply the rule\<close>
value "eval (RedundantAdd <+ RedundantSub) ((Add (Number 10) (Number 10)), fmempty)"
text \<open>@{value "eval (RedundantAdd <+ RedundantSub) ((Add (Number 10) (Number 10)), fmempty)"}\<close>

\<comment> \<open>Successful application\<close>
value "eval (RedundantAdd <+ RedundantSub) ((Add (Number 10) (Number 0)), fmempty)"
text \<open>@{value "eval (RedundantAdd <+ RedundantSub) ((Add (Number 10) (Number 0)), fmempty)"}\<close>

\<comment> \<open>Successful application in the second rule\<close>
value "eval (RedundantSub <+ RedundantAdd) ((Add (Number 10) (Number 0)), fmempty)"
text \<open>@{value "eval (RedundantSub <+ RedundantAdd) ((Add (Number 10) (Number 0)), fmempty)"}\<close>

value "ShiftConstRight"
value "eval ShiftConstRight ((Add (Number 0) (Number 10)), fmempty)"
value "eval ShiftConstRight ((Add (Number 10) (Add (Number 10) (Number 20))), fmempty)"
value "eval ShiftConstRight ((Add (Number 10) (Number 120)), fmempty)"

value "eval ShiftConstRight2 ((Add (Number 0) (Number 10)), fmempty)"
value "eval ShiftConstRight2 ((Add (Number 10) (Add (Number 10) (Number 20))), fmempty)"
value "eval ShiftConstRight2 ((Add (Number 10) (Number 120)), fmempty)"

value "eval EvalMinus ((UMinus (Number 10)), fmempty)"
value "eval EvalMinus ((UMinus (Add (Number 10) (Number 10))), fmempty)"
text \<open>@{value "eval EvalMinus ((UMinus (Number 10)), fmempty)"}\<close>

value "eval EvalAdd ((UMinus (Number 10)), fmempty)"
value "eval EvalAdd ((Add (Number 10) (Number 10)), fmempty)"
text \<open>@{value "eval EvalAdd ((Add (Number 10) (Number 10)), fmempty)"}\<close>


end