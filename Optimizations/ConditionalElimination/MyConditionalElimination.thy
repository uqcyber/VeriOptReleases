section \<open>Conditional Elimination Phase\<close>

theory MyConditionalElimination
  imports
    Semantics.IRTreeEvalThms
    Proofs.Rewrites
    Proofs.Bisimulation
begin

subsection \<open>Individual Elimination Rules\<close>

text \<open>The set of rules used for determining whether a condition @{term q1} implies
    another condition @{term q2} or its negation.
    These rules are used for conditional elimination.\<close>

inductive impliesx :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" ("_ \<Rrightarrow> _") and 
      impliesnot :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" ("_ \<Rrightarrow>\<not> _") where
  q_imp_q: 
  "q \<Rrightarrow> q" |
  eq_impliesnot_less:
  "(BinaryExpr BinIntegerEquals x y) \<Rrightarrow>\<not> (BinaryExpr BinIntegerLessThan x y)" |
  eq_impliesnot_less_rev:
  "(BinaryExpr BinIntegerEquals x y) \<Rrightarrow>\<not> (BinaryExpr BinIntegerLessThan y x)" |
  less_impliesnot_rev_less:
  "(BinaryExpr BinIntegerLessThan x y) \<Rrightarrow>\<not> (BinaryExpr BinIntegerLessThan y x)" |
  less_impliesnot_eq:
  "(BinaryExpr BinIntegerLessThan x y) \<Rrightarrow>\<not> (BinaryExpr BinIntegerEquals x y)" |
  less_impliesnot_eq_rev:
  "(BinaryExpr BinIntegerLessThan x y) \<Rrightarrow>\<not> (BinaryExpr BinIntegerEquals y x)" |
  negate_true:
  "\<lbrakk>x \<Rrightarrow>\<not> y\<rbrakk> \<Longrightarrow> x \<Rrightarrow> (UnaryExpr UnaryLogicNegation y)" |
  negate_false:
  "\<lbrakk>x \<Rrightarrow> y\<rbrakk> \<Longrightarrow> x \<Rrightarrow>\<not> (UnaryExpr UnaryLogicNegation y)"

inductive implies_fail :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool option \<Rightarrow> bool" where
  implies:
  "impliesx x y \<Longrightarrow> implies_fail x y (Some True)" |
  impliesnot:
  "impliesnot x y \<Longrightarrow> implies_fail x y (Some False)" |
  fail:
  "\<not>(impliesx x y \<or> impliesnot x y) \<Longrightarrow> implies_fail x y None"

inductive impliesy :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool option \<Rightarrow> bool" where
  q_imp_q: 
  "impliesy q q (Some True)" |
  eq_impliesnot_less:
  "impliesy (BinaryExpr BinIntegerEquals x y) (BinaryExpr BinIntegerLessThan x y) (Some False)" |
  eq_impliesnot_less_rev:
  "impliesy (BinaryExpr BinIntegerEquals x y) (BinaryExpr BinIntegerLessThan y x) (Some False)" |
  less_impliesnot_rev_less:
  "impliesy (BinaryExpr BinIntegerLessThan x y) (BinaryExpr BinIntegerLessThan y x) (Some False)" |
  less_impliesnot_eq:
  "impliesy (BinaryExpr BinIntegerLessThan x y) (BinaryExpr BinIntegerEquals x y) (Some False)" |
  less_impliesnot_eq_rev:
  "impliesy (BinaryExpr BinIntegerLessThan x y) (BinaryExpr BinIntegerEquals y x) (Some False)" |
  negate_implies:
  "impliesy x y (Some b) \<Longrightarrow> impliesy x (UnaryExpr UnaryLogicNegation y) (Some (\<not>b))" |
  unknown:
  "impliesy x y None"

(*
fun optNot :: "bool option \<Rightarrow> bool option" 
  where
    "optNot (Some True) = Some False"
  | "optNot (Some False) = Some True"
  | "optNot None = None"

fun operandUnaryNegation :: "IRExpr \<Rightarrow> IRExpr"
  where
    "operandUnaryNegation (UnaryExpr UnaryLogicNegation z) = z"
  | "operandUnaryNegation x = x"

function impliesz :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool option"
  where
    "impliesz (BinaryExpr BinIntegerEquals x y) (BinaryExpr BinIntegerLessThan x y) = (Some False)"
  | "impliesz (BinaryExpr BinIntegerEquals x y) (BinaryExpr BinIntegerLessThan y x) = (Some False)"
  | "impliesz (BinaryExpr BinIntegerLessThan x y) (BinaryExpr BinIntegerLessThan y x) = (Some False)"
  | "impliesz (BinaryExpr BinIntegerLessThan x y) (BinaryExpr BinIntegerEquals x y) = (Some False)"
  | "impliesz (BinaryExpr BinIntegerLessThan x y) (BinaryExpr BinIntegerEquals y x) = (Some False)"
  | "impliesz x y = (if x = y then
                       Some True
                     else if (\<exists>z. y = (UnaryExpr UnaryLogicNegation z)) then 
                       optNot (impliesz x (operandUnaryNegation y))
                     else
                        None)"
  by using old.prod.exhaust apply blast apply blast apply blast apply blast apply blast apply blast
sledgehammer
termination by sledgehammer
  using "termination" by blast 
*)

text \<open>The relation @{term "q1 \<Rrightarrow> q2"} indicates that the implication @{term "q1 \<longrightarrow> q2"}
    is known true (i.e. universally valid), 
    and the relation @{term "q1 \<Rrightarrow>\<not> q2"} indicates that the implication @{term "q1 \<longrightarrow> q2"}
    is known false (i.e. @{term "q1 \<longrightarrow>\<not> q2"} is universally valid.
    If neither @{term "q1 \<Rrightarrow> q2"} nor @{term "q1 \<Rrightarrow>\<not> q2"} then the status is unknown.
    Only the known true and known false cases can be used for conditional elimination.\<close>

fun implies_valid :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" (infix "\<Zinj>" 50) where
  "implies_valid q1 q2 = 
    (\<forall>m p v1 v2. ([m, p] \<turnstile> q1 \<mapsto> v1) \<and> ([m,p] \<turnstile> q2 \<mapsto> v2) \<longrightarrow> 
            (val_to_bool v1 \<longrightarrow> val_to_bool v2))"

fun impliesnot_valid :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" (infix "\<Zpinj>" 50) where
  "impliesnot_valid q1 q2 = 
    (\<forall>m p v1 v2. ([m, p] \<turnstile> q1 \<mapsto> v1) \<and> ([m,p] \<turnstile> q2 \<mapsto> v2) \<longrightarrow> 
            (val_to_bool v1 \<longrightarrow> \<not>val_to_bool v2))"

text \<open>The relation @{term "q1 \<Zinj> q2"} means @{term "q1 \<longrightarrow> q2"} is universally valid, 
      and the relation @{term "q1 \<Zpinj> q2"} means @{term "q1 \<longrightarrow> \<not>q2"} is universally valid.\<close>

lemma eval_negated:
  "([m, p] \<turnstile> q \<mapsto> v) \<longleftrightarrow> ([m, p] \<turnstile> (UnaryExpr UnaryLogicNegation q2) \<mapsto> intvalnegate v)"
proof (cases "[m, p] \<turnstile> q \<mapsto> v")
  case True
  then show ?thesis sorry
next
  case False
  then show ?thesis sorry
qed

lemma impliesnot_as_implies:
  "(q1 \<Zpinj> q2) \<longleftrightarrow> (q1 \<Zinj> (UnaryExpr UnaryLogicNegation q2))"
proof -
  have l2r: "(q1 \<Zpinj> q2) \<longrightarrow> (q1 \<Zinj> (UnaryExpr UnaryLogicNegation q2))"
  proof (cases "(q1 \<Zpinj> q2)")
    case True
    then show ?thesis
    proof -
      have a: "(\<forall>m p v1 v2. ([m, p] \<turnstile> q1 \<mapsto> v1) \<and> ([m,p] \<turnstile> q2 \<mapsto> v2) \<longrightarrow> 
            (val_to_bool v1 \<longrightarrow> \<not>val_to_bool v2))"
        using True by auto
      have b: "(\<forall>m p v2. ([m, p] \<turnstile> q2 \<mapsto> v2) \<longrightarrow> 
            ([m, p] \<turnstile> (UnaryExpr UnaryLogicNegation q2) \<mapsto> unary_eval UnaryLogicNegation v2))"
        sorry
      show ?thesis sorry 
    qed      
  next
    case False
    then show ?thesis sorry
  qed
  have r2l: "(q1 \<Zinj> (UnaryExpr UnaryLogicNegation q2)) \<longrightarrow> (q1 \<Zpinj> q2)"
  proof (cases "q1 \<Zinj> (UnaryExpr UnaryLogicNegation q2)")
    case True
    then show ?thesis sorry
  next
    case False
    then show ?thesis by blast
  qed
  show ?thesis using l2r r2l by blast   
qed



lemma eq_impliesnot_less_helper:
  "v1 = v2 \<longrightarrow> \<not>(int_signed_value b v1 < int_signed_value b v2)" 
  by force 

lemma eq_impliesnot_less_val:
  "val_to_bool(intval_equals v1 v2) \<longrightarrow> \<not>val_to_bool(intval_less_than v1 v2)"
  proof -
  have unfoldEqualDefined: "(intval_equals v1 v2 \<noteq> UndefVal) \<Longrightarrow>
        (val_to_bool(intval_equals v1 v2) \<longrightarrow> (\<not>(val_to_bool(intval_less_than v1 v2))))"
    subgoal premises p
  proof -
    obtain v1b v1v where v1v: "v1 = IntVal v1b v1v"
      by (metis array_length.cases intval_equals.simps(2,3,4,5) p)
    obtain v2b v2v where v2v: "v2 = IntVal v2b v2v"
      by (metis Value.exhaust_sel intval_equals.simps(6,7,8,9) p)
    have sameWidth: "v1b=v2b"
      by (metis bool_to_val_bin.simps intval_equals.simps(1) p v1v v2v)
    have unfoldEqual: "intval_equals v1 v2 = (bool_to_val (v1v=v2v))"
      by (simp add: sameWidth v1v v2v)
    have unfoldLessThan: "intval_less_than v1 v2 = (bool_to_val (int_signed_value v1b v1v < int_signed_value v2b v2v))"
      by (simp add: sameWidth v1v v2v)
    have val: "((v1v=v2v)) \<longrightarrow> (\<not>((int_signed_value v1b v1v < int_signed_value v2b v2v)))"
      using sameWidth by auto
    have doubleCast0: "val_to_bool (bool_to_val ((v1v = v2v))) = (v1v = v2v)"
      using bool_to_val.elims val_to_bool.simps(1) by fastforce
    have doubleCast1: "val_to_bool (bool_to_val ((int_signed_value v1b v1v < int_signed_value v2b v2v))) =
                                                 (int_signed_value v1b v1v < int_signed_value v2b v2v)"
      using bool_to_val.elims val_to_bool.simps(1) by fastforce
    then show ?thesis
      using p val unfolding unfoldEqual unfoldLessThan doubleCast0 doubleCast1 by blast
  qed done
  show ?thesis
    by (metis Value.distinct(1) val_to_bool.elims(2) unfoldEqualDefined)
qed

lemma eq_impliesnot_less_rev_val:
  "val_to_bool(intval_equals v1 v2) \<longrightarrow> \<not>val_to_bool(intval_less_than v2 v1)"
proof -
  have a: "intval_equals v1 v2 = intval_equals v2 v1"
    apply (cases "intval_equals v1 v2 = UndefVal")
    apply (smt (z3) bool_to_val_bin.simps intval_equals.elims intval_equals.simps)
    subgoal premises p
    proof -
      obtain v1b v1v where v1v: "v1 = IntVal v1b v1v"
        by (metis Value.exhaust_sel intval_equals.simps(2,3,4,5) p)
      obtain v2b v2v where v2v: "v2 = IntVal v2b v2v"
        by (metis Value.exhaust_sel intval_equals.simps(6,7,8,9) p)
      then show ?thesis
        by (smt (verit) bool_to_val_bin.simps intval_equals.simps(1) v1v)
    qed done
  show ?thesis
    using a eq_impliesnot_less_val by presburger
qed

lemma less_impliesnot_rev_less_val:
  "val_to_bool(intval_less_than v1 v2) \<longrightarrow> \<not>val_to_bool(intval_less_than v2 v1)"
  apply (rule impI)
  subgoal premises p
  proof -
    obtain v1b v1v where v1v: "v1 = IntVal v1b v1v"
      by (metis Value.exhaust_sel intval_less_than.simps(2,3,4,5) p val_to_bool.simps(2))
    obtain v2b v2v where v2v: "v2 = IntVal v2b v2v"
      by (metis Value.exhaust_sel intval_less_than.simps(6,7,8,9) p val_to_bool.simps(2))
    then have unfoldLessThanRHS: "intval_less_than v2 v1 =
                                 (bool_to_val (int_signed_value v2b v2v < int_signed_value v1b v1v))"
      using p v1v by force
    then have unfoldLessThanLHS: "intval_less_than v1 v2 =
                                 (bool_to_val (int_signed_value v1b v1v < int_signed_value v2b v2v))"
      using bool_to_val_bin.simps intval_less_than.simps(1) p v1v v2v val_to_bool.simps(2) by auto
    then have symmetry: "(int_signed_value v2b v2v < int_signed_value v1b v1v) \<longrightarrow>
                       (\<not>(int_signed_value v1b v1v < int_signed_value v2b v2v))"
      by simp
    then show ?thesis
      using p unfoldLessThanLHS unfoldLessThanRHS by fastforce
  qed done

lemma less_impliesnot_eq_val:
  "val_to_bool(intval_less_than v1 v2) \<longrightarrow> \<not>val_to_bool(intval_equals v1 v2)"
  using eq_impliesnot_less_val by blast 

lemma logic_negate_type:
  assumes "[m, p] \<turnstile> UnaryExpr UnaryLogicNegation x \<mapsto> v"
  shows "\<exists>b v2. [m, p] \<turnstile> x \<mapsto> IntVal b v2"
  using assms
  by (metis UnaryExprE intval_logic_negation.elims unary_eval.simps(4))

lemma intval_logic_negation_inverse:
  assumes "b > 0"
  assumes "x = IntVal b v"
  shows "val_to_bool (intval_logic_negation x) \<longleftrightarrow> \<not>(val_to_bool x)"
  using assms by (cases x; auto simp: logic_negate_def) 

lemma logic_negation_relation_tree:
  assumes "[m, p] \<turnstile> y \<mapsto> val"
  assumes "[m, p] \<turnstile> UnaryExpr UnaryLogicNegation y \<mapsto> invval"
  shows "val_to_bool val \<longleftrightarrow> \<not>(val_to_bool invval)"
  using assms using intval_logic_negation_inverse
  by (metis UnaryExprE evalDet eval_bits_1_64 logic_negate_type unary_eval.simps(4))

text \<open>The following theorem shows that the known true/false rules are valid.\<close>

theorem implies_valid:
  shows "(impliesy q1 q2 (Some True) \<longrightarrow> (q1 \<Zinj> q2)) \<and>
         (impliesy q1 q2 (Some False) \<longrightarrow> (q1 \<Zpinj> q2))"
(*proof (induct q1 q2 rule: impliesy.induct) *)
  sorry

theorem implies_impliesnot_valid:
  shows "((q1 \<Rrightarrow> q2) \<longrightarrow> (q1 \<Zinj> q2)) \<and>
         ((q1 \<Rrightarrow>\<not> q2) \<longrightarrow> (q1 \<Zpinj> q2))"
          (is "(?imp \<longrightarrow> ?val) \<and> (?notimp \<longrightarrow> ?notval)")
proof (induct q1 q2  rule: impliesx_impliesnot.induct)
  case (q_imp_q q)
  then show ?case 
    using evalDet by fastforce
next
  case (eq_impliesnot_less x y)
  then show ?case apply auto[1] using eq_impliesnot_less_val evalDet by blast
next
  case (eq_impliesnot_less_rev x y)
  then show ?case apply auto[1] using eq_impliesnot_less_rev_val evalDet by blast
next
  case (less_impliesnot_rev_less x y)
  then show ?case apply auto[1] using less_impliesnot_rev_less_val evalDet by blast
next
  case (less_impliesnot_eq x y)
  then show ?case apply auto[1] using less_impliesnot_eq_val evalDet by blast
next
  case (less_impliesnot_eq_rev x y)
  then show ?case apply auto[1] using eq_impliesnot_less_rev_val evalDet by metis 
next
  case (negate_true x y)
  then show ?case apply auto[1]
    by (metis logic_negation_relation_tree unary_eval.simps(4) unfold_unary)
next
  case (negate_false x y)
  then show ?case apply auto[1]
    by (metis UnaryExpr logic_negation_relation_tree unary_eval.simps(4)) 
qed








subsection \<open>OLD Individual Elimination Rules\<close>

text \<open>
We introduce a type @{term "TriState"} (as in the GraalVM compiler) to represent when static
analysis can tell us information about the value of a Boolean expression.
If @{term "Unknown"} then no information can be inferred and if
@{term "KnownTrue"}/@{term "KnownFalse"} one can infer the expression is always true/false.
\<close>
datatype TriState = Unknown | KnownTrue | KnownFalse

text \<open>
The implies relation corresponds to the LogicNode.implies
method from the compiler which attempts to infer when one
logic nodes value can be inferred from a known logic node.
\<close>
inductive implies :: "IRGraph \<Rightarrow> IRNode \<Rightarrow> IRNode \<Rightarrow> TriState \<Rightarrow> bool"
  ("_ \<turnstile> _ & _ \<hookrightarrow> _") for g where
  eq_imp_less:
  "g \<turnstile> (IntegerEqualsNode x y) & (IntegerLessThanNode x y) \<hookrightarrow> KnownFalse" |
  eq_imp_less_rev:
  "g \<turnstile> (IntegerEqualsNode x y) & (IntegerLessThanNode y x) \<hookrightarrow> KnownFalse" |
  less_imp_rev_less:
  "g \<turnstile> (IntegerLessThanNode x y) & (IntegerLessThanNode y x) \<hookrightarrow> KnownFalse" |
  less_imp_not_eq:
  "g \<turnstile> (IntegerLessThanNode x y) & (IntegerEqualsNode x y) \<hookrightarrow> KnownFalse" |
  less_imp_not_eq_rev:
  "g \<turnstile> (IntegerLessThanNode x y) & (IntegerEqualsNode y x) \<hookrightarrow> KnownFalse" |

  x_imp_x:
  "g \<turnstile> x & x \<hookrightarrow> KnownTrue" |

  negate_false:
  "\<lbrakk>g \<turnstile> x & (kind g y) \<hookrightarrow> KnownTrue\<rbrakk> \<Longrightarrow> g \<turnstile> x & (LogicNegationNode y) \<hookrightarrow> KnownFalse" |
  negate_true:
  "\<lbrakk>g \<turnstile> x & (kind g y) \<hookrightarrow> KnownFalse\<rbrakk> \<Longrightarrow> g \<turnstile> x & (LogicNegationNode y) \<hookrightarrow> KnownTrue"

text \<open>Total relation over partial implies relation\<close>
inductive condition_implies :: "IRGraph \<Rightarrow> IRNode \<Rightarrow> IRNode \<Rightarrow> TriState \<Rightarrow> bool"
  ("_ \<turnstile> _ & _ \<rightharpoonup> _") for g where
  "\<lbrakk>\<not>(g \<turnstile> a & b \<hookrightarrow> imp)\<rbrakk> \<Longrightarrow> (g \<turnstile> a & b \<rightharpoonup> Unknown)" |
  "\<lbrakk>(g \<turnstile> a & b \<hookrightarrow> imp)\<rbrakk> \<Longrightarrow> (g \<turnstile> a & b \<rightharpoonup> imp)"


inductive implies_tree :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool \<Rightarrow> bool"
  ("_ & _ \<hookrightarrow> _") where
  eq_imp_less: 
  "(BinaryExpr BinIntegerEquals x y) & (BinaryExpr BinIntegerLessThan x y) \<hookrightarrow> False" |
  eq_imp_less_rev:
  "(BinaryExpr BinIntegerEquals x y) & (BinaryExpr BinIntegerLessThan y x) \<hookrightarrow> False" |
  less_imp_rev_less:
  "(BinaryExpr BinIntegerLessThan x y) & (BinaryExpr BinIntegerLessThan y x) \<hookrightarrow> False" |
  less_imp_not_eq:
  "(BinaryExpr BinIntegerLessThan x y) & (BinaryExpr BinIntegerEquals x y) \<hookrightarrow> False" |
  less_imp_not_eq_rev:
  "(BinaryExpr BinIntegerLessThan x y) & (BinaryExpr BinIntegerEquals y x) \<hookrightarrow> False" |
  x_imp_x:
  "x & x \<hookrightarrow> True" |
  negate_false:
  "\<lbrakk>x & y \<hookrightarrow> True\<rbrakk> \<Longrightarrow> x & (UnaryExpr UnaryLogicNegation y) \<hookrightarrow> False" |
  negate_true:
  "\<lbrakk>x & y \<hookrightarrow> False\<rbrakk> \<Longrightarrow> x & (UnaryExpr UnaryLogicNegation y) \<hookrightarrow> True"

text \<open>
Proofs that the implies relation is correct with respect to the 
existing evaluation semantics.
\<close>

lemma logic_negation_relation:
  assumes "[g, m, p] \<turnstile> y \<mapsto> val"
  assumes "kind g neg = LogicNegationNode y"
  assumes "[g, m, p] \<turnstile> neg \<mapsto> invval"
  assumes "invval \<noteq> UndefVal"
  shows "val_to_bool val \<longleftrightarrow> \<not>(val_to_bool invval)"
  using assms
  by (metis LogicNegationNode encodeeval_def logic_negation_relation_tree repDet)


lemma implies_valid_bw:
  assumes "x & y \<hookrightarrow> imp"
  assumes "[m, p] \<turnstile> x \<mapsto> v1"
  assumes "[m, p] \<turnstile> y \<mapsto> v2"
  shows "(imp \<longrightarrow> (val_to_bool v1 \<longrightarrow> val_to_bool v2)) \<and>
         (\<not>imp \<longrightarrow> (val_to_bool v1 \<longrightarrow> \<not>(val_to_bool v2)))"
    (is "(?TP \<longrightarrow> ?TC) \<and> (?FP \<longrightarrow> ?FC)")
  apply (intro conjI; rule impI)
proof -
  assume KnownTrue: ?TP
  show ?TC
  using assms(1) KnownTrue assms(2-) proof (induct x y imp rule: implies_tree.induct)
    case (eq_imp_less x y)
    then show ?case by simp
  next
    case (eq_imp_less_rev x y)
    then show ?case by simp
  next
    case (less_imp_rev_less x y)
    then show ?case by simp
  next
    case (less_imp_not_eq x y)
    then show ?case by simp
  next
    case (less_imp_not_eq_rev x y)
    then show ?case by simp
  next
    case (x_imp_x)
    then show ?case
      by (metis evalDet)
  next
    case (negate_false x1)
    then show ?case using evalDet
      using assms(2,3) by blast
  next
    case (negate_true x y)
    then show ?case
      using logic_negation_relation_tree sorry
  qed
next
  assume KnownFalse: ?FP
  show ?FC using assms KnownFalse proof (induct x y imp rule: implies_tree.induct)
    case (eq_imp_less x y)
    obtain xval where xval: "[m, p] \<turnstile> x \<mapsto> xval"
      using eq_imp_less(1) eq_imp_less.prems(3)
      by blast
    then obtain yval where yval: "[m, p] \<turnstile> y \<mapsto> yval"
      using eq_imp_less.prems(3)
      using eq_imp_less.prems(2) by blast
    have eqeval: "[m, p] \<turnstile> (BinaryExpr BinIntegerEquals x y) \<mapsto> intval_equals xval yval"
      using xval yval evaltree.BinaryExpr
      by (metis BinaryExprE bin_eval.simps(11) eq_imp_less.prems(1) evalDet)
    have lesseval: "[m, p] \<turnstile> (BinaryExpr BinIntegerLessThan x y) \<mapsto> intval_less_than xval yval"
      using xval yval evaltree.BinaryExpr
      by (metis BinaryExprE bin_eval.simps(12) eq_imp_less.prems(2) evalDet)
    have "val_to_bool (intval_equals xval yval) \<longrightarrow> \<not>(val_to_bool (intval_less_than xval yval))"
      apply (cases xval; cases yval; auto)
      by (smt (verit, best) bool_to_val.simps(2) val_to_bool.simps(1))
    then show ?case
      using eqeval lesseval
      by (metis eq_imp_less.prems(1) eq_imp_less.prems(2) evalDet)
  next
    case (eq_imp_less_rev x y)
    obtain xval where xval: "[m, p] \<turnstile> x \<mapsto> xval"
      using eq_imp_less_rev.prems(3)
      using eq_imp_less_rev.prems(2) by blast
    obtain yval where yval: "[m, p] \<turnstile> y \<mapsto> yval"
      using eq_imp_less_rev.prems(3)
      using eq_imp_less_rev.prems(2) by blast
    have eqeval: "[m, p] \<turnstile> (BinaryExpr BinIntegerEquals x y) \<mapsto> intval_equals xval yval"
      using xval yval evaltree.BinaryExpr
      by (metis BinaryExprE bin_eval.simps(11) eq_imp_less_rev.prems(1) evalDet)
    have lesseval: "[m, p] \<turnstile> (BinaryExpr BinIntegerLessThan y x) \<mapsto> intval_less_than yval xval"
      using xval yval evaltree.BinaryExpr
      by (metis BinaryExprE bin_eval.simps(12) eq_imp_less_rev.prems(2) evalDet)
    have "val_to_bool (intval_equals xval yval) \<longrightarrow> \<not>(val_to_bool (intval_less_than yval xval))"
      apply (cases xval; cases yval; auto)
      by (metis (full_types) bool_to_val.simps(2) less_irrefl val_to_bool.simps(1))
    then show ?case
      using eqeval lesseval
      by (metis eq_imp_less_rev.prems(1) eq_imp_less_rev.prems(2) evalDet)
  next
    case (less_imp_rev_less x y)
    obtain xval where xval: "[m, p] \<turnstile> x \<mapsto> xval"
      using less_imp_rev_less.prems(3)
      using less_imp_rev_less.prems(2) by blast
    obtain yval where yval: "[m, p] \<turnstile> y \<mapsto> yval"
      using less_imp_rev_less.prems(3)
      using less_imp_rev_less.prems(2) by blast
    have lesseval: "[m, p] \<turnstile> (BinaryExpr BinIntegerLessThan x y) \<mapsto> intval_less_than xval yval"
      using xval yval evaltree.BinaryExpr
      by (metis BinaryExprE bin_eval.simps(12) evalDet less_imp_rev_less.prems(1))
    have revlesseval: "[m, p] \<turnstile> (BinaryExpr BinIntegerLessThan y x) \<mapsto> intval_less_than yval xval"
      using xval yval evaltree.BinaryExpr
      by (metis BinaryExprE bin_eval.simps(12) evalDet less_imp_rev_less.prems(2))
    have "val_to_bool (intval_less_than xval yval) \<longrightarrow> \<not>(val_to_bool (intval_less_than yval xval))"
      apply (cases xval; cases yval; auto)
      by (smt (verit) bool_to_val.simps(2) val_to_bool.simps(1))
    then show ?case
      by (metis evalDet less_imp_rev_less.prems(1) less_imp_rev_less.prems(2) lesseval revlesseval)
  next
    case (less_imp_not_eq x y)
    obtain xval where xval: "[m, p] \<turnstile> x \<mapsto> xval"
      using less_imp_not_eq.prems(3)
      using less_imp_not_eq.prems(1) by blast
    obtain yval where yval: "[m, p] \<turnstile> y \<mapsto> yval"
      using less_imp_not_eq.prems(3)
      using less_imp_not_eq.prems(1) by blast
    have eqeval: "[m, p] \<turnstile> (BinaryExpr BinIntegerEquals x y) \<mapsto> intval_equals xval yval"
      using xval yval evaltree.BinaryExpr
      by (metis BinaryExprE bin_eval.simps(11) evalDet less_imp_not_eq.prems(2))
    have lesseval: "[m, p] \<turnstile> (BinaryExpr BinIntegerLessThan x y) \<mapsto> intval_less_than xval yval"
      using xval yval evaltree.BinaryExpr
      by (metis BinaryExprE bin_eval.simps(12) evalDet less_imp_not_eq.prems(1))
    have "val_to_bool (intval_less_than xval yval) \<longrightarrow> \<not>(val_to_bool (intval_equals xval yval))"
      apply (cases xval; cases yval; auto)
      by (smt (verit, best) bool_to_val.simps(2) val_to_bool.simps(1))
    then show ?case
      by (metis eqeval evalDet less_imp_not_eq.prems(1) less_imp_not_eq.prems(2) lesseval)
  next
    case (less_imp_not_eq_rev x y)
    obtain xval where xval: "[m, p] \<turnstile> x \<mapsto> xval"
      using less_imp_not_eq_rev.prems(3)
      using less_imp_not_eq_rev.prems(1) by blast
    obtain yval where yval: "[m, p] \<turnstile> y \<mapsto> yval"
      using less_imp_not_eq_rev.prems(3)
      using less_imp_not_eq_rev.prems(1) by blast
    have eqeval: "[m, p] \<turnstile> (BinaryExpr BinIntegerEquals y x) \<mapsto> intval_equals yval xval"
      using xval yval evaltree.BinaryExpr
      by (metis BinaryExprE bin_eval.simps(11) evalDet less_imp_not_eq_rev.prems(2))
    have lesseval: "[m, p] \<turnstile> (BinaryExpr BinIntegerLessThan x y) \<mapsto> intval_less_than xval yval"
      using xval yval evaltree.BinaryExpr
      by (metis BinaryExprE bin_eval.simps(12) evalDet less_imp_not_eq_rev.prems(1))
    have "val_to_bool (intval_less_than xval yval) \<longrightarrow> \<not>(val_to_bool (intval_equals yval xval))"
      apply (cases xval; cases yval; auto)
      by (smt (verit, best) bool_to_val.simps(2) val_to_bool.simps(1))
    then show ?case
      by (metis eqeval evalDet less_imp_not_eq_rev.prems(1) less_imp_not_eq_rev.prems(2) lesseval)
  next
    case (x_imp_x x1)
    then show ?case by simp
  next
    case (negate_false x y)
    then show ?case sorry
  next
    case (negate_true x1)
    then show ?case by simp
  qed
qed

lemma implies_true_valid:
  assumes "x & y \<hookrightarrow> imp"
  assumes "imp"
  assumes "[m, p] \<turnstile> x \<mapsto> v1"
  assumes "[m, p] \<turnstile> y \<mapsto> v2"
  shows "val_to_bool v1 \<longrightarrow> val_to_bool v2"
  using assms implies_valid_bw eval_negated by blast

lemma implies_false_valid:
  assumes "x & y \<hookrightarrow> imp"
  assumes "\<not>imp"
  assumes "[m, p] \<turnstile> x \<mapsto> v1"
  assumes "[m, p] \<turnstile> y \<mapsto> v2"
  shows "val_to_bool v1 \<longrightarrow> \<not>(val_to_bool v2)"
  using assms implies_valid_bw eval_negated by blast 




subsection \<open>TryFold Elimination Rules\<close>

text \<open>
The following relation corresponds to the UnaryOpLogicNode.tryFold
and BinaryOpLogicNode.tryFold methods and their associated concrete implementations.

The relation determines if a logic operation can be shown true or false
through the stamp typing information.
\<close>
inductive tryFold :: "IRNode \<Rightarrow> (ID \<Rightarrow> Stamp) \<Rightarrow> bool \<Rightarrow> bool"
  where
  "\<lbrakk>alwaysDistinct (stamps x) (stamps y)\<rbrakk> 
    \<Longrightarrow> tryFold (IntegerEqualsNode x y) stamps False" |
  "\<lbrakk>neverDistinct (stamps x) (stamps y)\<rbrakk> 
    \<Longrightarrow> tryFold (IntegerEqualsNode x y) stamps True" |
  "\<lbrakk>is_IntegerStamp (stamps x);
    is_IntegerStamp (stamps y);
    stpi_upper (stamps x) < stpi_lower (stamps y)\<rbrakk> 
    \<Longrightarrow> tryFold (IntegerLessThanNode x y) stamps True" |
  "\<lbrakk>is_IntegerStamp (stamps x);
    is_IntegerStamp (stamps y);
    stpi_lower (stamps x) \<ge> stpi_upper (stamps y)\<rbrakk> 
    \<Longrightarrow> tryFold (IntegerLessThanNode x y) stamps False"

(*code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) tryFold .*)
code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool) tryFold .

text \<open>
Proofs that show that when the stamp lookup function is well-formed,
the tryFold relation correctly predicts the output value with respect to
our evaluation semantics.
\<close>
lemma
  assumes "kind g nid = IntegerEqualsNode x y"
  assumes "[g, m, p] \<turnstile> nid \<mapsto> v"
  assumes "([g, m, p] \<turnstile> x \<mapsto> xval) \<and> ([g, m, p] \<turnstile> y \<mapsto> yval)"
  shows "val_to_bool (intval_equals xval yval) \<longleftrightarrow> v = IntVal 32 1"
proof -
  have "v = intval_equals xval yval"
    using assms(1, 2, 3) BinaryExprE IntegerEqualsNode bin_eval.simps(7)
    by (smt (verit) bin_eval.simps(11) encodeeval_def evalDet repDet)
  then show ?thesis using intval_equals.simps val_to_bool.simps
    by (smt (verit) bool_to_val.simps(1) bool_to_val.simps(2) bool_to_val_bin.simps 
        intval_equals.elims one_neq_zero)
qed

lemma tryFoldIntegerEqualsAlwaysDistinct:
  assumes "wf_stamp g stamps"
  assumes "kind g nid = (IntegerEqualsNode x y)"
  assumes "[g, m, p] \<turnstile> nid \<mapsto> v"
  assumes "alwaysDistinct (stamps x) (stamps y)"
  shows "v = IntVal 32 0"
proof -
  have "\<forall> val. \<not>(valid_value val (join (stamps x) (stamps y)))"
    using assms(1,4) unfolding alwaysDistinct.simps
    by (smt (verit, best) is_stamp_empty.elims(2) valid_int valid_value.simps(1))
  obtain xv where "[g, m, p] \<turnstile> x \<mapsto> xv"
    using assms using assms(2,3) unfolding encodeeval_def sorry
  have "\<not>(\<exists> val . ([g, m, p] \<turnstile> x \<mapsto> val) \<and> ([g, m, p] \<turnstile> y \<mapsto> val))"
    using assms(1,4) unfolding alwaysDistinct.simps wf_stamp.simps encodeeval_def sorry
  then show ?thesis sorry
qed

lemma tryFoldIntegerEqualsNeverDistinct:
  assumes "wf_stamp g stamps"
  assumes "kind g nid = (IntegerEqualsNode x y)"
  assumes "[g, m, p] \<turnstile> nid \<mapsto> v"
  assumes "neverDistinct (stamps x) (stamps y)"
  shows "v = IntVal 32 1"
  using assms IntegerEqualsNodeE sorry

lemma tryFoldIntegerLessThanTrue:
  assumes "wf_stamp g stamps"
  assumes "kind g nid = (IntegerLessThanNode x y)"
  assumes "[g, m, p] \<turnstile> nid \<mapsto> v"
  assumes "stpi_upper (stamps x) < stpi_lower (stamps y)"
  shows "v = IntVal 32 1"
proof -
  have stamp_type: "is_IntegerStamp (stamps x)"
    using assms
    sorry
  obtain xval where xval: "[g, m, p] \<turnstile> x \<mapsto> xval"
    using assms(2,3) sorry
  obtain yval where yval: "[g, m, p] \<turnstile> y \<mapsto> yval"
    using assms(2,3) sorry
  have "is_IntegerStamp (stamps x) \<and> is_IntegerStamp (stamps y)"
    using assms(4)
    sorry
  then have "val_to_bool (intval_less_than xval yval)"
    sorry
  then show ?thesis
    sorry
qed

lemma tryFoldIntegerLessThanFalse:
  assumes "wf_stamp g stamps"
  assumes "kind g nid = (IntegerLessThanNode x y)"
  assumes "[g, m, p] \<turnstile> nid \<mapsto> v"
  assumes "stpi_lower (stamps x) \<ge> stpi_upper (stamps y)"
  shows "v = IntVal 32 0"
  proof -
  have stamp_type: "is_IntegerStamp (stamps x)"
    using assms
    sorry
  obtain xval where xval: "[g, m, p] \<turnstile> x \<mapsto> xval"
    using assms(2,3) sorry
  obtain yval where yval: "[g, m, p] \<turnstile> y \<mapsto> yval"
    using assms(2,3) sorry
  have "is_IntegerStamp (stamps x) \<and> is_IntegerStamp (stamps y)"
    using assms(4)
    sorry
  then have "\<not>(val_to_bool (intval_less_than xval yval))"
    sorry
  then show ?thesis
    sorry
qed

theorem tryFoldProofTrue:
  assumes "wf_stamp g stamps"
  assumes "tryFold (kind g nid) stamps True"
  assumes "[g, m, p] \<turnstile> nid \<mapsto> v"
  shows "val_to_bool v"
  using assms(2) proof (induction "kind g nid" stamps True rule: tryFold.induct)
case (1 stamps x y)
  then show ?case using tryFoldIntegerEqualsAlwaysDistinct assms
    by force
next
  case (2 stamps x y)
  then show ?case using tryFoldIntegerEqualsAlwaysDistinct assms
    by (smt (verit, best) one_neq_zero tryFold.cases tryFoldIntegerEqualsNeverDistinct tryFoldIntegerLessThanTrue val_to_bool.simps(1))
next
  case (3 stamps x y)
  then show ?case using tryFoldIntegerLessThanTrue assms
    by (smt (verit, best) one_neq_zero tryFold.cases tryFoldIntegerEqualsNeverDistinct val_to_bool.simps(1))
next
case (4 stamps x y)
  then show ?case using tryFoldIntegerLessThanFalse assms sorry
qed

theorem tryFoldProofFalse:
  assumes "wf_stamp g stamps"
  assumes "tryFold (kind g nid) stamps False"
  assumes "[g, m, p] \<turnstile> nid \<mapsto> v"
  shows "\<not>(val_to_bool v)"
using assms(2) proof (induction "kind g nid" stamps False rule: tryFold.induct)
case (1 stamps x y)
  then show ?case using tryFoldIntegerEqualsAlwaysDistinct assms sorry
next
case (2 stamps x y)
  then show ?case using tryFoldIntegerEqualsNeverDistinct assms sorry
next
  case (3 stamps x y)
  then show ?case using tryFoldIntegerLessThanTrue assms sorry
next
  case (4 stamps x y)
  then show ?case using tryFoldIntegerLessThanFalse assms sorry

qed


subsection \<open>Conditional Elimination Step\<close>

inductive_cases StepE:
  "g, p \<turnstile> (nid,m,h) \<rightarrow> (nid',m',h)"

text \<open>
Perform conditional elimination rewrites on the graph for a particular node.

In order to determine conditional eliminations appropriately the rule needs two
data structures produced by static analysis.
The first parameter is the set of IRNodes that we know result in a true value
when evaluated.
The second parameter is a mapping from node identifiers to the flow-sensitive stamp.

The relation transforms the third parameter to the fifth parameter for a node identifier
which represents the fourth parameter.
\<close>

inductive condset_implies :: "IRExpr set \<Rightarrow> IRExpr \<Rightarrow> bool \<Rightarrow> bool" where
  impliesTrue:
  "(\<exists>ce \<in> conds . (ce \<Rrightarrow> cond)) \<Longrightarrow> condset_implies conds cond True" |
  impliesFalse:
  "(\<exists>ce \<in> conds . (ce \<Rrightarrow>\<not> cond)) \<Longrightarrow> condset_implies conds cond False"

(*code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) condset_implies .*)
code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool) condset_implies .

fun conds_implies :: "IRExpr set \<Rightarrow> (ID \<Rightarrow> Stamp) \<Rightarrow> IRNode \<Rightarrow> IRExpr \<Rightarrow> bool option" where
  "conds_implies conds stamps condNode cond = 
    (if condset_implies conds cond True \<or> tryFold condNode stamps True 
      then Some True
    else if condset_implies conds cond False \<or> tryFold condNode stamps False
      then Some False
    else None)"

inductive ConditionalEliminationStep :: 
  "IRExpr set \<Rightarrow> (ID \<Rightarrow> Stamp) \<Rightarrow> ID \<Rightarrow> IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool"
  where
  impliesConds:
  "\<lbrakk>kind g ifcond = (IfNode cid t f);
    g \<turnstile> cid \<simeq> cond; 
    condNode = kind g cid;
    conds_implies conds stamps condNode cond = (Some True);
    g' = constantCondition True ifcond (kind g ifcond) g
    \<rbrakk> \<Longrightarrow> ConditionalEliminationStep conds stamps ifcond g g'" |

  impliesFalse:
  "\<lbrakk>kind g ifcond = (IfNode cid t f);
    g \<turnstile> cid \<simeq> cond;
    condNode = kind g cid;
    conds_implies conds stamps condNode cond = (Some False);
    g' = constantCondition False ifcond (kind g ifcond) g
    \<rbrakk> \<Longrightarrow> ConditionalEliminationStep conds stamps ifcond g g'" |

  unknown:
  "\<lbrakk>kind g ifcond = (IfNode cid t f);
    g \<turnstile> cid \<simeq> cond; 
    condNode = kind g cid;
    conds_implies conds stamps condNode cond = None
    \<rbrakk> \<Longrightarrow> ConditionalEliminationStep conds stamps ifcond g g" |

  notIfNode:
  "\<not>(is_IfNode (kind g ifcond)) \<Longrightarrow>
    ConditionalEliminationStep conds stamps ifcond g g"


(*
  tryFoldTrue:
  "\<lbrakk>kind g ifcond = (IfNode cid t f);
    cond = kind g cid;
    tryFold (kind g cid) stamps True;
    g' = constantCondition True ifcond (kind g ifcond) g
    \<rbrakk> \<Longrightarrow> ConditionalEliminationStep conds stamps ifcond g g'" |

  tryFoldFalse:
  "\<lbrakk>kind g ifcond = (IfNode cid t f);
    cond = kind g cid;
    tryFold (kind g cid) stamps False;
    g' = constantCondition False ifcond (kind g ifcond) g
    \<rbrakk> \<Longrightarrow> ConditionalEliminationStep conds stamps ifcond g g'"
*)


code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) ConditionalEliminationStep .

thm ConditionalEliminationStep.equation



subsection \<open>Control-flow Graph Traversal\<close>

type_synonym Seen = "ID set"
type_synonym Condition = "IRExpr"
type_synonym Conditions = "Condition list"
type_synonym StampFlow = "(ID \<Rightarrow> Stamp) list"
type_synonym ToVisit = "ID list"


text \<open>
nextEdge helps determine which node to traverse next by returning the first successor
edge that isn't in the set of already visited nodes.
If there is not an appropriate successor, None is returned instead.
\<close>
fun nextEdge :: "Seen \<Rightarrow> ID \<Rightarrow> IRGraph \<Rightarrow> ID option" where
  "nextEdge seen nid g = 
    (let nids = (filter (\<lambda>nid'. nid' \<notin> seen) (successors_of (kind g nid))) in 
     (if length nids > 0 then Some (hd nids) else None))"

text \<open>
pred determines which node, if any, acts as the predecessor of another.

Merge nodes represent a special case where-in the predecessor exists as
an input edge of the merge node, to simplify the traversal we treat only
the first input end node as the predecessor, ignoring that multiple nodes
may act as a successor.

For all other nodes, the predecessor is the first element of the predecessors set.
Note that in a well-formed graph there should only be one element in the predecessor set.\<close>
fun preds :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID list" where
  "preds g nid = (case kind g nid of
    (MergeNode ends _ _) \<Rightarrow> ends |
    _ \<Rightarrow> 
      sorted_list_of_set (IRGraph.predecessors g nid)
  )"

fun pred :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID option" where
  "pred g nid = (case kind g nid of
    (MergeNode ends _ _) \<Rightarrow> Some (hd ends) |
    _ \<Rightarrow> 
      (if IRGraph.predecessors g nid = {} 
        then None else
        Some (hd (sorted_list_of_set (IRGraph.predecessors g nid)))
      )
  )"


text \<open>
When the basic block of an if statement is entered, we know that the condition of the
preceding if statement must be true.
As in the GraalVM compiler, we introduce the registerNewCondition function which roughly
corresponds to the ConditionalEliminationPhase.registerNewCondition.
This method updates the flow-sensitive stamp information based on the condition which
we know must be true. 
\<close>
fun clip_upper :: "Stamp \<Rightarrow> int \<Rightarrow> Stamp" where
  "clip_upper (IntegerStamp b l h) c = 
          (if c < h then (IntegerStamp b l c) else (IntegerStamp b l h))" |
  "clip_upper s c = s"
fun clip_lower :: "Stamp \<Rightarrow> int \<Rightarrow> Stamp" where
  "clip_lower (IntegerStamp b l h) c = 
          (if l < c then (IntegerStamp b c h) else (IntegerStamp b l c))" |
  "clip_lower s c = s"

fun registerNewCondition :: "IRGraph \<Rightarrow> IRNode \<Rightarrow> (ID \<Rightarrow> Stamp) \<Rightarrow> (ID \<Rightarrow> Stamp)" where
  (* constrain equality by joining the stamps *)
  "registerNewCondition g (IntegerEqualsNode x y) stamps =
    (stamps
      (x := join (stamps x) (stamps y)))
      (y := join (stamps x) (stamps y))" |
  (* constrain less than by removing overlapping stamps *)
  "registerNewCondition g (IntegerLessThanNode x y) stamps =
    (stamps
      (x := clip_upper (stamps x) ((stpi_lower (stamps y)) - 1)))
      (y := clip_lower (stamps y) ((stpi_upper (stamps x)) + 1))" |
  "registerNewCondition g (LogicNegationNode c) stamps =
    (case (kind g c) of
      (IntegerLessThanNode x y) \<Rightarrow>
        (stamps
          (x := clip_lower (stamps x) ((stpi_upper (stamps y)))))
          (y := clip_upper (stamps y) ((stpi_lower (stamps x))))
       | _ \<Rightarrow> stamps)" |
  "registerNewCondition g _ stamps = stamps"

fun hdOr :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "hdOr (x # xs) de = x" |
  "hdOr [] de = de"

(*
fun isCFGNode :: "IRNode \<Rightarrow> bool" where
  "isCFGNode (BeginNode _) = True" |
  "isCFGNode (EndNode) = True" |
  "isCFGNode _ = False"

inductive CFGSuccessor ::
  "IRGraph \<Rightarrow> (ID \<times> Seen \<times> ToVisit) \<Rightarrow> (ID \<times> Seen \<times> ToVisit) \<Rightarrow> bool"
  for g where
  \<comment> \<open>
  Forward traversal transitively through successors until
  a CFG node is reached.\<close>
  "\<lbrakk>Some nid' = nextEdge seen nid g;
    \<not>(isCFGNode (kind g nid'));
    CFGSuccessor g (nid', {nid} \<union> seen, nid # toVisit) (nid'', seen', toVisit')\<rbrakk> 
    \<Longrightarrow> CFGSuccessor g (nid, seen, toVisit) (nid'', seen', toVisit')" |
  "\<lbrakk>Some nid' = nextEdge seen nid g;
    isCFGNode (kind g nid')\<rbrakk>
    \<Longrightarrow> CFGSuccessor g (nid, seen, toVisit) (nid', {nid} \<union> seen, nid # toVisit)" |

  \<comment> \<open>
  Backwards traversal transitively through toVisit stack until
  a CFG node is reached.\<close>
  "\<lbrakk>toVisit = nid' # toVisit';
    CFGSuccessor g (nid', {nid} \<union> seen, nid # toVisit) (nid'', seen', toVisit')\<rbrakk> 
    \<Longrightarrow> CFGSuccessor g (nid, seen, toVisit) (nid'', seen', toVisit')"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) CFGSuccessor .
*)

type_synonym DominatorCache = "(ID, ID set) map"

inductive 
  dominators_all :: "IRGraph \<Rightarrow> DominatorCache \<Rightarrow> ID \<Rightarrow> ID set set \<Rightarrow> ID list \<Rightarrow> DominatorCache \<Rightarrow> ID set set \<Rightarrow> ID list \<Rightarrow> bool" and
  dominators :: "IRGraph \<Rightarrow> DominatorCache \<Rightarrow> ID \<Rightarrow> (ID set \<times> DominatorCache) \<Rightarrow> bool" where

  "\<lbrakk>pre = []\<rbrakk>
    \<Longrightarrow> dominators_all g c nid doms pre c doms pre" |

  "\<lbrakk>pre = pr # xs;
    (dominators g c pr (doms', c'));
    dominators_all g c' pr (doms \<union> {doms'}) xs c'' doms'' pre'\<rbrakk>
    \<Longrightarrow> dominators_all g c nid doms pre c'' doms'' pre'" |

  "\<lbrakk>preds g nid = []\<rbrakk>
    \<Longrightarrow> dominators g c nid ({nid}, c)" |
  
  "\<lbrakk>c nid = None;
    preds g nid = x # xs;
    dominators_all g c nid {} (preds g nid) c' doms pre';
    c'' = c'(nid \<mapsto> ({nid} \<union> (\<Inter>doms)))\<rbrakk>
    \<Longrightarrow> dominators g c nid (({nid} \<union> (\<Inter>doms)), c'')" |

  "\<lbrakk>c nid = Some doms\<rbrakk>
    \<Longrightarrow> dominators g c nid (doms, c)"

\<comment> \<open>
Trying to simplify by removing the 3rd case won't work.
A base case for root nodes is required as \<Inter>{} = coset []
which swallows anything unioned with it.
\<close>
value "\<Inter>({}::nat set set)"
value "- \<Inter>({}::nat set set)"
value "\<Inter>({{}, {0}}::nat set set)"
value "{0::nat} \<union> (\<Inter>{})"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool) dominators_all .
code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) dominators .

(* initial: ConditionalEliminationTest13_testSnippet2 *)
definition ConditionalEliminationTest13_testSnippet2_initial :: IRGraph where
  "ConditionalEliminationTest13_testSnippet2_initial = irgraph [
  (0, (StartNode (Some 2) 8), VoidStamp),
  (1, (ParameterNode 0), IntegerStamp 32 (-2147483648) (2147483647)),
  (2, (FrameState [] None None None), IllegalStamp),
  (3, (ConstantNode (new_int 32 (0))), IntegerStamp 32 (0) (0)),
  (4, (ConstantNode (new_int 32 (1))), IntegerStamp 32 (1) (1)),
  (5, (IntegerLessThanNode 1 4), VoidStamp),
  (6, (BeginNode 13), VoidStamp),
  (7, (BeginNode 23), VoidStamp),
  (8, (IfNode 5 7 6), VoidStamp),
  (9, (ConstantNode (new_int 32 (-1))), IntegerStamp 32 (-1) (-1)),
  (10, (IntegerEqualsNode 1 9), VoidStamp),
  (11, (BeginNode 17), VoidStamp),
  (12, (BeginNode 15), VoidStamp),
  (13, (IfNode 10 12 11), VoidStamp),
  (14, (ConstantNode (new_int 32 (-2))), IntegerStamp 32 (-2) (-2)),
  (15, (StoreFieldNode 15 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink2'' 14 (Some 16) None 19), VoidStamp),
  (16, (FrameState [] None None None), IllegalStamp),
  (17, (EndNode), VoidStamp),
  (18, (MergeNode [17, 19] (Some 20) 21), VoidStamp),
  (19, (EndNode), VoidStamp),
  (20, (FrameState [] None None None), IllegalStamp),
  (21, (StoreFieldNode 21 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink1'' 3 (Some 22) None 25), VoidStamp),
  (22, (FrameState [] None None None), IllegalStamp),
  (23, (EndNode), VoidStamp),
  (24, (MergeNode [23, 25] (Some 26) 27), VoidStamp),
  (25, (EndNode), VoidStamp),
  (26, (FrameState [] None None None), IllegalStamp),
  (27, (StoreFieldNode 27 ''org.graalvm.compiler.core.test.ConditionalEliminationTestBase::sink0'' 9 (Some 28) None 29), VoidStamp),
  (28, (FrameState [] None None None), IllegalStamp),
  (29, (ReturnNode None None), VoidStamp)
  ]"

(* :(
fun dominators :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID set" where
  "dominators g nid = {nid} \<union> (\<Inter> y \<in> preds g nid. dominators g y)"
*)

values "{(snd x) 13| x. dominators ConditionalEliminationTest13_testSnippet2_initial Map.empty 25 x}"

(*fun condition_of :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID option" where
  "condition_of g nid = (case (kind g nid) of
    (IfNode c t f) \<Rightarrow> Some c |
    _ \<Rightarrow> None)"*)

inductive
  condition_of :: "IRGraph \<Rightarrow> ID \<Rightarrow> (IRExpr \<times> IRNode) option \<Rightarrow> bool" where
  "\<lbrakk>Some ifcond = pred g nid;
    kind g ifcond = IfNode cond t f;

    i = find_index nid (successors_of (kind g ifcond));
    c = (if i = 0 then kind g cond else LogicNegationNode cond);
    rep g cond ce;
    ce' = (if i = 0 then ce else UnaryExpr UnaryLogicNegation ce)\<rbrakk>
  \<Longrightarrow> condition_of g nid (Some (ce', c))" |

  "\<lbrakk>pred g nid = None\<rbrakk> \<Longrightarrow> condition_of g nid None" |
  "\<lbrakk>pred g nid = Some nid';
    \<not>(is_IfNode (kind g nid'))\<rbrakk> \<Longrightarrow> condition_of g nid None"

inductive
  conditions_of_dominators :: "IRGraph \<Rightarrow> ID list \<Rightarrow> Conditions \<Rightarrow> Conditions \<Rightarrow> bool" where
  "\<lbrakk>nids = []\<rbrakk>
    \<Longrightarrow> conditions_of_dominators g nids conditions conditions" |

  "\<lbrakk>nids = nid # nids';
    condition_of g nid (Some (expr, _));
    conditions_of_dominators g nids' (expr # conditions) conditions'\<rbrakk>
    \<Longrightarrow> conditions_of_dominators g nids conditions conditions'" |

  "\<lbrakk>nids = nid # nids';
    condition_of g nid None;
    conditions_of_dominators g nids' conditions conditions'\<rbrakk>
    \<Longrightarrow> conditions_of_dominators g nids conditions conditions'"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) conditions_of_dominators .

inductive
  stamps_of_dominators :: "IRGraph \<Rightarrow> ID list \<Rightarrow> StampFlow \<Rightarrow> StampFlow \<Rightarrow> bool" where
  "\<lbrakk>nids = []\<rbrakk>
    \<Longrightarrow> stamps_of_dominators g nids stamps stamps" |

  "\<lbrakk>nids = nid # nids';
    condition_of g nid (Some (_, node));
    he = registerNewCondition g node (hd stamps);
    stamps_of_dominators g nids' (he # stamps) stamps'\<rbrakk>
    \<Longrightarrow> stamps_of_dominators g nids stamps stamps'" |

  "\<lbrakk>nids = nid # nids';
    condition_of g nid None;
    stamps_of_dominators g nids' stamps stamps'\<rbrakk>
    \<Longrightarrow> stamps_of_dominators g nids stamps stamps'"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) stamps_of_dominators .

inductive
  analyse :: "IRGraph \<Rightarrow> DominatorCache \<Rightarrow> ID \<Rightarrow> (Conditions \<times> StampFlow \<times> DominatorCache) \<Rightarrow> bool" where
  "\<lbrakk>dominators g c nid (doms, c');
    conditions_of_dominators g (sorted_list_of_set doms) [] conds;
    stamps_of_dominators g (sorted_list_of_set doms) [stamp g] stamps\<rbrakk>
    \<Longrightarrow> analyse g c nid (conds, stamps, c')"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) analyse .

values "{x. dominators ConditionalEliminationTest13_testSnippet2_initial Map.empty 13 x}"
values "{(conds, stamps, c). 
analyse ConditionalEliminationTest13_testSnippet2_initial Map.empty 13 (conds, stamps, c)}"
values "{(hd stamps) 1| conds stamps c .
analyse ConditionalEliminationTest13_testSnippet2_initial Map.empty 13 (conds, stamps, c)}"
values "{(hd stamps) 1| conds stamps c .
analyse ConditionalEliminationTest13_testSnippet2_initial Map.empty 27 (conds, stamps, c)}"



text \<open>
The Step relation is a small-step traversal of the graph which handles transitions between
individual nodes of the graph.

It relates a pairs of tuple of the current node, the set of seen nodes, 
the always true stack of IfNode conditions, and the flow-sensitive stamp information.
\<close>
inductive Step 
  :: "IRGraph \<Rightarrow> (ID \<times> Seen \<times> Conditions \<times> StampFlow) \<Rightarrow> (ID \<times> Seen \<times> Conditions \<times> StampFlow) option \<Rightarrow> bool"
  for g where
  \<comment> \<open>
  Hit a BeginNode with an IfNode predecessor which represents
  the start of a basic block for the IfNode.
     1. nid' will be the successor of the begin node.
     2. Find the first and only predecessor.
     3. Extract condition from the preceding IfNode.
     4. Negate condition if the begin node is second branch
        (we've taken the else branch of the condition)
     5. Add the condition or the negated condition to stack
     6. Perform any stamp updates based on the condition using
        the registerNewCondition function and place them on the
        top of the stack of stamp information
  \<close>
  "\<lbrakk>kind g nid = BeginNode nid';

    nid \<notin> seen;
    seen' = {nid} \<union> seen;

    Some ifcond = pred g nid;
    kind g ifcond = IfNode cond t f;

    i = find_index nid (successors_of (kind g ifcond));
    c = (if i = 0 then kind g cond else LogicNegationNode cond);
    rep g cond ce;
    ce' = (if i = 0 then ce else UnaryExpr UnaryLogicNegation ce);
    conds' = ce' # conds;

    flow' = registerNewCondition g c (hdOr flow (stamp g))\<rbrakk>
   \<Longrightarrow> Step g (nid, seen, conds, flow) (Some (nid', seen', conds', flow' # flow))" |

  \<comment> \<open>
  Hit an EndNode
     1. nid' will be the usage of EndNode
     2. pop the conditions and stamp stack
  \<close>
  "\<lbrakk>kind g nid = EndNode;

    nid \<notin> seen;
    seen' = {nid} \<union> seen;

    nid' = any_usage g nid;

    conds' = tl conds;
    flow' = tl flow\<rbrakk>
   \<Longrightarrow> Step g (nid, seen, conds, flow) (Some (nid', seen', conds', flow'))" |

  \<comment> \<open>We can find a successor edge that is not in seen, go there\<close>
(*nid \<notin> seen;*)
  "\<lbrakk>\<not>(is_EndNode (kind g nid));
    \<not>(is_BeginNode (kind g nid));

    seen' = {nid} \<union> seen;

    Some nid' = nextEdge seen' nid g;
    nid' \<notin> seen'\<rbrakk>
   \<Longrightarrow> Step g (nid, seen, conds, flow) (Some (nid', seen', conds, flow))" |

  \<comment> \<open>We can cannot find a successor edge that is not in seen, give back None\<close>
  "\<lbrakk>\<not>(is_EndNode (kind g nid));
    \<not>(is_BeginNode (kind g nid));

    nid \<notin> seen;
    seen' = {nid} \<union> seen;

    None = nextEdge seen' nid g\<rbrakk>
    \<Longrightarrow> Step g (nid, seen, conds, flow) None" |

  \<comment> \<open>We've already seen this node, give back None\<close>
  "\<lbrakk>nid \<in> seen\<rbrakk> \<Longrightarrow> Step g (nid, seen, conds, flow) None"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) Step .


fun next_nid :: "IRGraph \<Rightarrow> ID set \<Rightarrow> ID \<Rightarrow> ID option" where
  "next_nid g seen nid = (case (kind g nid) of
    (EndNode) \<Rightarrow> Some (any_usage g nid) |
    _ \<Rightarrow> nextEdge seen nid g)"

inductive Step'
  :: "IRGraph \<Rightarrow> (ID \<times> Seen) \<Rightarrow> (ID \<times> Seen) option \<Rightarrow> bool"
  for g where
  \<comment> \<open>We can find a successor edge that is not in seen, go there\<close>
  "\<lbrakk>seen' = {nid} \<union> seen;

    Some nid' = next_nid g seen' nid;
    nid' \<notin> seen'\<rbrakk>
   \<Longrightarrow> Step' g (nid, seen) (Some (nid', seen'))" |

  \<comment> \<open>We can cannot find a successor edge that is not in seen, give back None\<close>
  "\<lbrakk>seen' = {nid} \<union> seen;

    None = next_nid g seen' nid\<rbrakk>
    \<Longrightarrow> Step' g (nid, seen) None" |

  \<comment> \<open>We've already seen this node, give back None\<close>
  "\<lbrakk>seen' = {nid} \<union> seen;

    Some nid' = next_nid g seen' nid;
    nid' \<in> seen'\<rbrakk> \<Longrightarrow> Step' g (nid, seen) None"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) Step' .

values "{x. Step' ConditionalEliminationTest13_testSnippet2_initial (17, {17,11,25,21,18,19,15,12,13,6,29,27,24,23,7,8,0}) x}"


text \<open>
The @{text "ConditionalEliminationPhase"} relation is responsible for combining
the individual traversal steps from the @{text "Step"} relation and the optimizations
from the @{text "ConditionalEliminationStep"} relation to perform a transformation of the
whole graph.
\<close>


inductive ConditionalEliminationPhase 
  :: "(ID \<times> Seen \<times> Conditions \<times> StampFlow \<times> ToVisit) \<Rightarrow> IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool"
  where

  \<comment> \<open>Can do a step and optimise for the current node\<close>
  "\<lbrakk>Step g (nid, seen, conds, flow) (Some (nid', seen', conds', flow'));
    ConditionalEliminationStep (set conds) (hdOr flow (stamp g)) nid g g';
    toVisit' = nid # toVisit;

    ConditionalEliminationPhase (nid', seen', conds', flow', toVisit') g' g''\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhase (nid, seen, conds, flow, toVisit) g g''" |

  \<comment> \<open>Can do a step, matches whether optimised or not causing non-determinism
      We need to find a way to negate ConditionalEliminationStep\<close>
  "\<lbrakk>Step g (nid, seen, conds, flow) (Some (nid', seen', conds', flow'));
    kind g nid = IfNode cid t f;
    g \<turnstile> cid \<simeq> cond;
    condNode = kind g cid;
    conds_implies (set conds) (hdOr flow (stamp g)) condNode cond = None;
    toVisit' = nid # toVisit;
    ConditionalEliminationPhase (nid', seen', conds', flow', toVisit') g g'\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhase (nid, seen, conds, flow, toVisit) g g'" |

  \<comment> \<open>Can't do a step but there is a predecessor we can backtrack to\<close>
(*Some nid' = pred g nid;*)
  "\<lbrakk>Step g (nid, seen, conds, flow) None;
    
    seen' = {nid} \<union> seen;
    toVisit \<noteq> [];
    nid' = hd toVisit;
    toVisit' = tl toVisit;
    ConditionalEliminationPhase (nid', seen', conds, flow, toVisit') g g'\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhase (nid, seen, conds, flow, toVisit) g g'" |

  \<comment> \<open>Can't do a step and have no predecessors so terminate\<close>
(*None = pred g nid*)
  "\<lbrakk>Step g (nid, seen, conds, flow) None;
    toVisit = []\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhase (nid, seen, conds, flow, toVisit) g g"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) ConditionalEliminationPhase . 

inductive ConditionalEliminationPhase' 
  :: "(ID \<times> Seen \<times> ToVisit \<times> DominatorCache) \<Rightarrow> IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool"
  where

  \<comment> \<open>Can do a step and optimise for the current node\<close>
  "\<lbrakk>Step' g (nid, seen) (Some (nid', seen'));
    analyse g c nid (conds, flow, c');
    ConditionalEliminationStep (set conds) (hdOr flow (stamp g)) nid g g';
    toVisit' = nid # toVisit;

    ConditionalEliminationPhase' (nid', seen', toVisit', c') g' g''\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhase' (nid, seen, toVisit, c) g g''" |

  \<comment> \<open>Can do a step, matches whether optimised or not causing non-determinism
      We need to find a way to negate ConditionalEliminationStep\<close>
  "\<lbrakk>Step' g (nid, seen) (Some (nid', seen'));
    analyse g c nid (conds, flow, c');
    kind g nid = IfNode cid t f;
    g \<turnstile> cid \<simeq> cond;
    condNode = kind g cid;
    conds_implies (set conds) (hdOr flow (stamp g)) condNode cond = None;
    toVisit' = nid # toVisit;
    ConditionalEliminationPhase' (nid', seen', toVisit', c') g g'\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhase' (nid, seen, toVisit, c) g g'" |

  \<comment> \<open>Can't do a step but there is a predecessor we can backtrack to\<close>
(*Some nid' = pred g nid;*)
  "\<lbrakk>Step' g (nid, seen) None;
    
    seen' = {nid} \<union> seen;
    toVisit = nid' # toVisit';
    ConditionalEliminationPhase' (nid', seen', toVisit', c) g g'\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhase' (nid, seen, toVisit, c) g g'" |

  \<comment> \<open>Can't do a step and have no predecessors so terminate\<close>
(*None = pred g nid*)
  "\<lbrakk>Step' g (nid, seen) None;
    toVisit = []\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhase' (nid, seen, toVisit, c) g g"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) ConditionalEliminationPhase' . 

definition runConditionalElimination :: "IRGraph \<Rightarrow> IRGraph" where
  "runConditionalElimination g = 
    (Predicate.the (ConditionalEliminationPhase'_i_i_o (0, {}, ([], Map.empty)) g))"

inductive ConditionalEliminationPhaseWithTrace\<^marker>\<open>tag invisible\<close>
  :: "IRGraph \<Rightarrow> (ID \<times> Seen \<times> Conditions \<times> StampFlow) \<Rightarrow> ID list \<Rightarrow> IRGraph \<Rightarrow> ID list \<Rightarrow> Conditions \<Rightarrow> bool" where\<^marker>\<open>tag invisible\<close>

  (* Can do a step and optimise for the current nid *)
  "\<lbrakk>Step g (nid, seen, conds, flow) (Some (nid', seen', conds', flow'));
    ConditionalEliminationStep (set conds) (hdOr flow (stamp g)) nid g g';
    
    ConditionalEliminationPhaseWithTrace g' (nid', seen', conds', flow') (nid # t) g'' t' conds''\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhaseWithTrace g (nid, seen, conds, flow) t g'' t' conds''" |

  (* Can do a step, matches whether optimised or not causing non-determinism
     Need to find a way to negate ConditionalEliminationStep *)
  "\<lbrakk>Step g (nid, seen, conds, flow) (Some (nid', seen', conds', flow'));
    
    ConditionalEliminationPhaseWithTrace g (nid', seen', conds', flow') (nid # t) g' t' conds''\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhaseWithTrace g (nid, seen, conds, flow) t g' t' conds''" |

  (* Can't do a step but there is a predecessor we can backtrace to *)
  "\<lbrakk>Step g (nid, seen, conds, flow) None;
    Some nid' = pred g nid;
    seen' = {nid} \<union> seen;
    ConditionalEliminationPhaseWithTrace g (nid', seen', conds, flow) (nid # t) g' t' conds'\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhaseWithTrace g (nid, seen, conds, flow) t g' t' conds'" |

  (* Can't do a step and have no predecessors do terminate *)
  "\<lbrakk>Step g (nid, seen, conds, flow) None;
    None = pred g nid\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhaseWithTrace g (nid, seen, conds, flow) t g (nid # t) conds"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool) ConditionalEliminationPhaseWithTrace .

(*

lemma IfNodeStepE: "g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h) \<Longrightarrow>
  (\<And>cond tb fb val.
        kind g nid = IfNode cond tb fb \<Longrightarrow>
        nid' = (if val_to_bool val then tb else fb) \<Longrightarrow> 
        [g, m, p] \<turnstile> kind g cond \<mapsto> val \<Longrightarrow> m' = m)"
  using StepE
  by (smt (verit, best) IfNode Pair_inject stepDet)

lemma ifNodeHasCondEvalStutter:
  assumes "(g m p h \<turnstile> nid \<leadsto> nid')"
  assumes "kind g nid = IfNode cond t f"
  shows "\<exists> v. ([g, m, p] \<turnstile> kind g cond \<mapsto> v)"
  using IfNodeStepE assms(1) assms(2)  stutter.cases
  by (meson IfNodeCond)

lemma ifNodeHasCondEval:
  assumes "(g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h'))"
  assumes "kind g nid = IfNode cond t f"
  shows "\<exists> v. ([g, m, p] \<turnstile> kind g cond \<mapsto> v)"
  using IfNodeStepE assms(1) assms(2)
  by (smt (z3) IRNode.disc(932) IRNode.simps(938) IRNode.simps(958) IRNode.simps(972) IRNode.simps(974) IRNode.simps(978) Pair_inject StutterStep ifNodeHasCondEvalStutter is_AbstractEndNode.simps is_EndNode.simps(12) step.cases)


lemma replace_if_t:
  assumes "kind g nid = IfNode cond tb fb"
  assumes "[g, m, p] \<turnstile> kind g cond \<mapsto> bool"
  assumes "val_to_bool bool"
  assumes g': "g' = replace_usages nid tb g"
  shows "\<exists>nid' .(g m p h \<turnstile> nid \<leadsto> nid') \<longleftrightarrow> (g' m p h \<turnstile> nid \<leadsto> nid')"
proof -
  have g1step: "g, p \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    by (meson IfNode assms(1) assms(2) assms(3))
  have g2step: "g', p \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    using g' unfolding replace_usages.simps
    by (simp add: stepRefNode)
  from g1step g2step show ?thesis
    using StutterStep by blast
qed

lemma replace_if_t_imp:
  assumes "kind g nid = IfNode cond tb fb"
  assumes "[g, m, p] \<turnstile> kind g cond \<mapsto> bool"
  assumes "val_to_bool bool"
  assumes g': "g' = replace_usages nid tb g"
  shows "\<exists>nid' .(g m p h \<turnstile> nid \<leadsto> nid') \<longrightarrow> (g' m p h \<turnstile> nid \<leadsto> nid')"
  using replace_if_t assms by blast

lemma replace_if_f:
  assumes "kind g nid = IfNode cond tb fb"
  assumes "[g, m, p] \<turnstile> kind g cond \<mapsto> bool"
  assumes "\<not>(val_to_bool bool)"
  assumes g': "g' = replace_usages nid fb g"
  shows "\<exists>nid' .(g m p h \<turnstile> nid \<leadsto> nid') \<longleftrightarrow> (g' m p h \<turnstile> nid \<leadsto> nid')"
proof -
  have g1step: "g, p \<turnstile> (nid, m, h) \<rightarrow> (fb, m, h)"
    by (meson IfNode assms(1) assms(2) assms(3))
  have g2step: "g', p \<turnstile> (nid, m, h) \<rightarrow> (fb, m, h)"
    using g' unfolding replace_usages.simps
    by (simp add: stepRefNode)
  from g1step g2step show ?thesis
    using StutterStep by blast
qed

text \<open>
Prove that the individual conditional elimination rules are correct
with respect to preservation of stuttering steps.
\<close>
lemma ConditionalEliminationStepProof:
  assumes wg: "wf_graph g"
  assumes ws: "wf_stamps g"
  assumes wv: "wf_values g"
  assumes nid: "nid \<in> ids g"
  assumes conds_valid: "\<forall> c \<in> conds . \<exists> v. ([g, m, p] \<turnstile> c \<mapsto> v) \<and> val_to_bool v"
  assumes ce: "ConditionalEliminationStep conds stamps g nid g'"

  shows "\<exists>nid' .(g m p h \<turnstile> nid \<leadsto> nid') \<longrightarrow> (g' m p h \<turnstile> nid \<leadsto> nid')"
  using ce using assms
proof (induct g nid g' rule: ConditionalEliminationStep.induct)
  case (impliesTrue g ifcond cid t f cond conds g')
  show ?case proof (cases "(g m p h \<turnstile> ifcond \<leadsto> nid')")
    case True
    obtain condv where condv: "[g, m, p] \<turnstile> kind g cid \<mapsto> condv"
      using implies.simps impliesTrue.hyps(3) impliesTrue.prems(4)
      using impliesTrue.hyps(2) True
      by (metis ifNodeHasCondEvalStutter impliesTrue.hyps(1))
    have condvTrue: "val_to_bool condv"
      by (metis condition_implies.intros(2) condv impliesTrue.hyps(2) impliesTrue.hyps(3) impliesTrue.prems(1) impliesTrue.prems(3) impliesTrue.prems(5) implies_true_valid)
    then show ?thesis
      using constantConditionValid 
      using impliesTrue.hyps(1) condv impliesTrue.hyps(4)
      by blast
  next
    case False
    then show ?thesis by auto
  qed
next
  case (impliesFalse g ifcond cid t f cond conds g')
  then show ?case 
  proof (cases "(g m p h \<turnstile> ifcond \<leadsto> nid')")
    case True
    obtain condv where condv: "[g, m, p] \<turnstile> kind g cid \<mapsto> condv"
      using ifNodeHasCondEvalStutter impliesFalse.hyps(1)
      using True by blast
    have condvFalse: "False = val_to_bool condv"
      by (metis condition_implies.intros(2) condv impliesFalse.hyps(2) impliesFalse.hyps(3) impliesFalse.prems(1) impliesFalse.prems(3) impliesFalse.prems(5) implies_false_valid)
    then show ?thesis
      using constantConditionValid 
      using impliesFalse.hyps(1) condv impliesFalse.hyps(4)
      by blast
  next
    case False
    then show ?thesis
      by auto
  qed
next
  case (tryFoldTrue g ifcond cid t f cond g' conds)
  then show ?case using constantConditionValid tryFoldProofTrue
    using StutterStep constantConditionTrue by metis
next
  case (tryFoldFalse g ifcond cid t f cond g' conds)
  then show ?case using constantConditionValid tryFoldProofFalse
    using StutterStep constantConditionFalse by metis
qed


text \<open>
Prove that the individual conditional elimination rules are correct
with respect to finding a bisimulation between the unoptimized and optimized graphs.
\<close>
lemma ConditionalEliminationStepProofBisimulation:
  assumes wf: "wf_graph g \<and> wf_stamp g stamps \<and> wf_values g"
  assumes nid: "nid \<in> ids g"
  assumes conds_valid: "\<forall> c \<in> conds . \<exists> v. ([g, m, p] \<turnstile> c \<mapsto> v) \<and> val_to_bool v"
  assumes ce: "ConditionalEliminationStep conds stamps g nid g'"
  assumes gstep: "\<exists> h nid'. (g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h))" (* we don't yet consider optimizations which produce a step that didn't already exist *)

  shows "nid | g \<sim> g'"
  using ce gstep using assms
proof (induct g nid g' rule: ConditionalEliminationStep.induct)
  case (impliesTrue g ifcond cid t f cond conds g' stamps)
  from impliesTrue(5) obtain h where gstep: "g, p \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
    by (metis IfNode StutterStep condition_implies.intros(2) ifNodeHasCondEvalStutter impliesTrue.hyps(1) impliesTrue.hyps(2) impliesTrue.hyps(3) impliesTrue.prems(2) impliesTrue.prems(4) implies_true_valid)
  have "g', p \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
    using constantConditionTrue impliesTrue.hyps(1) impliesTrue.hyps(4) by blast
  then show ?case using gstep
    by (metis stepDet strong_noop_bisimilar.intros)
next
  case (impliesFalse g ifcond cid t f cond conds g' stamps)
  from impliesFalse(5) obtain h where gstep: "g, p \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
    by (metis IfNode condition_implies.intros(2) ifNodeHasCondEval impliesFalse.hyps(1) impliesFalse.hyps(2) impliesFalse.hyps(3) impliesFalse.prems(2) impliesFalse.prems(4) implies_false_valid)
  have "g', p \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
    using constantConditionFalse impliesFalse.hyps(1) impliesFalse.hyps(4) by blast
  then show ?case using gstep
    by (metis stepDet strong_noop_bisimilar.intros)
next
  case (tryFoldTrue g ifcond cid t f cond stamps g' conds)
  from tryFoldTrue(5) obtain val where "[g, m, p] \<turnstile> kind g cid \<mapsto> val"
    using ifNodeHasCondEval tryFoldTrue.hyps(1) by blast
  then have "val_to_bool val"
    using tryFoldProofTrue tryFoldTrue.prems(2) tryFoldTrue(3) 
    by blast
  then obtain h where gstep: "g, p \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
    using tryFoldTrue(5)
    by (meson IfNode \<open>[g, m, p] \<turnstile> kind g cid \<mapsto> val\<close> tryFoldTrue.hyps(1))
  have "g', p \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
    using constantConditionTrue tryFoldTrue.hyps(1) tryFoldTrue.hyps(4) by presburger
  then show ?case using gstep
    by (metis stepDet strong_noop_bisimilar.intros)
next
  case (tryFoldFalse g ifcond cid t f cond stamps g' conds)
  from tryFoldFalse(5) obtain h where gstep: "g, p \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
    by (meson IfNode ifNodeHasCondEval tryFoldFalse.hyps(1) tryFoldFalse.hyps(3) tryFoldFalse.prems(2) tryFoldProofFalse)
  have "g', p \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
    using constantConditionFalse tryFoldFalse.hyps(1) tryFoldFalse.hyps(4) by blast
  then show ?case using gstep
    by (metis stepDet strong_noop_bisimilar.intros)
qed


text \<open>Mostly experimental proofs from here on out.\<close>

experiment begin
lemma if_step:
  assumes "nid \<in> ids g"
  assumes "(kind g nid) \<in> control_nodes"
  shows "(g m p h \<turnstile> nid \<leadsto> nid')"
  using assms apply (cases "kind g nid") sorry

lemma StepConditionsValid:
  assumes "\<forall> cond \<in> set conds. ([g, m, p] \<turnstile> cond \<mapsto> v) \<and> val_to_bool v"
  assumes "Step g (nid, seen, conds, flow) (Some (nid', seen', conds', flow'))"
  shows "\<forall> cond \<in> set conds'. ([g, m, p] \<turnstile> cond \<mapsto> v) \<and> val_to_bool v"
  using assms(2) 
proof (induction "(nid, seen, conds, flow)" "Some (nid', seen', conds', flow')" rule: Step.induct)
  case (1 ifcond cond t f i c)
  obtain cv where cv: "[g, m, p] \<turnstile> c \<mapsto> cv"
    sorry
  have cvt: "val_to_bool cv"
    sorry
  have "set conds' = {c} \<union> set conds"
    using "1.hyps"(8) by auto
  then show ?case using cv cvt assms(1) sorry
next
  case (2)
  from 2(5) have "set conds' \<subseteq> set conds"
    by (metis list.sel(2) list.set_sel(2) subsetI)
  then show ?case using assms(1)
    by blast
next
case (3)
  then show ?case
    using assms(1) by force
qed

lemma ConditionalEliminationPhaseProof:
  assumes "wf_graph g"
  assumes "wf_stamps g"
  assumes "ConditionalEliminationPhase g (0, {}, [], []) g'"
  
  shows "\<exists>nid' .(g m p h \<turnstile> 0 \<leadsto> nid') \<longrightarrow> (g' m p h \<turnstile> 0 \<leadsto> nid')"
proof -
  have "0 \<in> ids g"
    using assms(1) wf_folds by blast
  show ?thesis
using assms(3) assms proof (induct rule: ConditionalEliminationPhase.induct)
case (1 g nid g' succs nid' g'')
  then show ?case sorry
next
  case (2 succs g nid nid' g'')
  then show ?case sorry
next
  case (3 succs g nid)
  then show ?case 
    by simp
next
  case (4)
  then show ?case sorry
qed
qed
end
*)

end