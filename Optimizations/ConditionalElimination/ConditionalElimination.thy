section \<open>Conditional Elimination Phase\<close>

text \<open>
This theory presents the specification of the \texttt{ConditionalElimination} phase
within the GraalVM compiler.
The \texttt{ConditionalElimination} phase simplifies any condition of an \textsl{if}
statement that can be implied by the conditions that dominate it.
Such that if condition A implies that condition B \textsl{must} be true,
the condition B is simplified to \texttt{true}.

\begin{lstlisting}[language=java]
if (A) {
  if (B) {
    ...
  }
}
\end{lstlisting}

We begin by defining the individual implication rules used by the phase
in \ref{sec:rules}.
These rules are then lifted to the rewriting of a condition within an \textsl{if}
statement in \ref{sec:lift}.
The traversal algorithm used by the compiler is specified in \ref{sec:traversal}.
\<close>

theory ConditionalElimination
  imports
    Semantics.IRTreeEvalThms
    Proofs.Rewrites
    Proofs.Bisimulation
    OptimizationDSL.Markup
begin

declare [[show_types=false]]

subsection \<open>Implication Rules \label{sec:rules}\<close>

text \<open>
The set of rules used for determining whether a condition, @{term q\<^sub>1},
 implies another condition, @{term q\<^sub>2}, must be true or false.
\<close>

subsubsection \<open>Structural Implication\<close>

text \<open>
The first method for determining if a condition can be implied by another condition,
is structural implication.
That is, by looking at the structure of the conditions, we can determine the truth value.
For instance, @{term "x == y"} implies that @{term "x < y"} cannot be true.
\<close>

inductive 
  impliesx :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" ("_ \<Rrightarrow> _") and 
  impliesnot :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" ("_ \<Rrightarrow>\<not> _") where
  same:          "q \<Rrightarrow> q" |
  eq_not_less:   "exp[x eq y] \<Rrightarrow>\<not> exp[x < y]" |
  eq_not_less':  "exp[x eq y] \<Rrightarrow>\<not> exp[y < x]" |
  less_not_less: "exp[x < y] \<Rrightarrow>\<not> exp[y < x]" |
  less_not_eq:   "exp[x < y] \<Rrightarrow>\<not> exp[x eq y]" |
  less_not_eq':  "exp[x < y] \<Rrightarrow>\<not> exp[y eq x]" |
  negate_true:   "\<lbrakk>x \<Rrightarrow>\<not> y\<rbrakk> \<Longrightarrow> x \<Rrightarrow> exp[!y]" |
  negate_false:  "\<lbrakk>x \<Rrightarrow> y\<rbrakk> \<Longrightarrow> x \<Rrightarrow>\<not> exp[!y]"

inductive implies_complete :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool option \<Rightarrow> bool" where
  implies:
  "x \<Rrightarrow> y \<Longrightarrow> implies_complete x y (Some True)" |
  impliesnot:
  "x \<Rrightarrow>\<not> y \<Longrightarrow> implies_complete x y (Some False)" |
  fail:
  "\<not>((x \<Rrightarrow> y) \<or> (x \<Rrightarrow>\<not> y)) \<Longrightarrow> implies_complete x y None"


text \<open>
The relation @{term "q\<^sub>1 \<Rrightarrow> q\<^sub>2"} requires that the implication @{term "q\<^sub>1 \<longrightarrow> q\<^sub>2"}
is known true (i.e. universally valid).
The relation @{term "q\<^sub>1 \<Rrightarrow>\<not> q\<^sub>2"} requires that the implication @{term "q\<^sub>1 \<longrightarrow> q\<^sub>2"}
is known false (i.e. @{term "q1 \<longrightarrow>\<not> q2"} is universally valid).
If neither @{term "q\<^sub>1 \<Rrightarrow> q\<^sub>2"} nor @{term "q\<^sub>1 \<Rrightarrow>\<not> q\<^sub>2"} then the status is unknown
and the condition cannot be simplified.
\<close>

fun implies_valid :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" (infix "\<Zinj>" 50) where
  "implies_valid q1 q2 = 
    (\<forall>m p v1 v2. ([m, p] \<turnstile> q1 \<mapsto> v1) \<and> ([m,p] \<turnstile> q2 \<mapsto> v2) \<longrightarrow> 
            (val_to_bool v1 \<longrightarrow> val_to_bool v2))"

fun impliesnot_valid :: "IRExpr \<Rightarrow> IRExpr \<Rightarrow> bool" (infix "\<Zpinj>" 50) where
  "impliesnot_valid q1 q2 = 
    (\<forall>m p v1 v2. ([m, p] \<turnstile> q1 \<mapsto> v1) \<and> ([m,p] \<turnstile> q2 \<mapsto> v2) \<longrightarrow> 
            (val_to_bool v1 \<longrightarrow> \<not>val_to_bool v2))"

text \<open>
The relation @{term "q\<^sub>1 \<Zinj> q\<^sub>2"} means @{term "q\<^sub>1 \<longrightarrow> q\<^sub>2"} is universally valid, 
and the relation @{term "q\<^sub>1 \<Zpinj> q\<^sub>2"} means @{term "q\<^sub>1 \<longrightarrow> \<not>q\<^sub>2"} is universally valid.
\<close>

lemma eq_not_less_val:
  "val_to_bool(val[v1 eq v2]) \<longrightarrow> \<not>val_to_bool(val[v1 < v2])"
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

lemma eq_not_less'_val:
  "val_to_bool(val[v1 eq v2]) \<longrightarrow> \<not>val_to_bool(val[v2 < v1])"
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
    using a eq_not_less_val by presburger
qed

lemma less_not_less_val:
  "val_to_bool(val[v1 < v2]) \<longrightarrow> \<not>val_to_bool(val[v2 < v1])"
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

lemma less_not_eq_val:
  "val_to_bool(val[v1 < v2]) \<longrightarrow> \<not>val_to_bool(val[v1 eq v2])"
  using eq_not_less_val by blast 

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

text \<open>The following theorem show that the known true/false rules are valid.\<close>

theorem implies_impliesnot_valid:
  shows "((q1 \<Rrightarrow> q2) \<longrightarrow> (q1 \<Zinj> q2)) \<and>
         ((q1 \<Rrightarrow>\<not> q2) \<longrightarrow> (q1 \<Zpinj> q2))"
          (is "(?imp \<longrightarrow> ?val) \<and> (?notimp \<longrightarrow> ?notval)")
proof (induct q1 q2  rule: impliesx_impliesnot.induct)
  case (same q)
  then show ?case 
    using evalDet by fastforce
next
  case (eq_not_less x y)
  then show ?case apply auto[1] using eq_not_less_val evalDet by blast
next
  case (eq_not_less' x y)
  then show ?case apply auto[1] using eq_not_less'_val evalDet by blast
next
  case (less_not_less x y)
  then show ?case apply auto[1] using less_not_less_val evalDet by blast
next
  case (less_not_eq x y)
  then show ?case apply auto[1] using less_not_eq_val evalDet by blast
next
  case (less_not_eq' x y)
  then show ?case apply auto[1] using eq_not_less'_val evalDet by metis
next
  case (negate_true x y)
  then show ?case apply auto[1]
    by (metis logic_negation_relation_tree unary_eval.simps(4) unfold_unary)
next
  case (negate_false x y)
  then show ?case apply auto[1]
    by (metis UnaryExpr logic_negation_relation_tree unary_eval.simps(4)) 
qed


subsubsection \<open>Type Implication\<close>

text \<open>
The second mechanism to determine whether a condition implies another is
to use the type information of the relevant nodes.
For instance, @{term "x < 4"} implies @{term "x < 10"}.
We can show this by strengthening the type, stamp,
of the node @{term x} such that the upper bound is @{term 4}.
Then we the second condition is reached,
we know that the condition must be true by the upperbound.
\<close>

text \<open>
The following relation corresponds to the \texttt{UnaryOpLogicNode.tryFold}
and \texttt{BinaryOpLogicNode.tryFold} methods and their associated
concrete implementations.

We track the refined stamps by mapping nodes to Stamps,
the second parameter to @{term tryFold}.
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

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool) tryFold .

text \<open>
Prove that, when the stamp map is valid,
the @{term tryFold} relation correctly predicts the output value with respect to
our evaluation semantics.
\<close>

inductive_cases StepE:
  "g, p \<turnstile> (nid,m,h) \<rightarrow> (nid',m',h)"


lemma is_stamp_empty_valid:
  assumes "is_stamp_empty s"
  shows "\<not>(\<exists> val. valid_value val s)"
  using assms is_stamp_empty.simps apply (cases s; auto)
  by (metis linorder_not_le not_less_iff_gr_or_eq order.strict_trans valid_value.elims(2) valid_value.simps(1) valid_value.simps(5))

lemma join_valid:
  assumes "is_IntegerStamp s1 \<and> is_IntegerStamp s2"
  assumes "valid_stamp s1 \<and> valid_stamp s2"
  shows "(valid_value v s1 \<and> valid_value v s2) = valid_value v (join s1 s2)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs 
   using assms(1) apply (cases s1; cases s2; auto)
   apply (metis Value.inject(1) valid_int)
  by (smt (z3) valid_int valid_stamp.simps(1) valid_value.simps(1))
  next
  assume ?rhs
  then show ?lhs
    using assms apply (cases s1; cases s2; simp)
  by (smt (verit, best) assms(2) valid_int valid_value.simps(1) valid_value.simps(22))
qed

lemma alwaysDistinct_evaluate:
  assumes "wf_stamp g stamps"
  assumes "alwaysDistinct (stamps x) (stamps y)"
  assumes "is_IntegerStamp (stamps x) \<and> is_IntegerStamp (stamps y) \<and> valid_stamp (stamps x) \<and> valid_stamp (stamps y)"
  shows "\<not>(\<exists> val . ([g, m, p] \<turnstile> x \<mapsto> val) \<and> ([g, m, p] \<turnstile> y \<mapsto> val))"
proof -
  obtain stampx stampy where stampdef: "stampx = stamps x \<and> stampy = stamps y"
    by simp
  then have xv: "\<forall> xv . ([g, m, p] \<turnstile> x \<mapsto> xv) \<longrightarrow> valid_value xv stampx"
    by (meson assms(1) encodeeval.simps eval_in_ids wf_stamp.elims(2))
  from stampdef have yv: "\<forall> yv . ([g, m, p] \<turnstile> y \<mapsto> yv) \<longrightarrow> valid_value yv stampy"
    by (meson assms(1) encodeeval.simps eval_in_ids wf_stamp.elims(2))
  have "\<forall>v. valid_value v (join stampx stampy) = (valid_value v stampx \<and> valid_value v stampy)"
    using assms(3)
    by (simp add: join_valid stampdef)
  then show ?thesis
    using assms unfolding alwaysDistinct.simps
    using is_stamp_empty_valid stampdef xv yv by blast
qed

lemma alwaysDistinct_valid:
  assumes "wf_stamp g stamps"
  assumes "kind g nid = (IntegerEqualsNode x y)"
  assumes "[g, m, p] \<turnstile> nid \<mapsto> v"
  assumes "alwaysDistinct (stamps x) (stamps y)"
  shows "\<not>(val_to_bool v)"
proof -
  have no_valid: "\<forall> val. \<not>(valid_value val (join (stamps x) (stamps y)))"
    by (smt (verit, best) is_stamp_empty.elims(2) valid_int valid_value.simps(1) assms(1,4)
        alwaysDistinct.simps)
  obtain xe ye where repr: "rep g nid (BinaryExpr BinIntegerEquals xe ye)"
    by (metis assms(2) assms(3) encodeeval.simps rep_integer_equals)
  moreover have evale: "[m, p] \<turnstile> (BinaryExpr BinIntegerEquals xe ye) \<mapsto> v"
    by (metis assms(3) calculation encodeeval.simps repDet)
  moreover have repsub: "rep g x xe \<and> rep g y ye"
    by (metis IRNode.distinct(1955) IRNode.distinct(1997) IRNode.inject(17) IntegerEqualsNodeE assms(2) calculation)
  ultimately obtain xv yv where evalsub: "[g, m, p] \<turnstile> x \<mapsto> xv \<and> [g, m, p] \<turnstile> y \<mapsto> yv"
    by (meson BinaryExprE encodeeval.simps)
  have xvalid: "valid_value xv (stamps x)"
    using assms(1) encode_in_ids encodeeval.simps evalsub wf_stamp.simps by blast
  then have xint: "is_IntegerStamp (stamps x)"
    using assms(4) valid_value.elims(2) by fastforce
  then have xstamp: "valid_stamp (stamps x)"
    using xvalid apply (cases xv; auto) 
    apply (smt (z3) valid_stamp.simps(6) valid_value.elims(1))
    using is_IntegerStamp_def by fastforce
  have yvalid: "valid_value yv (stamps y)"
    using assms(1) encode_in_ids encodeeval.simps evalsub wf_stamp.simps by blast
  then have yint: "is_IntegerStamp (stamps y)"
    using assms(4) valid_value.elims(2) by fastforce
  then have ystamp: "valid_stamp (stamps y)"
    using yvalid apply (cases yv; auto) 
    apply (smt (z3) valid_stamp.simps(6) valid_value.elims(1))
    using is_IntegerStamp_def by fastforce
  have disjoint: "\<not>(\<exists> val . ([g, m, p] \<turnstile> x \<mapsto> val) \<and> ([g, m, p] \<turnstile> y \<mapsto> val))"
    using alwaysDistinct_evaluate
    using assms(1) assms(4) xint yint xvalid yvalid xstamp ystamp by simp
  have "v = bin_eval BinIntegerEquals xv yv"
    by (metis BinaryExprE encodeeval.simps evale evalsub graphDet repsub)
  also have "v \<noteq> UndefVal"
    using evale by auto
  ultimately have "\<exists>b1 b2. v =  bool_to_val_bin b1 b2 (xv = yv)"
    unfolding bin_eval.simps
    by (smt (z3) Value.inject(1) bool_to_val_bin.simps intval_equals.elims)
  then show ?thesis
    by (metis (mono_tags, lifting) \<open>(v::Value) \<noteq> UndefVal\<close> bool_to_val.elims bool_to_val_bin.simps disjoint evalsub val_to_bool.simps(1))
qed
thm_oracles alwaysDistinct_valid

lemma unwrap_valid:
  assumes "0 < b \<and> b \<le> 64"
  assumes "take_bit (b::nat) (vv::64 word) = vv"
  shows "(vv::64 word) = take_bit b (word_of_int (int_signed_value (b::nat) (vv::64 word)))"
  using assms apply auto[1]
  by (simp add: take_bit_signed_take_bit)

lemma asConstant_valid:
  assumes "asConstant s = val"
  assumes "val \<noteq> UndefVal"
  assumes "valid_value v s"
  shows "v = val"
proof -
  obtain b l h where s: "s = IntegerStamp b l h"
    using assms(1,2) by (cases s; auto)
  obtain vv where vdef: "v = IntVal b vv"
    using assms(3) s valid_int by blast
  have "l \<le> int_signed_value b vv \<and> int_signed_value b vv \<le> h"
    by (metis \<open>(v::Value) = IntVal (b::nat) (vv::64 word)\<close> assms(3) s valid_value.simps(1))
  then have veq: "int_signed_value b vv = l"
    by (smt (verit) asConstant.simps(1) assms(1) assms(2) s)
  have valdef: "val = new_int b (word_of_int l)"
    by (metis asConstant.simps(1) assms(1) assms(2) s)
  have "take_bit b vv = vv"
    by (metis \<open>(v::Value) = IntVal (b::nat) (vv::64 word)\<close> assms(3) s valid_value.simps(1))
  then show ?thesis
    using veq vdef valdef
    using assms(3) s unwrap_valid by force
qed

lemma neverDistinct_valid:
  assumes "wf_stamp g stamps"
  assumes "kind g nid = (IntegerEqualsNode x y)"
  assumes "[g, m, p] \<turnstile> nid \<mapsto> v"
  assumes "neverDistinct (stamps x) (stamps y)"
  shows "val_to_bool v"
proof -
  obtain val where constx: "asConstant (stamps x) = val"
    by simp
  moreover have "val \<noteq> UndefVal"
    using assms(4) calculation by auto
  then have constx: "val = asConstant (stamps y)"
    using calculation assms(4) by force
  obtain xe ye where repr: "rep g nid (BinaryExpr BinIntegerEquals xe ye)"
    by (metis assms(2) assms(3) encodeeval.simps rep_integer_equals)
  moreover have evale: "[m, p] \<turnstile> (BinaryExpr BinIntegerEquals xe ye) \<mapsto> v"
    by (metis assms(3) calculation encodeeval.simps repDet)
  moreover have repsub: "rep g x xe \<and> rep g y ye"
    by (metis IRNode.distinct(1955) IRNode.distinct(1997) IRNode.inject(17) IntegerEqualsNodeE assms(2) calculation)
  ultimately obtain xv yv where evalsub: "[g, m, p] \<turnstile> x \<mapsto> xv \<and> [g, m, p] \<turnstile> y \<mapsto> yv"
    by (meson BinaryExprE encodeeval.simps)
  have xvalid: "valid_value xv (stamps x)"
    using assms(1) encode_in_ids encodeeval.simps evalsub wf_stamp.simps by blast
  then have xint: "is_IntegerStamp (stamps x)"
    using assms(4) valid_value.elims(2) by fastforce
  have yvalid: "valid_value yv (stamps y)"
    using assms(1) encode_in_ids encodeeval.simps evalsub wf_stamp.simps by blast
  then have yint: "is_IntegerStamp (stamps y)"
    using assms(4) valid_value.elims(2) by fastforce
  have eq: "\<forall>v1 v2. (([g, m, p] \<turnstile> x \<mapsto> v1) \<and> ([g, m, p] \<turnstile> y \<mapsto> v2)) \<longrightarrow> v1 = v2"
    by (metis asConstant_valid assms(4) encodeEvalDet evalsub neverDistinct.elims(1) xvalid yvalid)
  have "v = bin_eval BinIntegerEquals xv yv"
    by (metis BinaryExprE encodeeval.simps evale evalsub graphDet repsub)
  also have "v \<noteq> UndefVal"
    using evale by auto
  ultimately have "\<exists>b1 b2. v =  bool_to_val_bin b1 b2 (xv = yv)"
    unfolding bin_eval.simps
    by (smt (z3) Value.inject(1) bool_to_val_bin.simps intval_equals.elims)
  then show ?thesis
    using \<open>(v::Value) \<noteq> UndefVal\<close> eq evalsub by fastforce
qed

lemma stampUnder_valid:
  assumes "wf_stamp g stamps"
  assumes "kind g nid = (IntegerLessThanNode x y)"
  assumes "[g, m, p] \<turnstile> nid \<mapsto> v"
  assumes "stpi_upper (stamps x) < stpi_lower (stamps y)"
  shows "val_to_bool v"
proof -
  obtain xe ye where repr: "rep g nid (BinaryExpr BinIntegerLessThan xe ye)"
    by (metis assms(2) assms(3) encodeeval.simps rep_integer_less_than)
  moreover have evale: "[m, p] \<turnstile> (BinaryExpr BinIntegerLessThan xe ye) \<mapsto> v"
    by (metis assms(3) calculation encodeeval.simps repDet)
  moreover have repsub: "rep g x xe \<and> rep g y ye"
    by (metis IRNode.distinct(2047) IRNode.distinct(2089) IRNode.inject(18) IntegerLessThanNodeE assms(2) repr)
  ultimately obtain xv yv where evalsub: "[g, m, p] \<turnstile> x \<mapsto> xv \<and> [g, m, p] \<turnstile> y \<mapsto> yv"
    by (meson BinaryExprE encodeeval.simps)
  have vval: "v = intval_less_than xv yv"
    by (metis BinaryExprE bin_eval.simps(14) encodeEvalDet encodeeval.simps evale evalsub repsub)
  then obtain b xvv where "xv = IntVal b xvv"
    by (metis bin_eval.simps(14) defined_eval_is_intval evale evaltree_not_undef is_IntVal_def)
  also have xvalid: "valid_value xv (stamps x)"
    by (meson assms(1) encodeeval.simps eval_in_ids evalsub wf_stamp.elims(2))
  then obtain xl xh where xstamp: "stamps x = IntegerStamp b xl xh"
    using calculation valid_value.simps apply (cases "stamps x"; auto)
    by presburger
  from vval obtain yvv where yint: "yv = IntVal b yvv"
    by (metis Value.collapse(1) bin_eval.simps(14) bool_to_val_bin.simps calculation defined_eval_is_intval evale evaltree_not_undef intval_less_than.simps(1))
  then have yvalid: "valid_value yv (stamps y)"
    using assms(1) encodeeval.simps evalsub no_encoding wf_stamp.simps by blast
  then obtain yl yh where ystamp: "stamps y = IntegerStamp b yl yh"
    using calculation yint valid_value.simps apply (cases "stamps y"; auto)
    by presburger
  have "int_signed_value b xvv \<le> xh"
    using calculation valid_value.simps(1) xstamp xvalid by presburger
  moreover have "yl \<le> int_signed_value b yvv"
    using valid_value.simps(1) yint ystamp yvalid by presburger
  moreover have "xh < yl"
    using assms(4) xstamp ystamp by auto
  ultimately have "int_signed_value b xvv < int_signed_value b yvv"
    by linarith
  then have "val_to_bool (intval_less_than xv yv)"
    by (simp add: \<open>(xv::Value) = IntVal (b::nat) (xvv::64 word)\<close> yint)
  then show ?thesis
    by (simp add: vval)
qed

lemma stampOver_valid:
  assumes "wf_stamp g stamps"
  assumes "kind g nid = (IntegerLessThanNode x y)"
  assumes "[g, m, p] \<turnstile> nid \<mapsto> v"
  assumes "stpi_lower (stamps x) \<ge> stpi_upper (stamps y)"
  shows "\<not>(val_to_bool v)"
proof -
  obtain xe ye where repr: "rep g nid (BinaryExpr BinIntegerLessThan xe ye)"
    by (metis assms(2) assms(3) encodeeval.simps rep_integer_less_than)
  moreover have evale: "[m, p] \<turnstile> (BinaryExpr BinIntegerLessThan xe ye) \<mapsto> v"
    by (metis assms(3) calculation encodeeval.simps repDet)
  moreover have repsub: "rep g x xe \<and> rep g y ye"
    by (metis IRNode.distinct(2047) IRNode.distinct(2089) IRNode.inject(18) IntegerLessThanNodeE assms(2) repr)
  ultimately obtain xv yv where evalsub: "[g, m, p] \<turnstile> x \<mapsto> xv \<and> [g, m, p] \<turnstile> y \<mapsto> yv"
    by (meson BinaryExprE encodeeval.simps)
  have vval: "v = intval_less_than xv yv"
    by (metis BinaryExprE bin_eval.simps(14) encodeEvalDet encodeeval.simps evale evalsub repsub)
  then obtain b xvv where "xv = IntVal b xvv"
    by (metis bin_eval.simps(14) defined_eval_is_intval evale evaltree_not_undef is_IntVal_def)
  also have xvalid: "valid_value xv (stamps x)"
    by (meson assms(1) encodeeval.simps eval_in_ids evalsub wf_stamp.elims(2))
  then obtain xl xh where xstamp: "stamps x = IntegerStamp b xl xh"
    using calculation valid_value.simps apply (cases "stamps x"; auto)
    by presburger
  from vval obtain yvv where yint: "yv = IntVal b yvv"
    by (metis Value.collapse(1) bin_eval.simps(14) bool_to_val_bin.simps calculation defined_eval_is_intval evale evaltree_not_undef intval_less_than.simps(1))
  then have yvalid: "valid_value yv (stamps y)"
    using assms(1) encodeeval.simps evalsub no_encoding wf_stamp.simps by blast
  then obtain yl yh where ystamp: "stamps y = IntegerStamp b yl yh"
    using calculation yint valid_value.simps apply (cases "stamps y"; auto)
    by presburger
  have "xl \<le> int_signed_value b xvv"
    using calculation valid_value.simps(1) xstamp xvalid by presburger
  moreover have "int_signed_value b yvv \<le> yh"
    using valid_value.simps(1) yint ystamp yvalid by presburger
  moreover have "xl \<ge> yh"
    using assms(4) xstamp ystamp by auto
  ultimately have "int_signed_value b xvv \<ge> int_signed_value b yvv"
    by linarith
  then have "\<not>(val_to_bool (intval_less_than xv yv))"
    by (simp add: \<open>(xv::Value) = IntVal (b::nat) (xvv::64 word)\<close> yint)
  then show ?thesis
    by (simp add: vval)
qed

theorem tryFoldTrue_valid:
  assumes "wf_stamp g stamps"
  assumes "tryFold (kind g nid) stamps True"
  assumes "[g, m, p] \<turnstile> nid \<mapsto> v"
  shows "val_to_bool v"
  using assms(2) proof (induction "kind g nid" stamps True rule: tryFold.induct)
case (1 stamps x y)
  then show ?case
    using alwaysDistinct_valid assms by force
next
  case (2 stamps x y)
  then show ?case
    by (smt (verit, best) one_neq_zero tryFold.cases neverDistinct_valid assms
        stampUnder_valid val_to_bool.simps(1))
next
  case (3 stamps x y)
  then show ?case
    by (smt (verit, best) one_neq_zero tryFold.cases neverDistinct_valid assms
        val_to_bool.simps(1) stampUnder_valid)
next
case (4 stamps x y)
  then show ?case
    by force
qed

theorem tryFoldFalse_valid:
  assumes "wf_stamp g stamps"
  assumes "tryFold (kind g nid) stamps False"
  assumes "[g, m, p] \<turnstile> nid \<mapsto> v"
  shows "\<not>(val_to_bool v)"
using assms(2) proof (induction "kind g nid" stamps False rule: tryFold.induct)
case (1 stamps x y)
  then show ?case
    by (smt (verit) stampOver_valid alwaysDistinct_valid tryFold.cases
        neverDistinct_valid val_to_bool.simps(1) assms)
next
case (2 stamps x y)
  then show ?case
    by blast
next
  case (3 stamps x y)
  then show ?case
    by blast
next
  case (4 stamps x y)
  then show ?case
    by (smt (verit, del_insts) tryFold.cases alwaysDistinct_valid val_to_bool.simps(1)
        stampOver_valid assms)
qed


subsection \<open>Lift rules\<close>

inductive condset_implies :: "IRExpr set \<Rightarrow> IRExpr \<Rightarrow> bool \<Rightarrow> bool" where
  impliesTrue:
  "(\<exists>ce \<in> conds . (ce \<Rrightarrow> cond)) \<Longrightarrow> condset_implies conds cond True" |
  impliesFalse:
  "(\<exists>ce \<in> conds . (ce \<Rrightarrow>\<not> cond)) \<Longrightarrow> condset_implies conds cond False"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool) condset_implies .

text \<open>
The @{term cond_implies} function lifts the structural and type implication
rules to the one relation.
\<close>

fun conds_implies :: "IRExpr set \<Rightarrow> (ID \<Rightarrow> Stamp) \<Rightarrow> IRNode \<Rightarrow> IRExpr \<Rightarrow> bool option" where
  "conds_implies conds stamps condNode cond = 
    (if condset_implies conds cond True \<or> tryFold condNode stamps True 
      then Some True
    else if condset_implies conds cond False \<or> tryFold condNode stamps False
      then Some False
    else None)"

text \<open>
Perform conditional elimination rewrites on the graph for a particular node
by lifting the individual implication rules to a relation that rewrites the
condition of \textsl{if} statements to constant values.

In order to determine conditional eliminations appropriately the rule needs two
data structures produced by static analysis.
The first parameter is the set of IRNodes that we know result in a true value
when evaluated.
The second parameter is a mapping from node identifiers to the flow-sensitive stamp.
\<close>

inductive ConditionalEliminationStep :: 
  "IRExpr set \<Rightarrow> (ID \<Rightarrow> Stamp) \<Rightarrow> ID \<Rightarrow> IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool"
  where
  impliesTrue:
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


code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) ConditionalEliminationStep .

thm ConditionalEliminationStep.equation



subsection \<open>Control-flow Graph Traversal\<close>

type_synonym Seen = "ID set"
type_synonym Condition = "IRExpr"
type_synonym Conditions = "Condition list"
type_synonym StampFlow = "(ID \<Rightarrow> Stamp) list"
type_synonym ToVisit = "ID list"


text \<open>
@{term "nextEdge"} helps determine which node to traverse next 
by returning the first successor edge that isn't in the set of already visited nodes.
If there is not an appropriate successor, None is returned instead.
\<close>
fun nextEdge :: "Seen \<Rightarrow> ID \<Rightarrow> IRGraph \<Rightarrow> ID option" where
  "nextEdge seen nid g = 
    (let nids = (filter (\<lambda>nid'. nid' \<notin> seen) (successors_of (kind g nid))) in 
     (if length nids > 0 then Some (hd nids) else None))"

text \<open>
@{term "pred"} determines which node, if any, acts as the predecessor of another.

Merge nodes represent a special case wherein the predecessor exists as
an input edge of the merge node, to simplify the traversal we treat only
the first input end node as the predecessor, ignoring that multiple nodes
may act as a successor.

For all other nodes, the predecessor is the first element of the predecessors set.
Note that in a well-formed graph there should only be one element in the predecessor set.
\<close>
fun preds :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID list" where
  "preds g nid = (case kind g nid of
    (MergeNode ends _ _) \<Rightarrow> ends |
    _ \<Rightarrow> 
      sorted_list_of_set (IRGraph.predecessors g nid)
  )"

fun pred :: "IRGraph \<Rightarrow> ID \<Rightarrow> ID option" where
  "pred g nid = (case preds g nid of [] \<Rightarrow> None | x # xs \<Rightarrow> Some x)"


text \<open>
When the basic block of an if statement is entered, we know that the condition of the
preceding if statement must be true.
As in the GraalVM compiler, we introduce the \texttt{registerNewCondition} function
which roughly corresponds to \texttt{ConditionalEliminationPhase.registerNewCondition}.
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

fun max_lower :: "Stamp \<Rightarrow> Stamp \<Rightarrow> Stamp" where
  "max_lower (IntegerStamp b1 xl xh) (IntegerStamp b2 yl yh) =
        (IntegerStamp b1 (max xl yl) xh)" |
  "max_lower xs ys = xs"
fun min_higher :: "Stamp \<Rightarrow> Stamp \<Rightarrow> Stamp" where
  "min_higher (IntegerStamp b1 xl xh) (IntegerStamp b2 yl yh) =
        (IntegerStamp b1 yl (min xh yh))" |
  "min_higher xs ys = ys"

fun registerNewCondition :: "IRGraph \<Rightarrow> IRNode \<Rightarrow> (ID \<Rightarrow> Stamp) \<Rightarrow> (ID \<Rightarrow> Stamp)" where
  \<comment> \<open>constrain equality by joining the stamps\<close>
  "registerNewCondition g (IntegerEqualsNode x y) stamps =
    (stamps
      (x := join (stamps x) (stamps y)))
      (y := join (stamps x) (stamps y))" |
  \<comment> \<open>constrain less than by removing overlapping stamps\<close>
  "registerNewCondition g (IntegerLessThanNode x y) stamps =
    (stamps
      (x := clip_upper (stamps x) ((stpi_lower (stamps y)) - 1)))
      (y := clip_lower (stamps y) ((stpi_upper (stamps x)) + 1))" |
  "registerNewCondition g (LogicNegationNode c) stamps =
    (case (kind g c) of
      (IntegerLessThanNode x y) \<Rightarrow>
        (stamps
          (x := max_lower (stamps x) (stamps y)))
          (y := min_higher (stamps x) (stamps y))
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
A base case for root nodes is required as @{term "\<Inter>{} = coset []"}
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

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) condition_of .

(*inductive
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
    \<Longrightarrow> conditions_of_dominators g nids conditions conditions'"*)

fun conditions_of_dominators :: "IRGraph \<Rightarrow> ID list \<Rightarrow> Conditions \<Rightarrow> Conditions" where
  "conditions_of_dominators g [] cds = cds" |
  "conditions_of_dominators g (nid # nids) cds = 
    (case (Predicate.the (condition_of_i_i_o g nid)) of 
      None \<Rightarrow> conditions_of_dominators g nids cds |
      Some (expr, _) \<Rightarrow> conditions_of_dominators g nids (expr # cds))"

(*code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) conditions_of_dominators .*)

(*
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
*)

fun stamps_of_dominators :: "IRGraph \<Rightarrow> ID list \<Rightarrow> StampFlow \<Rightarrow> StampFlow" where
  "stamps_of_dominators g [] stamps = stamps" |
  "stamps_of_dominators g (nid # nids) stamps = 
    (case (Predicate.the (condition_of_i_i_o g nid)) of 
      None \<Rightarrow> stamps_of_dominators g nids stamps |
      Some (_, node) \<Rightarrow> stamps_of_dominators g nids 
        ((registerNewCondition g node (hd stamps)) # stamps))"

(*code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) stamps_of_dominators .*)

inductive
  analyse :: "IRGraph \<Rightarrow> DominatorCache \<Rightarrow> ID \<Rightarrow> (Conditions \<times> StampFlow \<times> DominatorCache) \<Rightarrow> bool" where
  "\<lbrakk>dominators g c nid (doms, c');
    conditions_of_dominators g (sorted_list_of_set doms) [] = conds;
    stamps_of_dominators g (sorted_list_of_set doms) [stamp g] = stamps\<rbrakk>
    \<Longrightarrow> analyse g c nid (conds, stamps, c')"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) analyse .

values "{x. dominators ConditionalEliminationTest13_testSnippet2_initial Map.empty 13 x}"
values "{(conds, stamps, c). 
analyse ConditionalEliminationTest13_testSnippet2_initial Map.empty 13 (conds, stamps, c)}"
values "{(hd stamps) 1| conds stamps c .
analyse ConditionalEliminationTest13_testSnippet2_initial Map.empty 13 (conds, stamps, c)}"
values "{(hd stamps) 1| conds stamps c .
analyse ConditionalEliminationTest13_testSnippet2_initial Map.empty 27 (conds, stamps, c)}"

fun next_nid :: "IRGraph \<Rightarrow> ID set \<Rightarrow> ID \<Rightarrow> ID option" where
  "next_nid g seen nid = (case (kind g nid) of
    (EndNode) \<Rightarrow> Some (any_usage g nid) |
    _ \<Rightarrow> nextEdge seen nid g)"

inductive Step
  :: "IRGraph \<Rightarrow> (ID \<times> Seen) \<Rightarrow> (ID \<times> Seen) option \<Rightarrow> bool"
  for g where
  \<comment> \<open>We can find a successor edge that is not in seen, go there\<close>
  "\<lbrakk>seen' = {nid} \<union> seen;

    Some nid' = next_nid g seen' nid;
    nid' \<notin> seen'\<rbrakk>
   \<Longrightarrow> Step g (nid, seen) (Some (nid', seen'))" |

  \<comment> \<open>We can cannot find a successor edge that is not in seen, give back None\<close>
  "\<lbrakk>seen' = {nid} \<union> seen;

    None = next_nid g seen' nid\<rbrakk>
    \<Longrightarrow> Step g (nid, seen) None" |

  \<comment> \<open>We've already seen this node, give back None\<close>
  "\<lbrakk>seen' = {nid} \<union> seen;

    Some nid' = next_nid g seen' nid;
    nid' \<in> seen'\<rbrakk> \<Longrightarrow> Step g (nid, seen) None"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) Step .

fun nextNode :: "IRGraph \<Rightarrow> Seen \<Rightarrow> (ID \<times> Seen) option" where
  "nextNode g seen = 
    (let toSee = sorted_list_of_set {n \<in> ids g. n \<notin> seen} in
      case toSee of [] \<Rightarrow> None | (x # xs) \<Rightarrow> Some (x, seen \<union> {x}))"

values "{x. Step ConditionalEliminationTest13_testSnippet2_initial (17, {17,11,25,21,18,19,15,12,13,6,29,27,24,23,7,8,0}) x}"


text \<open>
The @{text "ConditionalEliminationPhase"} relation is responsible for combining
the individual traversal steps from the @{text "Step"} relation and the optimizations
from the @{text "ConditionalEliminationStep"} relation to perform a transformation of the
whole graph.
\<close>

inductive ConditionalEliminationPhase 
  :: "(Seen \<times> DominatorCache) \<Rightarrow> IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool"
  where

  \<comment> \<open>Can do a step and optimise for the current node\<close>
  "\<lbrakk>nextNode g seen = Some (nid, seen');
    
    analyse g c nid (conds, flow, c');
    ConditionalEliminationStep (set conds) (hd flow) nid g g';

    ConditionalEliminationPhase (seen', c') g' g''\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhase (seen, c) g g''" |

  "\<lbrakk>nextNode g seen = None\<rbrakk>
    \<Longrightarrow> ConditionalEliminationPhase (seen, c) g g"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) ConditionalEliminationPhase . 

definition runConditionalElimination :: "IRGraph \<Rightarrow> IRGraph" where
  "runConditionalElimination g = 
    (Predicate.the (ConditionalEliminationPhase_i_i_o ({}, Map.empty) g))"


values "{(doms, c')| doms c'.
dominators ConditionalEliminationTest13_testSnippet2_initial Map.empty 6 (doms, c')}"

values "{(conds, stamps, c)| conds stamps c .
analyse ConditionalEliminationTest13_testSnippet2_initial Map.empty 6 (conds, stamps, c)}"
value "
  (nextNode
      ConditionalEliminationTest13_testSnippet2_initial {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29})
"
(*
values "{g|g. (ConditionalEliminationPhase ({}, Map.empty) ConditionalEliminationTest13_testSnippet2_initial g)}"
*)
(*
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
*)

lemma IfNodeStepE: "g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h) \<Longrightarrow>
  (\<And>cond tb fb val.
        kind g nid = IfNode cond tb fb \<Longrightarrow>
        nid' = (if val_to_bool val then tb else fb) \<Longrightarrow> 
        [g, m, p] \<turnstile> cond \<mapsto> val \<Longrightarrow> m' = m)"
  using StepE
  by (smt (verit, best) IfNode Pair_inject stepDet)

lemma ifNodeHasCondEvalStutter:
  assumes "(g m p h \<turnstile> nid \<leadsto> nid')"
  assumes "kind g nid = IfNode cond t f"
  shows "\<exists> v. ([g, m, p] \<turnstile> cond \<mapsto> v)"
  using IfNodeStepE assms(1) assms(2)  stutter.cases unfolding encodeeval.simps
  by (smt (verit, ccfv_SIG) IfNodeCond)

lemma ifNodeHasCondEval:
  assumes "(g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m', h'))"
  assumes "kind g nid = IfNode cond t f"
  shows "\<exists> v. ([g, m, p] \<turnstile> cond \<mapsto> v)"
  using IfNodeStepE assms(1) assms(2) apply auto[1]
  by (smt (verit) IRNode.disc(1966) IRNode.distinct(1733) IRNode.distinct(1735) IRNode.distinct(1755) IRNode.distinct(1757) IRNode.distinct(1777) IRNode.distinct(1783) IRNode.distinct(1787) IRNode.distinct(1789) IRNode.distinct(401) IRNode.distinct(755) StutterStep fst_conv ifNodeHasCondEvalStutter is_AbstractEndNode.simps is_EndNode.simps(16) snd_conv step.cases)

lemma replace_if_t:
  assumes "kind g nid = IfNode cond tb fb"
  assumes "[g, m, p] \<turnstile> cond \<mapsto> bool"
  assumes "val_to_bool bool"
  assumes g': "g' = replace_usages nid tb g"
  shows "\<exists>nid' .(g m p h \<turnstile> nid \<leadsto> nid') \<longleftrightarrow> (g' m p h \<turnstile> nid \<leadsto> nid')"
proof -
  have g1step: "g, p \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    by (meson IfNode assms(1) assms(2) assms(3) encodeeval.simps)
  have g2step: "g', p \<turnstile> (nid, m, h) \<rightarrow> (tb, m, h)"
    using g' unfolding replace_usages.simps
    by (simp add: stepRefNode)
  from g1step g2step show ?thesis
    using StutterStep by blast
qed

lemma replace_if_t_imp:
  assumes "kind g nid = IfNode cond tb fb"
  assumes "[g, m, p] \<turnstile> cond \<mapsto> bool"
  assumes "val_to_bool bool"
  assumes g': "g' = replace_usages nid tb g"
  shows "\<exists>nid' .(g m p h \<turnstile> nid \<leadsto> nid') \<longrightarrow> (g' m p h \<turnstile> nid \<leadsto> nid')"
  using replace_if_t assms by blast

lemma replace_if_f:
  assumes "kind g nid = IfNode cond tb fb"
  assumes "[g, m, p] \<turnstile> cond \<mapsto> bool"
  assumes "\<not>(val_to_bool bool)"
  assumes g': "g' = replace_usages nid fb g"
  shows "\<exists>nid' .(g m p h \<turnstile> nid \<leadsto> nid') \<longleftrightarrow> (g' m p h \<turnstile> nid \<leadsto> nid')"
proof -
  have g1step: "g, p \<turnstile> (nid, m, h) \<rightarrow> (fb, m, h)"
    by (meson IfNode assms(1) assms(2) assms(3) encodeeval.simps)
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
  assumes conds_valid: "\<forall> c \<in> conds . \<exists> v. ([m, p] \<turnstile> c \<mapsto> v) \<and> val_to_bool v"
  assumes ce: "ConditionalEliminationStep conds stamps nid g g'"

  shows "\<exists>nid' .(g m p h \<turnstile> nid \<leadsto> nid') \<longrightarrow> (g' m p h \<turnstile> nid \<leadsto> nid')"
  using ce using assms
proof (induct nid g g' rule: ConditionalEliminationStep.induct)
  case (impliesTrue g ifcond cid t f cond conds g')
  show ?case proof (cases "\<exists>nid'. (g m p h \<turnstile> ifcond \<leadsto> nid')")
    case True
    show ?thesis
      by (metis StutterStep constantConditionNoIf constantConditionTrue impliesTrue.hyps(5))
  next
    case False
    then show ?thesis by auto
  qed
next
  case (impliesFalse g ifcond cid t f cond conds g')
  then show ?case 
  proof (cases "\<exists>nid'. (g m p h \<turnstile> ifcond \<leadsto> nid')")
    case True
    then show ?thesis
      by (metis StutterStep constantConditionFalse constantConditionNoIf impliesFalse.hyps(5))
  next
    case False
    then show ?thesis
      by auto
  qed
next
  case (unknown g ifcond cid t f cond condNode conds stamps)
  then show ?case
    by blast
next
  case (notIfNode g ifcond conds stamps)
  then show ?case
    by blast
qed


text \<open>
Prove that the individual conditional elimination rules are correct
with respect to finding a bisimulation between the unoptimized and optimized graphs.
\<close>
lemma ConditionalEliminationStepProofBisimulation:
  assumes wf: "wf_graph g \<and> wf_stamp g stamps \<and> wf_values g"
  assumes nid: "nid \<in> ids g"
  assumes conds_valid: "\<forall> c \<in> conds . \<exists> v. ([m, p] \<turnstile> c \<mapsto> v) \<and> val_to_bool v"
  assumes ce: "ConditionalEliminationStep conds stamps nid g g'"
  assumes gstep: "\<exists> h nid'. (g, p \<turnstile> (nid, m, h) \<rightarrow> (nid', m, h))" (* we don't yet consider optimizations which produce a step that didn't already exist *)

  shows "nid | g \<sim> g'"
  using ce gstep using assms
proof (induct nid g g' rule: ConditionalEliminationStep.induct)
  case (impliesTrue g ifcond cid t f cond condNode conds stamps g')
  from impliesTrue(5) obtain h where gstep: "g, p \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
    using IfNode encodeeval.simps ifNodeHasCondEval impliesTrue.hyps(1) impliesTrue.hyps(2) impliesTrue.hyps(3) impliesTrue.prems(4) implies_impliesnot_valid implies_valid.simps repDet
    by (smt (verit) conds_implies.elims condset_implies.simps impliesTrue.hyps(4) impliesTrue.prems(1) impliesTrue.prems(2) option.distinct(1) option.inject tryFoldTrue_valid)
  have "g', p \<turnstile> (ifcond, m, h) \<rightarrow> (t, m, h)"
    using constantConditionTrue impliesTrue.hyps(1) impliesTrue.hyps(5) by blast
  then show ?case using gstep
    by (metis stepDet strong_noop_bisimilar.intros)
next
  case (impliesFalse g ifcond cid t f cond condNode conds stamps g')
  from impliesFalse(5) obtain h where gstep: "g, p \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
    using IfNode encodeeval.simps ifNodeHasCondEval impliesFalse.hyps(1) impliesFalse.hyps(2) impliesFalse.hyps(3) impliesFalse.prems(4) implies_impliesnot_valid impliesnot_valid.simps repDet
    by (smt (verit) conds_implies.elims condset_implies.simps impliesFalse.hyps(4) impliesFalse.prems(1) impliesFalse.prems(2) option.distinct(1) option.inject tryFoldFalse_valid)
  have "g', p \<turnstile> (ifcond, m, h) \<rightarrow> (f, m, h)"
    using constantConditionFalse impliesFalse.hyps(1) impliesFalse.hyps(5) by blast
  then show ?case using gstep
    by (metis stepDet strong_noop_bisimilar.intros)
next
  case (unknown g ifcond cid t f cond condNode conds stamps)
  then show ?case
    using strong_noop_bisimilar.simps by presburger
next
  case (notIfNode g ifcond conds stamps)
  then show ?case
    using strong_noop_bisimilar.simps by presburger
qed


experiment begin
(*lemma if_step:
  assumes "nid \<in> ids g"
  assumes "(kind g nid) \<in> control_nodes"
  shows "(g m p h \<turnstile> nid \<leadsto> nid')"
  using assms apply (cases "kind g nid") sorry
*)
(*
definition blockNodes :: "IRGraph \<Rightarrow> Block \<Rightarrow> ID set" where
  "blockNodes g b = {n \<in> ids g. blockOf g n = b}"

lemma phiInCFG:
  "\<forall>n \<in> blockNodes g nid. (g, p \<turnstile> (n, m, h) \<rightarrow> (n', m', h'))"
*)

lemma inverse_succ:
  "\<forall>n' \<in> (succ g n). n \<in> ids g \<longrightarrow> n \<in> (predecessors g n')"
  by simp

lemma sequential_successors:
  assumes "is_sequential_node n"
  shows "successors_of n \<noteq> []"
  using assms by (cases n; auto)

lemma nid'_succ:
  assumes "nid \<in> ids g"
  assumes "\<not>(is_AbstractEndNode (kind g nid0))"
  assumes "g, p \<turnstile> (nid0, m0, h0) \<rightarrow> (nid, m, h)"
  shows "nid \<in> succ g nid0"
  using assms(3) proof (induction "(nid0, m0, h0)" "(nid, m, h)" rule: step.induct)
  case SequentialNode
  then show ?case
    by (metis length_greater_0_conv nth_mem sequential_successors succ.simps)
next
  case (FixedGuardNode cond before val)
  then have "{nid} = succ g nid0"
    using IRNodes.successors_of_FixedGuardNode unfolding succ.simps
    by (metis empty_set list.simps(15))
  then show ?case
    using FixedGuardNode.hyps(5) by blast
next
  case (BytecodeExceptionNode args st exceptionType ref)
  then have "{nid} = succ g nid0"
    using IRNodes.successors_of_BytecodeExceptionNode unfolding succ.simps
    by (metis empty_set list.simps(15))
  then show ?case
    by blast
next
  case (IfNode cond tb fb val)
  then have "{tb, fb} = succ g nid0"
    using IRNodes.successors_of_IfNode unfolding succ.simps
    by (metis empty_set list.simps(15))
  then show ?case
    by (metis IfNode.hyps(3) insert_iff)
next
  case (EndNodes i phis inps vs)
  then show ?case using assms(2) by blast
next
  case (NewArrayNode len st length' arrayType h' ref refNo)
  then have "{nid} = succ g nid0"
    using IRNodes.successors_of_NewArrayNode unfolding succ.simps
    by (metis empty_set list.simps(15))
  then show ?case
    by blast
next
  case (ArrayLengthNode x ref arrayVal length')
  then have "{nid} = succ g nid0"
    using IRNodes.successors_of_ArrayLengthNode unfolding succ.simps
    by (metis empty_set list.simps(15))
  then show ?case
    by blast
next
  case (LoadIndexedNode index guard array indexVal ref arrayVal loaded)
  then have "{nid} = succ g nid0"
    using IRNodes.successors_of_LoadIndexedNode unfolding succ.simps
    by (metis empty_set list.simps(15))
  then show ?case
    by blast
next
  case (StoreIndexedNode check val st index guard array indexVal ref "value" arrayVal updated)
  then have "{nid} = succ g nid0"
    using IRNodes.successors_of_StoreIndexedNode unfolding succ.simps
    by (metis empty_set list.simps(15))
  then show ?case
    by blast
next
  case (NewInstanceNode cname obj ref)
  then have "{nid} = succ g nid0"
    using IRNodes.successors_of_NewInstanceNode unfolding succ.simps
    by (metis empty_set list.simps(15))
  then show ?case
    by blast
next
  case (LoadFieldNode f obj ref)
  then have "{nid} = succ g nid0"
    using IRNodes.successors_of_LoadFieldNode unfolding succ.simps
    by (metis empty_set list.simps(15))
  then show ?case
    by blast
next
  case (SignedDivNode x y zero sb v1 v2)
  then have "{nid} = succ g nid0"
    using IRNodes.successors_of_SignedDivNode unfolding succ.simps
    by (metis empty_set list.simps(15))
  then show ?case
    by blast
next
  case (SignedRemNode x y zero sb v1 v2)
  then have "{nid} = succ g nid0"
    using IRNodes.successors_of_SignedRemNode unfolding succ.simps
    by (metis empty_set list.simps(15))
  then show ?case
    by blast
next
  case (StaticLoadFieldNode f)
  then have "{nid} = succ g nid0"
    using IRNodes.successors_of_LoadFieldNode unfolding succ.simps
    by (metis empty_set list.simps(15))
  then show ?case
    by blast
next 
  case (StoreFieldNode _ _ _ _ _ _) 
  then have "{nid} = succ g nid0"
    using IRNodes.successors_of_StoreFieldNode unfolding succ.simps
    by (metis empty_set list.simps(15))
  then show ?case
    by blast
next
  case (StaticStoreFieldNode _ _ _ _)
  then have "{nid} = succ g nid0"
    using IRNodes.successors_of_StoreFieldNode unfolding succ.simps
    by (metis empty_set list.simps(15))
  then show ?case
    by blast
qed

lemma nid'_pred:
  assumes "nid \<in> ids g"
  assumes "\<not>(is_AbstractEndNode (kind g nid0))"
  assumes "g, p \<turnstile> (nid0, m0, h0) \<rightarrow> (nid, m, h)"
  shows "nid0 \<in> predecessors g nid"
  using assms
  by (meson inverse_succ nid'_succ step_in_ids)

definition wf_pred:
  "wf_pred g = (\<forall>n \<in> ids g. card (predecessors g n) = 1)"

lemma
  assumes "\<not>(is_AbstractMergeNode (kind g n'))"
  assumes "wf_pred g"
  shows "\<exists>v. predecessors g n = {v} \<and> pred g n' = Some v"
  using assms unfolding pred.simps sorry

lemma inverse_succ1:
  assumes "\<not>(is_AbstractEndNode (kind g n'))"
  assumes "wf_pred g"
  shows "\<forall>n' \<in> (succ g n). n \<in> ids g \<longrightarrow> Some n = (pred g n')"
  using assms sorry

lemma BeginNodeFlow:
  assumes "g, p \<turnstile> (nid0, m0, h0) \<rightarrow> (nid, m, h)"
  assumes "Some ifcond = pred g nid"
  assumes "kind g ifcond = IfNode cond t f"
  assumes "i = find_index nid (successors_of (kind g ifcond))"
  shows "i = 0 \<longleftrightarrow> ([g, m, p] \<turnstile> cond \<mapsto> v) \<and> val_to_bool v"
proof -
  obtain tb fb where "[tb, fb] = successors_of (kind g ifcond)"
    by (simp add: assms(3))
  have "nid0 = ifcond"
    using assms step.IfNode sorry
  show ?thesis sorry
qed

(*
lemma StepConditionsValid:
  assumes "\<forall> cond \<in> set conds. ([m, p] \<turnstile> cond \<mapsto> v) \<longrightarrow> val_to_bool v"
  assumes "g, p \<turnstile> (nid0, m0, h0) \<rightarrow> (nid, m, h)"
  assumes "Step g (nid, seen, conds, flow) (Some (nid', seen', conds', flow'))"
  shows "\<forall> cond \<in> set conds'. ([m, p] \<turnstile> cond \<mapsto> v) \<longrightarrow> val_to_bool v"
  using assms(3)
proof (induction "(nid, seen, conds, flow)" "Some (nid', seen', conds', flow')" rule: Step.induct)
  case (1 ifcond cond t f i c ce ce' flow')
  assume "\<exists>cv. [m, p] \<turnstile> ce \<mapsto> cv"
  then obtain cv where "[m, p] \<turnstile> ce \<mapsto> cv"
    by blast
  have cvt: "val_to_bool cv"
    using assms(2) sorry
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
*)

end

end
