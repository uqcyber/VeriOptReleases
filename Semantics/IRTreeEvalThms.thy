subsection \<open>Data-flow Tree Theorems\<close>

theory IRTreeEvalThms
  imports
    Graph.ValueThms
    IRTreeEval
begin

subsubsection \<open>Deterministic Data-flow Evaluation\<close>

lemma evalDet:
  "[m,p] \<turnstile> e \<mapsto> v\<^sub>1 \<Longrightarrow> 
   [m,p] \<turnstile> e \<mapsto> v\<^sub>2 \<Longrightarrow>
   v\<^sub>1 = v\<^sub>2"
  apply (induction arbitrary: v\<^sub>2 rule: "evaltree.induct") by (elim EvalTreeE; auto)+

lemma evalAllDet:
  "[m,p] \<turnstile> e \<mapsto>\<^sub>L v1 \<Longrightarrow> 
   [m,p] \<turnstile> e \<mapsto>\<^sub>L v2 \<Longrightarrow>
   v1 = v2"
  apply (induction arbitrary: v2 rule: "evaltrees.induct")
  apply (elim EvalTreeE; auto)
  using evalDet by force

subsubsection \<open>Typing Properties for Integer Evaluation Functions\<close>

text \<open>We use three simple typing properties on integer values: 
   $is_IntVal32, is_IntVal64$ and the more general $is_IntVal$.\<close>

lemma unary_eval_not_obj_ref:
  shows "unary_eval op x \<noteq> ObjRef v"
  by (cases op; cases x; auto)

lemma unary_eval_not_obj_str:
  shows "unary_eval op x \<noteq> ObjStr v"
  by (cases op; cases x; auto)

(* declare [[show_types = true]] *)

(* TODO: try proving some results about int_[un]signed_value? *)
(* TODO
lemma negative_iff_top_bit:
  fixes v :: "'a :: len word"
  assumes "b < LENGTH('a)"
  shows "(signed_take_bit b v <s 0) = bit v b"
  using signed_take_bit_negative_iff apply transfer

lemma signed_eq_unsigned:
  assumes "int_signed_value b v \<ge> 0"
  shows "int_signed_value b v = int_unsigned_value b v"
proof -
  thm signed_take_bit_negative_iff

  have "\<not> bit v b"
    using assms int_signed_value.simps 
*)

(* Note: this will need qualifying once we have non-integer unary ops. *)
lemma unary_eval_int:
  assumes "unary_eval op x \<noteq> UndefVal"
  shows "is_IntVal (unary_eval op x)"
  by (cases "unary_eval op x"; auto simp add: assms unary_eval_not_obj_ref unary_eval_not_obj_str)

lemma bin_eval_int:
  assumes "bin_eval op x y \<noteq> UndefVal"
  shows "is_IntVal (bin_eval op x y)" 
  using assms
  apply (cases op; cases x; cases y; auto simp add: is_IntVal_def)
  apply presburger+ (* prove 6 more easy cases *)
  prefer 3 prefer 4
     apply (smt (verit, best) new_int.simps)
     apply (smt (verit, best) new_int.simps)
  by (metis bool_to_val.elims)+

lemma IntVal0:
  "(IntVal 32 0) = (new_int 32 0)"
  by auto

lemma IntVal1:
  "(IntVal 32 1) = (new_int 32 1)"
  by auto

(* ICK, a collection of relevant take_bit_x lemmas would help *)
lemma bin_eval_new_int:
  assumes "bin_eval op x y \<noteq> UndefVal"
  shows "\<exists>b v. (bin_eval op x y) = new_int b v \<and>
               b = (if op \<in> binary_fixed_32_ops then 32 else intval_bits x)"
  using is_IntVal_def assms
proof (cases op)
  case BinAdd
  then show ?thesis
    using assms apply (cases x; cases y; auto) by presburger
next
  case BinMul
  then show ?thesis
    using assms apply (cases x; cases y; auto) by presburger
next
  case BinSub
  then show ?thesis
    using assms apply (cases x; cases y; auto) by presburger
next
  case BinAnd
  then show ?thesis
    using assms apply (cases x; cases y; auto) by (metis take_bit_and)+
next
  case BinOr
  then show ?thesis
    using assms apply (cases x; cases y; auto) by (metis take_bit_or)+
next
  case BinXor
  then show ?thesis
    using assms apply (cases x; cases y; auto) by (metis take_bit_xor)+
next
  case BinShortCircuitOr
  then show ?thesis
    using assms apply (cases x; cases y; auto)
    by (metis IntVal1 bits_mod_0 bool_to_val.elims new_int.simps take_bit_eq_mod)+
next
  case BinLeftShift
  then show ?thesis
    using assms by (cases x; cases y; auto)
next
  case BinRightShift
  then show ?thesis
    using assms apply (cases x; cases y; auto) by (smt (verit, del_insts) new_int.simps)+
next
  case BinURightShift
  then show ?thesis
    using assms by (cases x; cases y; auto)
next
  case BinIntegerEquals
  then show ?thesis
    using assms apply (cases x; cases y; auto)
    apply (metis (full_types) IntVal0 IntVal1 bool_to_val.simps(1,2) new_int.elims) by presburger
next
  case BinIntegerLessThan
  then show ?thesis
    using assms apply (cases x; cases y; auto)
    apply (metis (no_types, opaque_lifting) bool_to_val.simps(1,2) bool_to_val.elims new_int.simps
           IntVal1 take_bit_of_0)
    by presburger
next
  case BinIntegerBelow
  then show ?thesis
    using assms apply (cases x; cases y; auto)
    apply (metis bool_to_val.simps(1,2) bool_to_val.elims new_int.simps IntVal0 IntVal1)
    by presburger
next
  case BinIntegerTest
  then show ?thesis
    using assms apply (cases x; cases y; auto)
    apply (metis bool_to_val.simps(1,2) bool_to_val.elims new_int.simps IntVal0 IntVal1)
    by presburger
next
  case BinIntegerNormalizeCompare
  then show ?thesis
    using assms apply (cases x; cases y; auto) using take_bit_of_0 apply blast
    by (metis IntVal1 intval_word.simps new_int.elims take_bit_minus_one_eq_mask)+
next
  case BinIntegerMulHigh
  then show ?thesis
    using assms apply (cases x; cases y; auto)
    prefer 2 prefer 5 prefer 8
      apply presburger+
    by metis+
qed

lemma int_stamp:
  assumes "is_IntVal v"
  shows "is_IntegerStamp (constantAsStamp v)"
  using assms is_IntVal_def by auto

lemma validStampIntConst:
  assumes "v = IntVal b ival"
  assumes "0 < b \<and> b \<le> 64"
  shows "valid_stamp (constantAsStamp v)"
proof -
  have bnds: "fst (bit_bounds b) \<le> int_signed_value b ival \<and> 
              int_signed_value b ival \<le> snd (bit_bounds b)"
    using assms(2) int_signed_value_bounds by simp
  have s: "constantAsStamp v = IntegerStamp b (int_signed_value b ival) (int_signed_value b ival)"
    using assms(1) by simp
  then show ?thesis
    unfolding s valid_stamp.simps using assms(2) bnds by linarith 
qed

lemma validDefIntConst:
  assumes v: "v = IntVal b ival"
  assumes "0 < b \<and> b \<le> 64"
  assumes "take_bit b ival = ival"
  shows "valid_value v (constantAsStamp v)"
proof -
  have bnds: "fst (bit_bounds b) \<le> int_signed_value b ival \<and> 
              int_signed_value b ival \<le> snd (bit_bounds b)"
    using assms(2) int_signed_value_bounds by simp
  have s: "constantAsStamp v = IntegerStamp b (int_signed_value b ival) (int_signed_value b ival)"
    using assms(1) by simp
  then show ?thesis
    using assms validStampIntConst by simp
qed

(* is it useful to have a new_int version of the above? 
lemma validIntConst:
  assumes i: "v = new_int b ival"
  assumes "0 < b \<and> b \<le> 64"
  shows "valid_value v (constantAsStamp v)"
proof -
  have bnds: "fst (bit_bounds b) \<le> int_signed_value b ival \<and> int_signed_value b ival \<le> snd (bit_bounds b)"
    using assms int_signed_value_bounds
    by presburger 
  have s: "constantAsStamp v = IntegerStamp b (int_signed_value b ival) (int_signed_value b ival)"
    using assms new_int.simps constantAsStamp.simps 
  then show ?thesis
  using i new_int.simps validDefIntConst 
*)

subsubsection \<open>Evaluation Results are Valid\<close>

text \<open>A valid value cannot be $UndefVal$.\<close>
lemma valid_not_undef:
  assumes "valid_value val s"
  assumes "s \<noteq> VoidStamp"
  shows "val \<noteq> UndefVal"
  apply (rule valid_value.elims(1)[of val s True]) using assms by auto

(* Elimination rules for valid_value, for each kind of stamp. *)
lemma valid_VoidStamp[elim]:
  shows "valid_value val VoidStamp \<Longrightarrow> val = UndefVal"
  by (metis valid_value.simps(12))

lemma valid_ObjStamp[elim]:
  shows "valid_value val (ObjectStamp klass exact nonNull alwaysNull) \<Longrightarrow> (\<exists>v. val = ObjRef v)"
  by (metis val_to_bool.cases valid_value.simps(3,11,17))

lemma valid_int[elim]:
  shows "valid_value val (IntegerStamp b lo hi) \<Longrightarrow> (\<exists>v. val = IntVal b v)"
  using valid_value.elims(2) by fastforce

lemmas valid_value_elims =
  valid_VoidStamp
  valid_ObjStamp
  valid_int

lemma evaltree_not_undef:
  fixes m p e v
  shows "([m,p] \<turnstile> e \<mapsto> v) \<Longrightarrow> v \<noteq> UndefVal"
  apply (induction rule: "evaltree.induct") by (auto simp add: wf_value_def)

lemma leafint:
  assumes "[m,p] \<turnstile> LeafExpr i (IntegerStamp b lo hi) \<mapsto> val"
  shows "\<exists>b v. val = (IntVal b v)"
(* Note: we could also add: ...\<and> lo \<le> sint v \<and> sint v \<le> hi *)
proof - 
  have "valid_value val (IntegerStamp b lo hi)"
    using assms by (rule LeafExprE; simp)
  then show ?thesis
    by auto
qed

lemma default_stamp [simp]: "default_stamp = IntegerStamp 32 (-2147483648) 2147483647"
  by (auto simp add: default_stamp_def)

lemma valid_value_signed_int_range [simp]:
  assumes "valid_value val (IntegerStamp b lo hi)"
  assumes "lo < 0"
  shows "\<exists>v. (val = IntVal b v \<and> 
             lo \<le> int_signed_value b v \<and> 
             int_signed_value b v \<le> hi)"
  by (metis valid_value.simps(1) assms(1) valid_int)

(* If we want to support unsigned values:
lemma valid_value_unsigned_int_range [simp]:
  assumes "valid_value val (IntegerStamp b lo hi)"
  assumes "0 \<le> lo"
  shows "\<exists>v. (val = IntVal b v \<and> 
             lo \<le> int_unsigned_value b v \<and> 
             int_unsigned_value b v \<le> hi)"
  using assms valid_int
  by fastforce
*)

subsubsection \<open>Example Data-flow Optimisations\<close>

(* TODO: need to know that valid_values fit within b bits!
   This requires that the bounds also fit within b bits!
lemma valid_value_fits:
  assumes "valid_value (IntVal b v) (IntegerStamp b lo hi)"
  assumes "0 \<le> lo"
  shows "take_bit b v = v"
  using assms valid_value_unsigned_int_range 
*)

(* An example refinement: a + 0 = a *)
(*
lemma a0a_helper [simp]:
  assumes a: "valid_value v (IntegerStamp b lo hi)"
  shows "intval_add v (IntVal b 0) = v"
proof -
  obtain v64 :: int64 where "v = (IntVal b v64)" using a valid_int by blast 
  then have "v64+0=v64" by simp
  then have "intval_add (IntVal b v64) (IntVal b 0) = IntVal b (take_bit b v64)"
    by auto
  then show ?thesis 
qed

lemma a0a: "(BinaryExpr BinAdd (LeafExpr 1 default_stamp) (ConstantExpr (IntVal32 0)))
              \<ge> (LeafExpr 1 default_stamp)"
  by (auto simp add: evaltree.LeafExpr)
*)

(* Another example refinement: x + (y - x) \<ge> y *)
(* TODO:
lemma xyx_y_helper [simp]:
  assumes "valid_value x (IntegerStamp 32 lox hix)"
  assumes "valid_value y (IntegerStamp 32 loy hiy)"
  shows "intval_add x (intval_sub y x) = y"
proof -
  obtain x32 :: int32 where x: "x = (IntVal32 x32)" using assms valid32 by blast
  obtain y32 :: int32 where y: "y = (IntVal32 y32)" using assms valid32 by blast
  show ?thesis using x y by simp
qed

lemma xyx_y: 
  "(BinaryExpr BinAdd
     (LeafExpr x (IntegerStamp 32 lox hix))
     (BinaryExpr BinSub
       (LeafExpr y (IntegerStamp 32 loy hiy))
       (LeafExpr x (IntegerStamp 32 lox hix))))
   \<ge> (LeafExpr y (IntegerStamp 32 loy hiy))"
  by (auto simp add: LeafExpr)
*)

subsubsection \<open>Monotonicity of Expression Refinement\<close>

text \<open>We prove that each subexpression position is monotonic.
That is, optimizing a subexpression anywhere deep inside a top-level expression
also optimizes that top-level expression.  

Note that we might also be able to do
this via reusing Isabelle's $mono$ operator (HOL.Orderings theory), proving instantiations
like $mono (UnaryExpr op)$, but it is not obvious how to do this for both arguments
of the binary expressions.\<close>

lemma mono_unary: 
  assumes "x \<ge> x'"
  shows "(UnaryExpr op x) \<ge> (UnaryExpr op x')"
  using assms by auto

lemma mono_binary: 
  assumes "x \<ge> x'"
  assumes "y \<ge> y'"
  shows "(BinaryExpr op x y) \<ge> (BinaryExpr op x' y')"
  using BinaryExpr assms by auto

lemma never_void:
  assumes "[m, p] \<turnstile> x \<mapsto> xv"
  assumes "valid_value xv (stamp_expr xe)"
  shows "stamp_expr xe \<noteq> VoidStamp"
  using assms(2) by force

(* These were trivially true, due to operator precedence errors.
lemma stamp32:
  "\<exists>v . ((xv = IntVal32 v) \<longleftrightarrow> valid_value xv (IntegerStamp 32 lo hi))"
  using valid_int32
  by (metis (full_types) Value.inject(1) zero_neq_one)

lemma stamp64:
  "\<exists>v . xv = IntVal64 v \<longleftrightarrow> valid_value xv (IntegerStamp 64 lo hi)"
  using valid_int64
  by (metis (full_types) Value.inject(2) zero_neq_one)
*)

(* This lemma is no longer true once we allow some non-integer values.
lemma stamprange:
  "valid_value v s \<longrightarrow> (\<exists>b lo hi. (s = IntegerStamp b lo hi) \<and> (b=8 \<or> b=16 \<or> b=32 \<or> b=64))"
  using valid_value.elims
*)  

lemma compatible_trans:
  "compatible x y \<and> compatible y z \<Longrightarrow> compatible x z"
  by (cases x; cases y; cases z; auto)

lemma compatible_refl:
  "compatible x y \<Longrightarrow> compatible y x"
  using compatible.elims(2) by fastforce

(*
lemma tmp:
  assumes "[m, p] \<turnstile> xe \<mapsto> xv"
  shows "valid_value xv (stamp_expr xe)"
  sorry (* proved later *)

lemma helping:
  assumes "[m, p] \<turnstile> xe \<mapsto> xv"
  assumes "\<forall>m p v. ([m,p] \<turnstile> xe \<mapsto> v) \<longrightarrow> [m,p] \<turnstile> ye \<mapsto> v"
  shows "compatible (stamp_expr xe) (stamp_expr ye)"
proof -
  have "[m, p] \<turnstile> ye \<mapsto> xv"
    using assms(1,2)
    by blast
  then have "valid_value xv (stamp_expr ye)"
    using tmp by simp
  then show ?thesis using stamprange
      apply (cases "\<exists>v. xv = IntVal32 v")
    using assms(2) valid_value.elims(2)
    using assms(1) tmp apply fastforce
    by (smt (verit, del_insts) assms(1) compatible.simps(1) tmp valid_value.elims(2))
qed
*)

lemma mono_conditional: 
  assumes "c \<ge> c'"
  assumes "t \<ge> t'"
  assumes "f \<ge> f'"
  shows "(ConditionalExpr c t f) \<ge> (ConditionalExpr c' t' f')"
proof (simp only: le_expr_def; (rule allI)+; rule impI)
  fix m p v
  assume a: "[m,p] \<turnstile> ConditionalExpr c t f \<mapsto> v"
  then obtain cond where c: "[m,p] \<turnstile> c \<mapsto> cond" 
    by auto
  then have c': "[m,p] \<turnstile> c' \<mapsto> cond" 
    using assms by simp
  (*have co: "compatible (stamp_expr t) (stamp_expr f)"
    using a by auto*)
  then obtain tr where tr: "[m,p] \<turnstile> t \<mapsto> tr"
    using a by auto
  then have tr': "[m,p] \<turnstile> t' \<mapsto> tr"
    using assms(2) by auto
  then obtain fa where fa: "[m,p] \<turnstile> f \<mapsto> fa"
    using a by blast
  then have fa': "[m,p] \<turnstile> f' \<mapsto> fa"
    using assms(3) by auto
  define branch  where b:  "branch  = (if val_to_bool cond then t else f)"
  define branch' where b': "branch' = (if val_to_bool cond then t' else f')"
  then have beval: "[m,p] \<turnstile> branch \<mapsto> v" 
    using a b c evalDet by blast 
  (*then have "compatible (stamp_expr branch) (stamp_expr branch')"
      using helping
      using assms(2) assms(3) b b' by force
  then have compatible: "compatible (stamp_expr te') (stamp_expr fe')"
    using compatible_trans co compatible_refl
    proof (cases "val_to_bool cond")
      case True
      then have "branch = te"
        using b by simp
      from True have "branch' = te'"
        using b' by simp
      then have "compatible (stamp_expr te) (stamp_expr te')"
        using \<open>branch = te\<close> \<open>compatible (stamp_expr branch) (stamp_expr branch')\<close> by blast
      then have "compatible (stamp_expr fe) (stamp_expr fe')"
        using co compatible_trans compatible_refl sorry
      then show ?thesis
        using \<open>compatible (stamp_expr te) (stamp_expr te')\<close> co compatible_refl compatible_trans by blast
    next
      case False
      then show ?thesis sorry
    qed*)
  from beval have "[m,p] \<turnstile> branch' \<mapsto> v" 
    using assms by (auto simp add: b b')
  then show "[m,p] \<turnstile> ConditionalExpr c' t' f' \<mapsto> v"
    using c' fa' tr' by (simp add: evaltree_not_undef b' ConditionalExpr)
qed

(*
Step 3: if e1 isrefby e2 then g[e1] isREFby g[e2]
   Note: This needs to go after IRStepObj.thy.


lemma graph_refined:
  assumes "e1 \<ge> e2"
  assumes "g \<triangleleft> e1 \<leadsto> (g1, x1)"
  assumes "g \<triangleleft> e2 \<leadsto> (g2, x2)"
  shows "\<forall> m m' h h'. (g \<turnstile> (x1, m, h) \<rightarrow> (nid, m', h'))
                  \<longrightarrow> (g \<turnstile> (x2, m, h) \<rightarrow> (nid, m', h'))"
*)

subsection \<open>Unfolding rules for evaltree quadruples down to bin-eval level\<close>

text \<open>These rewrite rules can be useful when proving optimizations.
  They support top-down rewriting of each level of the tree into the 
  lower-level $bin_eval$ / $unary_eval$ level, simply by saying
  $unfolding unfold_evaltree$.\<close>

(* TODO:
lemma unfold_valid32 [simp]:
  "valid_value y (constantAsStamp (IntVal b v)) = (y = IntVal b v)"
  by (induction y; auto dest: signed_word_eqI)

lemma unfold_valid64 [simp]:
  "valid_value y (constantAsStamp (IntVal64 v)) = (y = IntVal64 v)"
  by (induction y; auto dest: signed_word_eqI)
*)

(* the general case, for all constants *)
lemma unfold_const:
  "([m,p] \<turnstile> ConstantExpr c \<mapsto> v) = (wf_value v \<and> v = c)"
  by auto

(* TODO:
corollary unfold_const32:
  shows "([m,p] \<turnstile> ConstantExpr (IntVal 32 c) \<mapsto> v) = (v = IntVal 32 c)"
  using unfold_valid32 by blast 

corollary unfold_const64:
  shows "([m,p] \<turnstile> ConstantExpr (IntVal64 c) \<mapsto> v) = (v = IntVal64 c)"
  using unfold_valid64 by blast 
*)

lemma unfold_binary:
  shows "([m,p] \<turnstile> BinaryExpr op xe ye \<mapsto> val) = (\<exists> x y.
          (([m,p] \<turnstile> xe \<mapsto> x) \<and>
           ([m,p] \<turnstile> ye \<mapsto> y) \<and>
           (val = bin_eval op x y) \<and>
           (val \<noteq> UndefVal)
        ))" (is "?L = ?R")  (* (\<exists> x y. (?R1 \<and> ?R2 \<and> ?R3))" *)
proof (intro iffI)
  assume 3: ?L
  show ?R by (rule evaltree.cases[OF 3]; blast+)
next
  assume ?R
  then obtain x y where "[m,p] \<turnstile> xe \<mapsto> x"
        and "[m,p] \<turnstile> ye \<mapsto> y"
        and "val = bin_eval op x y"
        and "val \<noteq> UndefVal"
    by auto
  then show ?L
     by (rule BinaryExpr)
 qed

lemma unfold_unary:
  shows "([m,p] \<turnstile> UnaryExpr op xe \<mapsto> val)
         = (\<exists> x.
             (([m,p] \<turnstile> xe \<mapsto> x) \<and>
              (val = unary_eval op x) \<and>
              (val \<noteq> UndefVal)
             ))" (is "?L = ?R")
  by auto

(* TODO: conditional *)

lemmas unfold_evaltree =
  unfold_binary
  unfold_unary
(*
  unfold_const32
  unfold_const64
  unfold_valid32
  unfold_valid64
*)

(* we could add this more general rule too, for completeness:
  unfold_const
  but we want the more specific unfold_const32/64 rules to have priority.
  This does not seem possible with 'lemmas' - order is ignored.
*)

subsection \<open>Lemmas about $new\_int$ and integer eval results.\<close>

lemma unary_eval_new_int:
  assumes def: "unary_eval op x \<noteq> UndefVal"
  shows "\<exists>b v. (unary_eval op x = new_int b v \<and>
              
          b = (if op \<in> normal_unary  then intval_bits x      else 
               if op \<in> boolean_unary then 32                 else 
                                          ir_resultBits op))"
proof (cases "op \<in> normal_unary")
  case True
  then show ?thesis
    by (metis def empty_iff insert_iff intval_abs.elims intval_bits.simps unary_eval.simps(1,2,3,4)
        intval_logic_negation.elims intval_negate.elims intval_not.elims)
next
  case False
  then show ?thesis
  proof (cases "op \<in> boolean_unary")
    case True
    then show ?thesis 
      by (metis IntVal0 IntVal1 singletonD unary_eval.simps(8) False intval_is_null.elims assms
          bool_to_val.elims)
  next
    case False
      consider ib ob where "op = UnaryNarrow ib ob" |
               ib ob where "op = UnaryZeroExtend ib ob" |
               ib ob where "op = UnarySignExtend ib ob"
        by (metis \<open>(op::IRUnaryOp) \<notin> normal_unary\<close> False IRUnaryOp.exhaust insert_iff)
  then show ?thesis
  proof (cases)
    case 1
    then show ?thesis
      apply auto
      by (smt (verit, del_insts) new_int.elims def intval_narrow.elims unary_eval.simps(5))
  next
    case 2
    then show ?thesis
      apply auto
      by (smt (verit, del_insts) new_int.elims def intval_zero_extend.elims unary_eval.simps(7))
  next
    case 3
    then show ?thesis
      apply auto
      by (smt (verit, del_insts) new_int.elims def intval_sign_extend.elims unary_eval.simps(6))
  qed
 qed
qed

lemma new_int_unused_bits_zero:
  assumes "IntVal b ival = new_int b ival0"
  shows "take_bit b ival = ival"
  by (simp add: new_int_take_bits assms)

lemma unary_eval_unused_bits_zero:
  assumes "unary_eval op x = IntVal b ival"
  shows "take_bit b ival = ival" 
  by (metis unary_eval_new_int Value.inject(1) new_int.elims new_int_unused_bits_zero Value.simps(5)
      assms)

lemma bin_eval_unused_bits_zero:
  assumes "bin_eval op x y = (IntVal b ival)"
  shows "take_bit b ival = ival"
  by (metis bin_eval_new_int Value.distinct(1) Value.inject(1) new_int.elims new_int_take_bits 
      assms) 

lemma eval_unused_bits_zero:
  "[m,p] \<turnstile> xe \<mapsto> (IntVal b ix) \<Longrightarrow> take_bit b ix = ix"
proof (induction xe)
  case (UnaryExpr x1 xe)
  then show ?case 
    by (auto simp add: unary_eval_unused_bits_zero)
next
  case (BinaryExpr x1 xe1 xe2)
  then show ?case
    by (auto simp add: bin_eval_unused_bits_zero)
next
  case (ConditionalExpr xe1 xe2 xe3)
  then show ?case
    by (metis (full_types) EvalTreeE(3))
next
  case (ParameterExpr i s)
  then have "valid_value (p!i) s"
    by fastforce
  then show ?case
    by (metis Value.distinct(7) intval_bits.simps valid_value.elims(2) local.ParameterExpr
        ParameterExprE intval_word.simps) 
next
  case (LeafExpr x1 x2)
  then show ?case
    by (smt (z3) EvalTreeE(6) Value.simps(11) valid_value.elims(1) valid_value.simps(1)) 
next
  case (ConstantExpr x)
  then show ?case 
    by (metis EvalTreeE(1) constantAsStamp.simps(1) valid_value.simps(1) wf_value_def)
next
  case (ConstantVar x)
  then show ?case
    by auto
next
  case (VariableExpr x1 x2)
  then show ?case
    by auto
qed

lemma unary_normal_bitsize:
  assumes "unary_eval op x = IntVal b ival"
  assumes "op \<in> normal_unary"
  shows "\<exists> ix. x = IntVal b ix"
  using assms apply (cases op; auto)
  by (smt (verit) Value.distinct(1) Value.sel(1) new_int.simps intval_abs.elims intval_negate.elims 
      intval_not.elims intval_logic_negation.elims)+

lemma unary_not_normal_bitsize:
  assumes "unary_eval op x = IntVal b ival"
  assumes "op \<notin> normal_unary \<and> op \<notin> boolean_unary"
  shows "b = ir_resultBits op \<and> 0 < b \<and> b \<le> 64"
  apply (cases op) prefer 8 using assms apply blast+  (* the normal_unary and boolean_unary cases *)
  by (smt(verit) Value.distinct(1) assms(1) intval_bits.simps intval_narrow.elims intval_narrow_ok
      intval_zero_extend.elims linorder_not_less neq0_conv new_int.simps unary_eval.simps(5,6,7) 
      IRUnaryOp.sel(4,5,6) intval_sign_extend.elims)+

lemma unary_eval_bitsize:
  assumes "unary_eval op x = IntVal b ival"
  assumes 2: "x = IntVal bx ix"
  assumes "0 < bx \<and> bx \<le> 64"
  shows "0 < b \<and> b \<le> 64"
proof (cases "op \<in> normal_unary")
  case True
  then obtain tmp where "unary_eval op x = new_int bx tmp"
    by (cases op; simp; auto simp: 2)
  then show ?thesis
    using assms by simp
next
  case False
  then show ?thesis
  proof (cases "op \<in> boolean_unary")
    case True
    then show ?thesis
      using assms by (cases op; simp)+
  next
    case False
    then obtain tmp where "unary_eval op x = new_int b tmp \<and> 0 < b \<and> b \<le> 64"
     using \<open>(op::IRUnaryOp) \<notin> normal_unary\<close> apply (cases op; simp; auto simp: 2) 
     by (smt (verit) Value.simps(5) assms intval_bits.simps order_less_le_trans new_int.simps
         intval_zero_extend.simps(1) unary_eval.simps(5,6,7) intval_narrow_ok intval_narrow.simps(1)
         intval_sign_extend.elims)+
  then show ?thesis
    by simp 
 qed 
qed

(*
lemma unary2:
  assumes "[m,p] \<turnstile> xe \<mapsto> IntVal b ix \<Longrightarrow> 0 < b \<and> b \<le> 64"
  assumes "[m,p] \<turnstile> UnaryExpr op xe \<mapsto> IntVal b ix"
  shows "0 < b \<and> b \<le> 64"
*)

lemma bin_eval_inputs_are_ints:
  assumes "bin_eval op x y = IntVal b ix"
  obtains xb yb xi yi where "x = IntVal xb xi \<and> y = IntVal yb yi"
proof -
  have "bin_eval op x y \<noteq> UndefVal"
    by (simp add: assms)
  then show ?thesis
    using assms that by (cases op; cases x; cases y; auto)
qed

lemma eval_bits_1_64:
  "[m,p] \<turnstile> xe \<mapsto> (IntVal b ix) \<Longrightarrow> 0 < b \<and> b \<le> 64"
proof (induction xe arbitrary: "b" "ix")
  case (UnaryExpr op x2)
  then obtain xv where 
       xv: "([m,p] \<turnstile> x2 \<mapsto> xv) \<and>
            IntVal b ix = unary_eval op xv"
    by (auto simp add: unfold_binary)
  then have "b = (if op \<in> normal_unary  then intval_bits xv else 
                  if op \<in> boolean_unary then 32 else 
                                             ir_resultBits op)"
    by (metis Value.disc(1) Value.discI(1) Value.sel(1) new_int.simps unary_eval_new_int)
  then show ?case
    by (metis xv linorder_le_cases linorder_not_less numeral_less_iff semiring_norm(76,78) gr0I 
        unary_normal_bitsize unary_not_normal_bitsize UnaryExpr.IH)
next
  case (BinaryExpr op x y)
  then obtain xv yv where 
       xy: "([m,p] \<turnstile> x \<mapsto> xv) \<and>
            ([m,p] \<turnstile> y \<mapsto> yv) \<and>
            IntVal b ix = bin_eval op xv yv"
    by (auto simp add: unfold_binary)
  then have def: "bin_eval op xv yv \<noteq> UndefVal" and xv: "xv \<noteq> UndefVal" and "yv \<noteq> UndefVal"
    using evaltree_not_undef xy by (force, blast, blast)
  then have "b = (if op \<in> binary_fixed_32_ops then 32 else intval_bits xv)" 
    by (metis xy intval_bits.simps new_int.simps bin_eval_new_int) 
  then show ?case
    by (metis BinaryExpr.IH(1) Value.distinct(7,9) xv bin_eval_inputs_are_ints intval_bits.elims 
        le_add_same_cancel1 less_or_eq_imp_le numeral_Bit0 xy zero_less_numeral)
next
  case (ConditionalExpr xe1 xe2 xe3)
  then show ?case
    by (metis (full_types) EvalTreeE(3))
next
  case (ParameterExpr x1 x2)
  then show ?case
    by (metis (no_types, lifting) valid_value.elims(2) valid_value.simps(17) intval_bits.simps
        valid_stamp.simps(1) ParameterExprE)
next
  case (LeafExpr x1 x2)
  then show ?case
    by (smt (z3) Value.distinct(7) Value.inject(1) valid_stamp.simps(1) valid_value.elims(1) 
        EvalTreeE(6))
next
  case (ConstantExpr x)
  then show ?case 
    by (metis wf_value_def constantAsStamp.simps(1) valid_stamp.simps(1) valid_value.simps(1)
        EvalTreeE(1))
next
  case (ConstantVar x)
  then show ?case
    by auto 
next
  case (VariableExpr x1 x2)
  then show ?case
    by auto
qed

lemma unfold_binary_width:
  assumes "op \<notin> binary_fixed_32_ops \<and> op \<notin> binary_shift_ops \<and> op \<notin> binary_fixed_ops"
  shows "([m,p] \<turnstile> BinaryExpr op xe ye \<mapsto> IntVal b val) = (\<exists> x y.
          (([m,p] \<turnstile> xe \<mapsto> IntVal b x) \<and>
           ([m,p] \<turnstile> ye \<mapsto> IntVal b y) \<and>
           (IntVal b val = bin_eval op (IntVal b x) (IntVal b y)) \<and>
           (IntVal b val \<noteq> UndefVal)
        ))" (is "?L = ?R")
proof (intro iffI)
  assume 3: ?L
  show ?R 
    apply (rule evaltree.cases[OF 3]) apply auto
    subgoal premises p for x y
    proof (cases op)
      case BinAdd
      then show ?thesis
        using assms apply auto
        by (smt (verit) Value.inject(1) bin_eval.simps(1) bin_eval_inputs_are_ints p
            intval_add.simps(1))
    next
      case BinMul
      then show ?thesis
        using assms apply auto
        by (smt (verit) Value.inject(1) bin_eval.simps(2) intval_mul.elims new_int.elims p
            new_int_bin.simps)
    next
      case BinSub
      then show ?thesis
        using assms apply auto
        by (smt (verit) Value.inject(1) bin_eval.simps(3) intval_sub.elims new_int.elims p
            new_int_bin.simps)
    next
      case BinAnd
      then show ?thesis
        using assms apply auto
        by (smt (z3) BinAnd bin_eval.simps(4) bin_eval_inputs_are_ints intval_and.simps(1)
            p(1,2,3,4) Value.inject(1) take_bit_and intval_and.elims new_int_bin.simps
            new_int.simps)
    next
      case BinOr
      then show ?thesis
        using assms apply auto
        by (smt (verit) bin_eval.simps(5) intval_bits.simps intval_or.elims new_int.simps p
            new_int_bin.simps take_bit_or)
    next
      case BinXor
      then show ?thesis
        using assms apply auto
        by (smt (verit) Value.inject(1) bin_eval.simps(6) intval_xor.elims new_int.elims p
            new_int_bin.simps take_bit_xor)
    next
      case BinShortCircuitOr
      then show ?thesis
        using assms by auto
    next
      case BinLeftShift
      then show ?thesis
        using assms by blast
    next
      case BinRightShift
      then show ?thesis
        using assms by blast
    next
      case BinURightShift
      then show ?thesis
        using assms by blast
    next
      case BinIntegerEquals
      then show ?thesis
        using assms by blast
    next
      case BinIntegerLessThan
      then show ?thesis
        using assms by blast
    next
      case BinIntegerBelow
      then show ?thesis
        using assms by blast
    next
      case BinIntegerTest
      then show ?thesis
        using assms by blast
    next
      case BinIntegerNormalizeCompare
      then show ?thesis
        using assms by blast
    next
      case BinIntegerMulHigh
      then show ?thesis
        using assms by blast
    qed
    done
next
  assume R: ?R
  then obtain x y where "[m,p] \<turnstile> xe \<mapsto> IntVal b x"
        and "[m,p] \<turnstile> ye \<mapsto> IntVal b y"
        and "new_int b val = bin_eval op (IntVal b x) (IntVal b y)"
        and "new_int b val \<noteq> UndefVal"
    using bin_eval_unused_bits_zero by force
  then show ?L 
    using R by blast
qed

end
