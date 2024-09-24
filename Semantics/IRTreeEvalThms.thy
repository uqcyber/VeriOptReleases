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
  "[m,p] \<turnstile> e [\<mapsto>] v1 \<Longrightarrow> 
   [m,p] \<turnstile> e [\<mapsto>] v2 \<Longrightarrow>
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

lemma unary_eval_not_array:
  shows "unary_eval op x \<noteq> ArrayVal len v"
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
  by (cases "unary_eval op x"; auto simp add: assms unary_eval_not_obj_ref unary_eval_not_obj_str
      unary_eval_not_array)

lemma bin_eval_int:
  assumes "bin_eval op x y \<noteq> UndefVal"
  shows "is_IntVal (bin_eval op x y)" 
  using assms
  apply (cases op; cases x; cases y; auto simp add: is_IntVal_def)
  apply presburger+ (* prove 6 more easy cases *)
  prefer 3 prefer 4
     apply (smt (verit, del_insts) new_int.simps)
                      apply (smt (verit, del_insts) new_int.simps)
                      apply (meson new_int_bin.simps)+
                      apply (meson bool_to_val.elims)
                      apply (meson bool_to_val.elims)
                     apply (smt (verit, del_insts) new_int.simps)+
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
  case BinDiv
  then show ?thesis
    using assms apply (cases x; cases y; auto)
    by (meson new_int_bin.simps)
next
  case BinMod
  then show ?thesis
    using assms apply (cases x; cases y; auto)
    by (meson new_int_bin.simps)
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
    by (metis IntVal0 IntVal1 bool_to_val.elims new_int.elims)+
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

lemma min_int_bit_bounds:
  assumes "0 < b \<and> b \<le> 64"
  shows "(-(2 ^ (b-1))) = word_of_int (fst (bit_bounds b))"
  using assms unfolding bit_bounds.simps fst_def apply simp
  by (simp add: two_exp_div)

(*lemma min_int_bit_bounds:
  assumes "0 < b \<and> b \<le> 64"
  shows "int_signed_value b (min_int b) = (fst (bit_bounds b))"
  using assms unfolding bit_bounds.simps fst_def apply simp using min_int_signed_neg2pow two_exp_div
  sledgehammer
  by (simp add: two_exp_div)
*)

lemma take_bit_mod:
  fixes w :: "'a::len word"
  shows "take_bit b w = w mod 2 ^ b"
  using take_bit_eq_mod by blast
                  
(*
v\<open>set_bit n a = a OR push_bit n 1\<close>
    and unset_bit_eq_or_xor: \<open>unset_bit n a = (a OR push_bit n 1) XOR push_bit n 1\<close>
    and flip_bit_eq_xor: \<open>flip_bit n a = a XOR push_bit n 1\<close>
    and push_bit_eq_mult: \<open>push_bit n a = a * 2 ^ n\<close>

signed_take_bit n a = take_bit n a OR (of_bool (bit a n) * NOT (mask n))
*)
context includes bit_operations_syntax begin

value "(-1)::int64"
value "mask 64::int64"

(*
proof -
  have "set_bit (b-1) 0 = (or 0 (push_bit (b-1) 1))"
    using set_bit_eq_or by blast
  also have "... = push_bit (b-1) 1"
    using or.left_neutral by blast
  also have "... = 2 ^ (b-1)"
    using push_bit_eq_mult
    using push_bit_of_1 by blast
  ultimately have sbdef: "set_bit (b-1) 0 = 2 ^ (b-1)"
    by simp
  have "signed_take_bit (b-1) ?b = take_bit (b-1) ?b OR (of_bool (bit ?b (b-1))) * NOT (mask (b-1))"
    by (simp add: signed_take_bit_def)
  also have "bit ?b (b-1)"
    using bit_set_bit_iff
    using assms by fastforce
  ultimately have rhse:"signed_take_bit (b-1) ?b = take_bit (b-1) ?b OR (NOT (mask (b-1)))"
    using signed_take_bit_eq_if_negative by blast
  have "signed_take_bit b ?a = take_bit b ?a OR (of_bool (bit ?a b)) * NOT (mask b)"
    by (simp add: signed_take_bit_def)
  have "?a = push_bit (b-1) (-1)"
    by (simp add: min_int_def push_bit_minus)
  have "bit (mask 64::int64) (b-1)"
    using assms bit_mask_iff ValueThms.size64
    by fastforce
  also have "of_bool (bit ?a (b-1)) = 1"
    using calculation
    by (simp add: \<open>min_int (b::nat) = push_bit (b - (1::nat)) (- (1::64 word))\<close> bit_mask_iff bit_push_bit_iff minus_1_eq_mask)
  ultimately have lhse:"signed_take_bit (b-1) ?a = take_bit (b-1) ?a OR (NOT (mask (b-1)))"
    using signed_take_bit_eq_if_negative by auto
  show ?thesis using lhse rhse
    by (metis (no_types, lifting) \<open>min_int (b::nat) = push_bit (b - (1::nat)) (- (1::64 word))\<close> eq_imp_le int_signed_value.elims push_bit_minus_one_eq_not_mask take_bit_minus_one_eq_mask take_bit_not_take_bit take_bit_set_bit_eq word_bitwise_m1_simps(1))
qed
*)

lemma max_int_bit_bounds:
  assumes "0 < b \<and> b \<le> 64"
  shows "max_int b = word_of_int (snd (bit_bounds b))"
  using assms unfolding max_int_def bit_bounds.simps fst_def apply simp
  by (simp add: mask_eq_decr_exp two_exp_div)

lemma min_int_bit_bounds_signed:
  assumes "0 < b \<and> b \<le> 64"
  shows "int_signed_value b (min_int b) = int_signed_value b (word_of_int (fst (bit_bounds b)))"
  using assms unfolding min_int_def bit_bounds.simps fst_def apply simp
  using min_int_def min_int_signed_neg2pow two_exp_div by force

value "fst (bit_bounds 32)"
value "min_int 32"
value "take_bit 32 (min_int 32)"
value "sint (min_int 32)"
value "sint (take_bit 32 (min_int 32))"
value "int_signed_value 32 (set_bit 31 0::int64)"
value "int_signed_value 32 (min_int 32)"

lemma min_int_take_bit:
  assumes "0 < b \<and> b \<le> 64"
  shows "take_bit b (min_int b) = (min_int b)"
  using assms unfolding min_int_def
  by (metis diff_less linorder_not_less take_bit_of_0 take_bit_set_bit_eq zero_less_one)

lemma max_int_take_bit:
  assumes "0 < b \<and> b \<le> 64"
  shows "take_bit b (max_int b) = (max_int b)"
  using assms unfolding max_int_def
  by auto

lemma min_int_signed:
  assumes "0 < b \<and> b \<le> 64"
  shows "int_signed_value b (min_int b) = -(2 ^ (b-1))" (is "int_signed_value b ?a = _")
proof -
  have "min_int b = push_bit (b-1) 1"
    by (simp add: min_int_def set_bit_def)
  also have "... = 2 ^ (b-1)" (is "_ = ?pow")
    using push_bit_of_1 by blast
  ultimately have min_int_eq: "min_int b = ..."
    by simp
  have "signed_take_bit b ?a = take_bit b ?a OR (of_bool (bit ?a b)) * NOT (mask b)"
    by (simp add: signed_take_bit_def)
  have pb: "?a = push_bit (b-1) 1"
    by (simp add: min_int_def set_bit_def)
  have "bit (mask 64::int64) (b-1)"
    using assms bit_mask_iff ValueThms.size64
    by fastforce
  also have "of_bool (bit ?a (b-1)) = 1"
    using calculation
    by (metis (no_types, lifting) add.right_neutral bit.compl_one bit_0 bit_0_eq bit_0_eq bit_0_eq bit_decr_iff bit_not_iff bit_push_bit_iff diff_is_0_eq' even_bit_succ_iff mask_eq_exp_minus_1 negative_all_set_32 of_bool_eq_1_iff order.refl pb rel_simps(51))
  ultimately have lhse:"signed_take_bit (b-1) ?a = take_bit (b-1) ?a OR (NOT (mask (b-1)))"
    using signed_take_bit_eq_if_negative by auto
  also have "... = (NOT (mask (b-1)))"
    using take_bit_push_bit
    by (metis (no_types, lifting) cancel_comm_monoid_add_class.diff_cancel or.commute or.right_neutral pb push_bit_of_0 take_bit_0)
  ultimately have "(signed_take_bit (b - (1::nat)) (min_int b)) = - ((2) ^ (b - (1::nat)))"
    by (simp add: minus_exp_eq_not_mask)
  then show ?thesis unfolding int_signed_value.simps
    using ValueThms.upper_bounds_equiv bit_bounds.simps bit_minus_1_iff min_int_bit_bounds power_increasing_iff prod.sel(1) sint_sbintrunc'
    by (smt (verit, del_insts) One_nat_def Suc_leI Suc_pred ValueThms.signed_take_bit_int_greater_eq_minus_exp_word Word.bit_mask_iff \<open>bit (mask (64::nat)) ((b::nat) - (1::nat))\<close> assms min_less_iff_conj not_less signed_take_bit_int_less_eq_self_iff)
(*
    using One_nat_def Suc_diff_eq_diff_pred Suc_leI Suc_pred ValueThms.signed_take_bit_int_greater_eq_minus_exp_word Word.bit_mask_iff \<open>bit (mask (64::nat)) ((b::nat) - (1::nat))\<close> add.inverse_inverse assms bit_mask_iff bit_push_bit_iff bit_sint_iff diff_le_mono diff_less len_gt_0 min_less_iff_conj minus_1_eq_mask pb push_bit_minus_one_eq_not_mask signed_take_bit_eq signed_take_bit_int_eq_self_iff signed_take_bit_int_less_self_iff signed_take_bit_minus signed_take_bit_negative_iff sint_word_ariths(4) sint_word_ariths(7) take_bit_int_greater_eq take_bit_not_mask_eq_0 zero_less_one
    sledgehammer
    by (smt (verit) ValueThms.upper_bounds_equiv bit_bounds.simps bit_minus_1_iff min_int_bit_bounds power_increasing_iff prod.sel(1) sint_sbintrunc')
    by (smt (verit) ValueThms.take_bit_smaller_range diff_is_0_eq diff_le_self le_less le_numeral_extra(4) len_of_numeral_defs(2) min_int_take_bit of_bool_eq(1) power.simps(1) push_bit_of_1 signed_push_bit_eq signed_take_bit_eq_take_bit_add signed_take_bit_int_less_eq signed_take_bit_int_less_eq_self_iff signed_take_bit_int_less_exp signed_take_bit_of_0 signed_take_bit_of_minus_1 sint_word_ariths(8) take_bit_int_less_exp take_bit_of_1 take_bit_push_bit)
*)
(*
    by (smt (verit, best) One_nat_def Suc_diff_eq_diff_pred Suc_leI Suc_pred ValueThms.signed_take_bit_int_greater_eq_minus_exp_word Word.bit_mask_iff \<open>bit (mask (64::nat)) ((b::nat) - (1::nat))\<close> add.inverse_inverse assms bit_mask_iff bit_push_bit_iff bit_sint_iff diff_le_mono diff_less len_gt_0 min_less_iff_conj minus_1_eq_mask pb push_bit_minus_one_eq_not_mask signed_take_bit_eq signed_take_bit_int_eq_self_iff signed_take_bit_int_less_self_iff signed_take_bit_minus signed_take_bit_negative_iff sint_word_ariths(4) sint_word_ariths(7) take_bit_int_greater_eq take_bit_not_mask_eq_0 zero_less_one)
*)
qed

lemma max_int_signed:
  assumes "0 < b \<and> b \<le> 64"
  shows "int_signed_value b (max_int b) = (2 ^ (b-1)) - 1" (is "int_signed_value b ?a = _")
proof -
  have "signed_take_bit b ?a = take_bit b ?a OR (of_bool (bit ?a b)) * NOT (mask b)"
    by (simp add: signed_take_bit_def)
  have pb: "?a = (push_bit (b-1) (1)) - 1"
    by (simp add: mask_eq_decr_exp max_int_def)
  have "bit (mask 64::int64) (b-1)"
    using assms bit_mask_iff ValueThms.size64
    by fastforce
  also have "of_bool (bit ?a (b-1)) = 0"
    using calculation
    by (metis bit_take_bit_iff less_irrefl_nat mask_eq_exp_minus_1 max_int_def of_bool_eq_0_iff take_bit_minus_one_eq_mask)
  ultimately have lhse:"signed_take_bit (b-1) ?a = take_bit (b-1) ?a"
    by (simp add: signed_take_bit_eq_if_positive)
  then show ?thesis unfolding int_signed_value.simps
    by (smt (verit, best) JavaWords.signed_take_bit_int_less_exp_word \<open>bit (mask (64::nat)) ((b::nat) - (1::nat))\<close> bit_mask_iff bit_set_bit_iff mask_eq_exp_minus_1 mask_eq_take_bit_minus_one max_int_def not_less set_bit_eq_idem_iff signed_take_bit_eq sint_n1 take_bit_int_greater_eq_self_iff)
qed

lemma min_int_min:
  fixes ival::int64
  assumes "0 < b \<and> b \<le> 64"
  shows "b \<turnstile> (min_int b) \<le>j ival"
  using assms unfolding int_signed_value.simps
  using size64
  by (metis ValueThms.int_signed_value_range int_signed_value.simps min_int_signed)

lemma max_int_max:
  fixes ival::int64
  assumes "0 < b \<and> b \<le> 64"
  shows "b \<turnstile> ival \<le>j (max_int b)"
  using assms unfolding int_signed_value.simps
  using size64 ValueThms.int_signed_value_range int_signed_value.simps max_int_signed
  by auto
end

lemma validStampIntConst:
  assumes "v = IntVal b ival"
  assumes "0 < b \<and> b \<le> 64"
  shows "valid_stamp (constantAsStamp v)"
  using assms
  using max_int_max min_int_min by auto

lemma down_mask_constant_valid:
  assumes "d = (and v (mask b))"
  shows "(and (not v) d) = 0"
  using assms
  by (metis and.assoc bit.conj_cancel_left zero_and_eq)

lemma up_mask_constant_valid:
  assumes "u = (and v (mask b))"
  assumes "take_bit b v = v"
  shows "(and v u) = v"
  using assms
  by (simp add: take_bit_eq_mask)


lemma validDefIntConst:
  assumes v: "v = IntVal b ival"
  assumes "0 < b \<and> b \<le> 64"
  assumes "take_bit b ival = ival"
  shows "valid_value v (constantAsStamp v)"
  using assms min_int_min max_int_max down_mask_constant_valid up_mask_constant_valid
  by (simp add: take_bit_eq_mask)


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
  by simp

lemma valid_ObjStamp[elim]:
  shows "valid_value val (ObjectStamp klass exact nonNull alwaysNull) \<Longrightarrow> (\<exists>v. val = ObjRef v)"
  by (metis Value.exhaust valid_value.simps(3,11,12,18))

lemma valid_int[elim]:
  shows "valid_value val (IntegerStamp b lo hi d u) \<Longrightarrow> (\<exists>v. val = IntVal b v)"
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
  assumes "[m,p] \<turnstile> LeafExpr i (IntegerStamp b lo hi d u) \<mapsto> val"
  shows "\<exists>b v. val = (IntVal b v)"
(* Note: we could also add: ...\<and> lo \<le> sint v \<and> sint v \<le> hi *)
proof - 
  have "valid_value val (IntegerStamp b lo hi d u)"
    using assms by (rule LeafExprE; simp)
  then show ?thesis
    by auto
qed

value "default_stamp"
(*
value "mask 32::int64"
lemma default_stamp [simp]: "default_stamp = IntegerStamp 32 (18446744071562067968) 2147483647 0 4294967295"
  by (auto simp add: default_stamp_def)
*)

lemma valid_value_signed_int_range [simp]:
  assumes "valid_value val (IntegerStamp b lo hi d u)"
  assumes "lo < 0"
  shows "\<exists>v. (val = IntVal b v \<and> 
             (b \<turnstile> lo \<le>j v) \<and> 
             (b \<turnstile> v \<le>j hi))"
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
              
          b = (if op \<in> normal_unary       then intval_bits x  else
               if op \<in> boolean_unary      then 32             else
               if op \<in> unary_fixed_32_ops then 32             else
                                          ir_resultBits op))"
proof (cases op)
  case UnaryAbs
  then show ?thesis
    apply auto
    by (metis intval_bits.simps intval_abs.simps(1) UnaryAbs def new_int.elims unary_eval.simps(1)
        intval_abs.elims)
next
  case UnaryNeg
  then show ?thesis
    apply auto
    by (metis def intval_bits.simps intval_negate.elims new_int.elims unary_eval.simps(2))
next
  case UnaryNot
  then show ?thesis
    apply auto
    by (metis intval_bits.simps intval_not.elims new_int.simps unary_eval.simps(3) def)
next
  case UnaryLogicNegation
  then show ?thesis
    apply auto
    by (metis intval_bits.simps UnaryLogicNegation intval_logic_negation.elims new_int.elims def
        unary_eval.simps(4))
next
  case (UnaryNarrow x51 x52)
  then show ?thesis
    using assms apply auto
    subgoal premises p
    proof -
      obtain xb xvv where xvv: "x = IntVal xb xvv"
        by (metis UnaryNarrow def intval_logic_negation.cases intval_narrow.simps(2,3,4,5)
            unary_eval.simps(5))
      then have evalNotUndef: "intval_narrow x51 x52 x \<noteq> UndefVal"
        using p by fast
      then show ?thesis
        by (metis (no_types, lifting) new_int.elims intval_narrow.simps(1) xvv)
    qed done
next
  case (UnarySignExtend x61 x62)
  then show ?thesis
    using assms apply auto
    subgoal premises p
    proof -
      obtain xb xvv where xvv: "x = IntVal xb xvv"
        by (metis Value.exhaust intval_sign_extend.simps(2,3,4,5) p(2))
      then have evalNotUndef: "intval_sign_extend x61 x62 x \<noteq> UndefVal"
        using p by fast
      then show ?thesis
        by (metis intval_sign_extend.simps(1) new_int.elims xvv)
    qed done
next
  case (UnaryZeroExtend x71 x72)
  then show ?thesis
    using assms apply auto
    subgoal premises p
    proof -
      obtain xb xvv where xvv: "x = IntVal xb xvv"
        by (metis Value.exhaust intval_zero_extend.simps(2,3,4,5) p(2))
      then have evalNotUndef: "intval_zero_extend x71 x72 x \<noteq> UndefVal"
        using p by fast
      then show ?thesis
        by (metis intval_zero_extend.simps(1) new_int.elims xvv)
    qed done
next
  case UnaryIsNull
  then show ?thesis
    apply auto
    by (metis bool_to_val.simps(1) new_int.simps IntVal0 IntVal1 unary_eval.simps(8) assms def
        intval_is_null.elims bool_to_val.elims)
next
  case UnaryReverseBytes
  then show ?thesis
    apply auto
    by (metis intval_bits.simps intval_reverse_bytes.elims new_int.elims unary_eval.simps(9) def)
next
  case UnaryBitCount
  then show ?thesis
    apply auto
    by (metis intval_bit_count.elims new_int.simps unary_eval.simps(10) intval_bit_count.simps(1)
        def)
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
  then show ?case using ParameterExprE Value.simps(14) intval_bits.simps intval_word.simps local.ParameterExpr valid_value.elims(2)
    apply simp
    by (smt (z3) Value.distinct(9) Value.inject(1))
next
  case (LeafExpr x1 x2)
  then show ?case using LeafExprE intval_bits.simps Value.distinct(9) intval_word.simps valid_value.elims(2)
    apply simp
    by (smt (z3) Value.distinct(9) intval_bits.simps intval_word.simps)
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
  using assms apply (cases op; auto) prefer 5
  apply (smt (verit, ccfv_threshold) Value.distinct(1) Value.inject(1) intval_reverse_bytes.elims
      new_int.simps)
  by (metis Value.distinct(1) Value.inject(1) intval_logic_negation.elims new_int.simps
      intval_not.elims intval_negate.elims intval_abs.elims)+

lemma unary_not_normal_bitsize:
  assumes "unary_eval op x = IntVal b ival"
  assumes "op \<notin> normal_unary \<and> op \<notin> boolean_unary \<and> op \<notin> unary_fixed_32_ops"
  shows "b = ir_resultBits op \<and> 0 < b \<and> b \<le> 64"
  apply (cases op) prefer 8 prefer 10 prefer 10 using assms apply blast+  (* the normal_unary and boolean_unary cases *)
  by (smt(verit, ccfv_SIG) Value.distinct(1) assms(1) intval_bits.simps intval_narrow.elims
      intval_narrow_ok intval_zero_extend.elims linorder_not_less neq0_conv new_int.simps
      unary_eval.simps(5,6,7) IRUnaryOp.sel(4,5,6) intval_sign_extend.elims)+

lemma unary_eval_bitsize:
  assumes "unary_eval op x = IntVal b ival"
  assumes 2: "x = IntVal bx ix"
  assumes "0 < bx \<and> bx \<le> 64"
  shows "0 < b \<and> b \<le> 64"
  using assms apply (cases op; simp)
  by (metis Value.distinct(1) Value.inject(1) intval_narrow.simps(1) le_zero_eq intval_narrow_ok
      new_int.simps le_zero_eq gr_zeroI)+

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
  then have "b = (if op \<in> normal_unary       then intval_bits xv else
                  if op \<in> unary_fixed_32_ops then 32             else
                  if op \<in> boolean_unary      then 32             else
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
    by (smt (verit, best) Value.distinct(9,11,13) BinaryExpr.IH(1) xv bin_eval_inputs_are_ints xy
        intval_bits.elims le_add_same_cancel1 less_or_eq_imp_le numeral_Bit0 zero_less_numeral)
next
  case (ConditionalExpr xe1 xe2 xe3)
  then show ?case
    by (metis (full_types) EvalTreeE(3))
next
  case (ParameterExpr x1 x2)
  then show ?case
    apply auto
    using valid_value.elims(2)
    by (metis valid_stamp.simps(1) intval_bits.simps valid_value.simps(18))+
next
  case (LeafExpr x1 x2)
  then show ?case
    apply auto
    using valid_value.elims(1,2)
    by (metis Value.inject(1) valid_stamp.simps(1) valid_value.simps(18) Value.distinct(9))+
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


lemma bin_eval_normal_bits:
  assumes "op \<in> binary_normal"
  assumes "bin_eval op x y = xy"
  assumes "xy \<noteq> UndefVal"
  shows "\<exists>xv yv xyv b. (x = IntVal b xv \<and> y = IntVal b yv \<and> xy = IntVal b xyv)"
  using assms apply simp
  proof (cases "op \<in> binary_normal")
  case True
  then show ?thesis
    proof -
      have operator: "xy = bin_eval op x y"
        by (simp add: assms(2))
      obtain xv xb where xv: "x = IntVal xb xv"
        by (metis assms(3) bin_eval_inputs_are_ints bin_eval_int is_IntVal_def operator)
      obtain yv yb where yv: "y = IntVal yb yv"
        by (metis assms(3) bin_eval_inputs_are_ints bin_eval_int is_IntVal_def operator)
      then have notUndefMeansWidthSame: "bin_eval op x y \<noteq> UndefVal \<Longrightarrow> (xb = yb)"
        using assms apply (cases op; auto)
        by (metis intval_xor.simps(1) intval_or.simps(1) intval_div.simps(1) intval_mod.simps(1) intval_and.simps(1) intval_sub.simps(1)
            intval_mul.simps(1) intval_add.simps(1) new_int_bin.elims xv)+
      then have inWidthsSame: "xb = yb"
        using assms(3) operator by auto
      obtain ob xyv where out: "xy = IntVal ob xyv"
        by (metis Value.collapse(1) assms(3) bin_eval_int operator)
      then have "yb = ob"
        using assms apply (cases op; auto)
           apply (simp add: inWidthsSame xv yv)+
           apply (metis assms(3) intval_bits.simps new_int.simps new_int_bin.elims)
           apply (metis xv yv Value.distinct(1) intval_mod.simps(1) new_int.simps new_int_bin.elims)
          by (simp add: inWidthsSame xv yv)+
      then show ?thesis
      using xv yv inWidthsSame assms out by blast
  qed
next
  case False
  then show ?thesis
    using assms by simp
qed

lemma unfold_binary_width_bin_normal:
  assumes "op \<in> binary_normal"
  shows "\<And>xv yv.
           IntVal b val = bin_eval op xv yv \<Longrightarrow>
           [m,p] \<turnstile> xe \<mapsto> xv \<Longrightarrow>
           [m,p] \<turnstile> ye \<mapsto> yv \<Longrightarrow>
           bin_eval op xv yv \<noteq> UndefVal \<Longrightarrow>
           \<exists>xa.
           (([m,p] \<turnstile> xe \<mapsto> IntVal b xa) \<and>
            (\<exists>ya. (([m,p] \<turnstile> ye \<mapsto> IntVal b ya) \<and>
              bin_eval op xv yv = bin_eval op (IntVal b xa) (IntVal b ya))))"
  using assms apply simp
  subgoal premises p for x y
  proof -
    obtain xv yv where eval: "([m,p] \<turnstile> xe \<mapsto> xv) \<and> ([m,p] \<turnstile> ye \<mapsto> yv)"
      using p(2,3) by blast
    then obtain xa bb where xa: "xv = IntVal bb xa"
      by (metis bin_eval_inputs_are_ints evalDet p(1,2))
    then obtain ya yb where ya: "yv = IntVal yb ya"
      by (metis bin_eval_inputs_are_ints evalDet p(1,3) eval)
    then have eqWidth: "bb = b"
      by (metis intval_bits.simps p(1,2,4) assms eval xa bin_eval_normal_bits evalDet)
    then obtain xy where eval0: "bin_eval op x y = IntVal b xy"
      by (metis p(1))
    then have sameVals: "bin_eval op x y = bin_eval op xv yv"
      by (metis evalDet p(2,3) eval)
    then have notUndefMeansSameWidth: "bin_eval op xv yv \<noteq> UndefVal \<Longrightarrow> (bb = yb)"
      using assms apply (cases op; auto)
      by (metis intval_add.simps(1) intval_mul.simps(1) intval_div.simps(1) intval_mod.simps(1) intval_sub.simps(1) intval_and.simps(1)
          intval_or.simps(1) intval_xor.simps(1) new_int_bin.simps xa ya)+
    have unfoldVal: "bin_eval op x y = bin_eval op (IntVal bb xa) (IntVal yb ya)"
      unfolding sameVals xa ya by simp
    then have sameWidth: "b = yb"
      using eqWidth notUndefMeansSameWidth p(4) sameVals by force
    then show ?thesis
      using eqWidth eval xa ya unfoldVal by blast
  qed
  done

lemma unfold_binary_width:
  assumes "op \<in> binary_normal"
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
    apply (cases "op \<in> binary_normal")
    using unfold_binary_width_bin_normal assms by force+
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
