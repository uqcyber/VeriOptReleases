subsection \<open>Evaluation Stamp Theorems\<close>

theory StampEvalThms
  imports Graph.ValueThms
          Semantics.IRTreeEvalThms
begin

lemma
  assumes "take_bit b v = v"
  shows "signed_take_bit b v = v"
  by (metis(full_types) eq_imp_le signed_take_bit_take_bit assms)

lemma unwrap_signed_take_bit:
  fixes v :: int64
  assumes "0 < b \<and> b \<le> 64"
  assumes "signed_take_bit (b - 1) v = v"
  shows "signed_take_bit 63 (Word.rep (signed_take_bit (b - Suc 0) v)) = sint v"
  using assms by (simp add: signed_def)

lemma unrestricted_new_int_always_valid [simp]:
  assumes "0 < b \<and> b \<le> 64"
  shows "valid_value (new_int b v) (unrestricted_stamp (IntegerStamp b lo hi))"
  by (simp; metis One_nat_def assms int_power_div_base int_signed_value.simps int_signed_value_range
      linorder_not_le not_exp_less_eq_0_int zero_less_numeral)

lemma unary_undef: "val = UndefVal \<Longrightarrow> unary_eval op val = UndefVal"
  by (cases op; auto)

lemma unary_obj: 
  "val = ObjRef x \<Longrightarrow> (if (op = UnaryIsNull) then 
                           unary_eval op val \<noteq> UndefVal else 
                           unary_eval op val = UndefVal)"
  by (cases op; auto)

lemma unrestricted_stamp_valid:
  assumes "s = unrestricted_stamp (IntegerStamp b lo hi)"
  assumes "0 < b \<and> b \<le> 64"
  shows "valid_stamp s"
  by (smt (z3) Stamp.inject(1) bit_bounds.simps not_exp_less_eq_0_int prod.sel(1,2) assms
      unrestricted_stamp.simps(2) upper_bounds_equiv valid_stamp.elims(1))

lemma unrestricted_stamp_valid_value [simp]:
  assumes 1: "result = IntVal b ival"
  assumes "take_bit b ival = ival"
  assumes "0 < b \<and> b \<le> 64"
  shows "valid_value result (unrestricted_stamp (IntegerStamp b lo hi))"
proof -
  have "valid_stamp (unrestricted_stamp (IntegerStamp b lo hi))"
    using assms unrestricted_stamp_valid by blast 
  then show ?thesis
    unfolding unrestricted_stamp.simps using assms int_signed_value_bounds valid_value.simps
    by presburger
qed


(* TODO: update to allow any bit size? 
lemma unrestricted_stamp32_always_valid [simp]:
  assumes "fst (bit_bounds bits) \<le> sint ival \<and> sint ival \<le> snd (bit_bounds bits)"
  assumes "bits = 32 \<or> bits = 16 \<or> bits = 8 \<or> bits = 1"
  assumes "result = IntVal32 ival"
  shows "valid_value result (unrestricted_stamp (IntegerStamp bits lo hi))"
  using assms valid_value.simps(1) unrestricted_stamp.simps(2) by presburger

lemma larger_stamp32_always_valid [simp]:
  assumes "valid_value result (unrestricted_stamp (IntegerStamp inBits lo hi))"
  assumes "result = IntVal32 ival"
  assumes "outBits = 32 \<or> outBits = 16 \<or> outBits = 8 \<or> outBits = 1"
  assumes "inBits \<le> outBits"
  shows "valid_value result (unrestricted_stamp (IntegerStamp outBits lo hi))"
  using assms by (smt (z3)  bit_bounds.simps diff_le_mono linorder_not_less lower_bounds_equiv not_numeral_le_zero numerals(1) power_increasing_iff prod.sel(1) prod.sel(2) unrestricted_stamp.simps(2) valid_value.simps(1))
*)



subsubsection \<open>Support Lemmas for Integer Stamps and Associated IntVal values\<close>
(* TODO: these do not use eval so could go up into a StampThms.thy? *)

text \<open>Valid int implies some useful facts.\<close>
lemma valid_int_gives:
  assumes "valid_value (IntVal b val) stamp"
  obtains lo hi where "stamp = IntegerStamp b lo hi \<and>
       valid_stamp (IntegerStamp b lo hi) \<and>
       take_bit b val = val \<and>
       lo \<le> int_signed_value b val \<and> int_signed_value b val \<le> hi"
  by (smt (z3) Value.distinct(7) Value.inject(1) valid_value.elims(1) assms)

text \<open>And the corresponding lemma where we know the stamp rather than the value.\<close>
lemma valid_int_stamp_gives:
  assumes "valid_value val (IntegerStamp b lo hi)"
  obtains ival where "val = IntVal b ival \<and>
       valid_stamp (IntegerStamp b lo hi) \<and>
       take_bit b ival = ival \<and>
       lo \<le> int_signed_value b ival \<and> int_signed_value b ival \<le> hi"
  by (metis assms valid_int valid_value.simps(1))

text \<open>A valid int must have the expected number of bits.\<close>
lemma valid_int_same_bits:
  assumes "valid_value (IntVal b val) (IntegerStamp bits lo hi)"
  shows "b = bits"
  by (meson assms valid_value.simps(1))

text \<open>A valid value means a valid stamp.\<close>
lemma valid_int_valid_stamp:
  assumes "valid_value (IntVal b val) (IntegerStamp bits lo hi)"
  shows "valid_stamp (IntegerStamp bits lo hi)"
  by (metis assms valid_value.simps(1))

text \<open>A valid int means a valid non-empty stamp.\<close>
lemma valid_int_not_empty:
  assumes "valid_value (IntVal b val) (IntegerStamp bits lo hi)"
  shows "lo \<le> hi"
  by (metis assms order.trans valid_value.simps(1))

text \<open>A valid int fits into the given number of bits (and other bits are zero).\<close>
lemma valid_int_fits:
  assumes "valid_value (IntVal b val) (IntegerStamp bits lo hi)"
  shows "take_bit bits val = val"
  by (metis assms valid_value.simps(1))

lemma valid_int_is_zero_masked:
  assumes "valid_value (IntVal b val) (IntegerStamp bits lo hi)"
  shows "and val (not (mask bits)) = 0"
  by (metis (no_types, lifting) assms bit.conj_cancel_right take_bit_eq_mask valid_int_fits 
      word_bw_assocs(1) word_log_esimps(1))

text \<open>Unsigned ints have bounds $0$ up to $2^bits$.\<close>
lemma valid_int_unsigned_bounds:
  assumes "valid_value (IntVal b val) (IntegerStamp bits lo hi)"
  (* Not actually needed: assumes "0 \<le> lo" *)
  shows "uint val < 2 ^ bits"
  by (metis assms(1) mask_eq_iff take_bit_eq_mask valid_value.simps(1))

text \<open>Signed ints have the usual two-complement bounds.\<close>
lemma valid_int_signed_upper_bound:
  assumes "valid_value (IntVal b val) (IntegerStamp bits lo hi)"
  shows "int_signed_value bits val < 2 ^ (bits - 1)"
  by (metis (mono_tags, opaque_lifting) diff_le_mono int_signed_value.simps less_imp_diff_less
      linorder_not_le one_le_numeral order_less_le_trans signed_take_bit_int_less_exp_word sint_lt
      power_increasing)

lemma valid_int_signed_lower_bound:
  assumes "valid_value (IntVal b val) (IntegerStamp bits lo hi)"
  shows "-(2 ^ (bits - 1)) \<le> int_signed_value bits val"
  by (smt (verit) diff_le_self int_signed_value.simps linorder_not_less power_increasing_iff
      signed_take_bit_int_greater_eq_minus_exp_word sint_greater_eq)

text \<open>and $bit\_bounds$ versions of the above bounds.\<close>
lemma valid_int_signed_upper_bit_bound:
  assumes "valid_value (IntVal b val) (IntegerStamp bits lo hi)"
  shows "int_signed_value bits val \<le> snd (bit_bounds bits)"
proof - 
  have "b = bits"
    using assms valid_int_same_bits by blast
  then show ?thesis 
    using assms by auto
qed

lemma valid_int_signed_lower_bit_bound:
  assumes "valid_value (IntVal b val) (IntegerStamp bits lo hi)"
  shows " fst (bit_bounds bits) \<le> int_signed_value bits val"
proof - 
  have "b = bits"
    using assms valid_int_same_bits by blast
  then show ?thesis
    using assms by auto
qed

text \<open>Valid values satisfy their stamp bounds.\<close>

lemma valid_int_signed_range:
  assumes "valid_value (IntVal b val) (IntegerStamp bits lo hi)"
  shows "lo \<le> int_signed_value bits val \<and> int_signed_value bits val \<le> hi"
  by (metis assms valid_value.simps(1))

subsubsection \<open>Validity of all Unary Operators\<close>

text \<open>We split the validity proof for unary operators into two lemmas,
  one for normal unary operators whose output bits equals their input bits,
  and the other case for the widen and narrow operators.\<close>

lemma eval_normal_unary_implies_valid_value:
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  assumes "result = unary_eval op val"
  assumes op: "op \<in> normal_unary"
  assumes notbool: "op \<notin> boolean_unary"
  assumes "result \<noteq> UndefVal"
  assumes "valid_value val (stamp_expr expr)"
  shows "valid_value result (stamp_expr (UnaryExpr op expr))"
proof -
  obtain b1 v1 where v1: "val = IntVal b1 v1"
    by (metis Value.exhaust_sel assms(2,5,6) notbool singleton_iff unary_obj valid_value.simps(3,11))
  then obtain b2 v2 where v2: "result = IntVal b2 v2"
    by (metis Value.exhaust assms(2,5) unary_eval_not_obj_ref unary_eval_not_obj_str)
  then have "result = unary_eval op (IntVal b1 v1)"
    using assms(2) v1 by blast
  then obtain vtmp where vtmp: "result = new_int b2 vtmp"
    using assms(3) by (auto simp add: v2)
  obtain b' lo' hi' where "stamp_expr expr = IntegerStamp b' lo' hi'"
    by (metis assms(6) v1 valid_int_gives)
  then have "stamp_unary op (stamp_expr expr) =
    unrestricted_stamp
     (IntegerStamp (if op \<in> normal_unary then b' else ir_resultBits op) lo' hi')"
    using op by force
  then obtain lo2 hi2 where s: "(stamp_expr (UnaryExpr op expr)) = unrestricted_stamp (IntegerStamp b2 lo2 hi2)"
    unfolding stamp_expr.simps 
    by (metis (full_types) assms(2,6) unary_normal_bitsize v2 valid_int_same_bits op
        \<open>stamp_expr (expr::IRExpr) = IntegerStamp (b'::nat) (lo'::int) (hi'::int)\<close>)
  then have "0 < b1 \<and> b1 \<le> 64"
    using assms(1) eval_bits_1_64 v1 by blast
  then have "fst (bit_bounds b2) \<le> int_signed_value b2 v2 \<and>
             int_signed_value b2 v2 \<le> snd (bit_bounds b2)"
    using assms(2) int_signed_value_bounds unary_eval_bitsize v1 v2 by blast
  then show ?thesis
    by (smt (verit) \<open>(0::nat) < (b1::nat) \<and> b1 \<sqsubseteq> (64::nat)\<close> assms(2) new_int_unused_bits_zero s v1
        unary_eval_bitsize v2 valid_stamp.simps(1) vtmp valid_value.simps unrestricted_stamp.simps)
qed

lemma narrow_widen_output_bits:
  assumes "unary_eval op val \<noteq> UndefVal"
  assumes "op \<notin> normal_unary"
  assumes "op \<notin> boolean_unary"
  shows "0 < (ir_resultBits op) \<and> (ir_resultBits op) \<le> 64"
proof -
  consider ib ob where "op = UnaryNarrow ib ob"
         | ib ob where "op = UnarySignExtend ib ob"
         | ib ob where "op = UnaryZeroExtend ib ob"
    using IRUnaryOp.exhaust_sel assms(2,3) by blast
  then show ?thesis
  proof (cases)
    case 1
    then show ?thesis
      using assms intval_narrow_ok by force
  next
    case 2
    then show ?thesis
      using assms intval_sign_extend_ok by force
  next
    case 3
    then show ?thesis
      using assms intval_zero_extend_ok by force
  qed
qed

lemma eval_widen_narrow_unary_implies_valid_value:
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  assumes "result = unary_eval op val"
  assumes op: "op \<notin> normal_unary"
  and notbool: "op \<notin> boolean_unary"
  assumes "result \<noteq> UndefVal"
  assumes "valid_value val (stamp_expr expr)"
  shows "valid_value result (stamp_expr (UnaryExpr op expr))"
proof -
  obtain b1 v1 where v1: "val = IntVal b1 v1"
    by (metis Value.exhaust_sel assms(2,5,6) insert_iff  unary_obj unary_undef valid_value.simps(11)
        notbool)
  then have "result = unary_eval op (IntVal b1 v1)"
    using assms(2) by blast
  then obtain v2 where v2: "result = new_int (ir_resultBits op) v2"
    using assms by (cases op; simp; (meson new_int.simps)+)
  then obtain v3 where v3: "result = IntVal (ir_resultBits op) v3"
    using assms by (cases op; simp; (meson new_int.simps)+)
  then obtain b lo2 hi2 where eval: "stamp_expr expr = IntegerStamp b lo2 hi2"
    by (metis assms(6) v1 valid_int_gives)
  then have s: "(stamp_expr (UnaryExpr op expr)) = unrestricted_stamp (IntegerStamp (ir_resultBits op) lo2 hi2)"
    using op notbool by (cases op; auto)
  then have outBits: "0 < (ir_resultBits op) \<and> (ir_resultBits op) \<le> 64"
    using assms narrow_widen_output_bits by blast
  then have "fst (bit_bounds (ir_resultBits op)) \<le> int_signed_value (ir_resultBits op) v3 \<and>
             int_signed_value (ir_resultBits op) v3 \<le> snd (bit_bounds (ir_resultBits op))"
    by (smt (verit, del_insts) Stamp.inject(1) assms(3,5) int_signed_value_bounds s valid_int_gives
        stamp_expr.simps(1) stamp_unary.simps(1) unrestricted_stamp.simps(2) v1)
  then show ?thesis
    using v2 s by (simp add: v3 outBits)
qed

lemma eval_boolean_unary_implies_valid_value:
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  assumes "result = unary_eval op val"
  assumes op: "op \<in> boolean_unary"
  assumes notnorm: "op \<notin> normal_unary"
  assumes "result \<noteq> UndefVal"
  assumes "valid_value val (stamp_expr expr)"
  shows "valid_value result (stamp_expr (UnaryExpr op expr))"
  proof -
    obtain b1 where v1: "val = ObjRef (b1)"
      by (metis singletonD unary_eval.simps(8) intval_is_null.elims assms(2,3,5))
    then have eval: "result = unary_eval op (ObjRef (b1))"
      using assms(2) by blast
  then obtain v2 where v2: "result = IntVal 32 v2"
    by (metis op singleton_iff unary_eval.simps(8) intval_is_null.simps(1) bool_to_val.simps(1,2))
  have vBounds: "result \<in> {bool_to_val True, bool_to_val False}"
    by (metis insertI1 insertI2 intval_is_null.simps(1) op singleton_iff unary_eval.simps(8) eval)
  then have boolstamp: "(stamp_expr (UnaryExpr op expr)) = (IntegerStamp 32 0 1)"
    using op by (cases op; auto)
  then show ?thesis
    using vBounds by (cases result; auto)
  qed

lemma eval_unary_implies_valid_value:
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  assumes "result = unary_eval op val"
  assumes "result \<noteq> UndefVal"
  assumes "valid_value val (stamp_expr expr)"
  shows "valid_value result (stamp_expr (UnaryExpr op expr))"
  proof (cases "op \<in> normal_unary")
    case True
    then show ?thesis 
      using assms eval_normal_unary_implies_valid_value by blast
  next
    case False
    then show ?thesis
  proof (cases "op \<in> boolean_unary")
    case True
    then show ?thesis
      using assms eval_boolean_unary_implies_valid_value by blast
  next
    case False
    then show ?thesis
      using assms
      by (meson eval_normal_unary_implies_valid_value eval_widen_narrow_unary_implies_valid_value)
  qed 
qed

subsubsection \<open>Support Lemmas for Binary Operators\<close>

lemma binary_undef: "v1 = UndefVal \<or> v2 = UndefVal \<Longrightarrow> bin_eval op v1 v2 = UndefVal"
  by (cases op; auto)

lemma binary_obj: "v1 = ObjRef x \<or> v2 = ObjRef y \<Longrightarrow> bin_eval op v1 v2 = UndefVal"
  by (cases op; auto)

text \<open>Some lemmas about the three different output sizes for binary operators.\<close>

lemma bin_eval_bits_binary_shift_ops:
  assumes "result = bin_eval op (IntVal b1 v1) (IntVal b2 v2)"
  assumes "result \<noteq> UndefVal"
  assumes "op \<in> binary_shift_ops"
  shows "\<exists>v. result = new_int b1 v"
  using assms by (cases op; simp; smt (verit, best) new_int.simps)+

lemma bin_eval_bits_fixed_32_ops:
  assumes "result = bin_eval op (IntVal b1 v1) (IntVal b2 v2)"
  assumes "result \<noteq> UndefVal"
  assumes "op \<in> binary_fixed_32_ops"
  shows "\<exists>v. result = new_int 32 v"
  apply (cases op; simp)
  using assms by (metis new_int.simps bin_eval_new_int)+

lemma bin_eval_bits_normal_ops:
  assumes "result = bin_eval op (IntVal b1 v1) (IntVal b2 v2)"
  assumes "result \<noteq> UndefVal"
  assumes "op \<notin> binary_shift_ops"
  assumes "op \<notin> binary_fixed_32_ops"
  shows "\<exists>v. result = new_int b1 v"
  using assms apply (cases op; simp)
  by (metis take_bit_xor take_bit_and take_bit_or)+

lemma bin_eval_input_bits_equal:
  assumes "result = bin_eval op (IntVal b1 v1) (IntVal b2 v2)"
  assumes "result \<noteq> UndefVal"
  assumes "op \<notin> binary_shift_ops"
  shows "b1 = b2"
  using assms apply (cases op; simp) by presburger+

lemma bin_eval_implies_valid_value:
  assumes "[m,p] \<turnstile> expr1 \<mapsto> val1"
  assumes "[m,p] \<turnstile> expr2 \<mapsto> val2"
  assumes "result = bin_eval op val1 val2"
  assumes "result \<noteq> UndefVal"
  assumes "valid_value val1 (stamp_expr expr1)"
  assumes "valid_value val2 (stamp_expr expr2)"
  shows "valid_value result (stamp_expr (BinaryExpr op expr1 expr2))"
proof -
  obtain b1 v1 where v1: "val1 = IntVal b1 v1"
    by (metis Value.collapse(1) assms(3,4) bin_eval_inputs_are_ints bin_eval_int)
  obtain b2 v2 where v2: "val2 = IntVal b2 v2"
    by (metis Value.collapse(1) assms(3,4) bin_eval_inputs_are_ints bin_eval_int)
  then obtain lo1 hi1 where s1: "stamp_expr expr1 = IntegerStamp b1 lo1 hi1"
    by (metis assms(5) v1 valid_int_gives)
  then obtain lo2 hi2 where s2: "stamp_expr expr2 = IntegerStamp b2 lo2 hi2"
    by (metis assms(6) v2 valid_int_gives)
  then have r: "result = bin_eval op (IntVal b1 v1) (IntVal b2 v2)"
    using assms(3) v1 v2 by presburger
  then obtain bres vtmp where vtmp: "result = new_int bres vtmp"
    using assms by (meson bin_eval_new_int)
  then obtain vres where vres: "result = IntVal bres vres"
    by force
  (* now calculate the result stamp for the three classes of operators. *)
  then have sres: "stamp_expr (BinaryExpr op expr1 expr2) =
             unrestricted_stamp (IntegerStamp bres lo1 hi1)
           \<and> 0 < bres \<and> bres \<le> 64"
    proof (cases "op \<in> binary_shift_ops")
      case True
      then show ?thesis
        unfolding stamp_expr.simps
        by (metis Value.inject(1) eval_bits_1_64 new_int.simps r assms(1,4) stamp_binary.simps(1)
            bin_eval_bits_binary_shift_ops s2 s1 v1 vres)
    next
      case False
      then have "op \<notin> binary_shift_ops"
        by blast
      then have beq: "b1 = b2"
        using v1 v2 assms bin_eval_input_bits_equal by blast
      then show ?thesis
      proof (cases "op \<in> binary_fixed_32_ops")
        case True
        then show ?thesis
        unfolding stamp_expr.simps
        by (metis False Value.inject(1) beq bin_eval_new_int le_add_same_cancel1 new_int.simps s2 s1
            numeral_Bit0 vres zero_le_numeral zero_less_numeral assms(3,4) stamp_binary.simps(1))
      next
        case False
        then show ?thesis 
        unfolding s1 s2 stamp_binary.simps stamp_expr.simps
        by (metis beq bin_eval_new_int eval_bits_1_64 intval_bits.simps assms(1,3,4) vres v1
            unrestricted_new_int_always_valid unrestricted_stamp.simps(2) valid_int_same_bits)
    qed
  qed
  then show ?thesis 
    using unrestricted_new_int_always_valid vres vtmp by presburger
qed

subsubsection \<open>Validity of Stamp Meet and Join Operators\<close>

lemma stamp_meet_integer_is_valid_stamp:
  assumes "valid_stamp stamp1"
  assumes "valid_stamp stamp2"
  assumes "is_IntegerStamp stamp1"
  assumes "is_IntegerStamp stamp2"
  shows "valid_stamp (meet stamp1 stamp2)"
  by (smt (verit, del_insts) meet.simps(2) valid_stamp.simps(1,8) is_IntegerStamp_def assms)

lemma stamp_meet_is_valid_stamp:
  assumes 1: "valid_stamp stamp1"
  assumes 2: "valid_stamp stamp2"
  shows "valid_stamp (meet stamp1 stamp2)"
  by (cases stamp1; cases stamp2; insert stamp_meet_integer_is_valid_stamp[OF 1 2]; auto)

lemma stamp_meet_commutes: "meet stamp1 stamp2 = meet stamp2 stamp1"
  by (cases stamp1; cases stamp2; auto)

lemma stamp_meet_is_valid_value1:
  assumes "valid_value val stamp1"  (*  \<or> valid_value val stamp2" *)
  assumes "valid_stamp stamp2"
  assumes "stamp1 = IntegerStamp b1 lo1 hi1"
  assumes "stamp2 = IntegerStamp b2 lo2 hi2"
  assumes "meet stamp1 stamp2 \<noteq> IllegalStamp"
  shows "valid_value val (meet stamp1 stamp2)"
proof -
  have m: "meet stamp1 stamp2 = IntegerStamp b1 (min lo1 lo2) (max hi1 hi2)"
    by (metis assms(3,4,5) meet.simps(2))
  obtain ival where val: "val = IntVal b1 ival"
    using assms valid_int by blast 
  then have v: "valid_stamp (IntegerStamp b1 lo1 hi1) \<and>
       take_bit b1 ival = ival \<and>
       lo1 \<le> int_signed_value b1 ival \<and> int_signed_value b1 ival \<le> hi1"
    by (metis assms(1,3) valid_value.simps(1))
  then have mm: "min lo1 lo2 \<le> int_signed_value b1 ival \<and> int_signed_value b1 ival \<le> max hi1 hi2"
    by linarith
  then have "valid_stamp (IntegerStamp b1 (min lo1 lo2) (max hi1 hi2))"
    by (metis meet.simps(2) stamp_meet_is_valid_stamp v assms(2,3,4,5))
  then show ?thesis 
    using mm v valid_value.simps val m by presburger
qed

text \<open>and the symmetric lemma follows by the commutativity of meet.\<close>

lemma stamp_meet_is_valid_value:
  assumes "valid_value val stamp2"
  assumes "valid_stamp stamp1"
  assumes "stamp1 = IntegerStamp b1 lo1 hi1"
  assumes "stamp2 = IntegerStamp b2 lo2 hi2"
  assumes "meet stamp1 stamp2 \<noteq> IllegalStamp"
  shows "valid_value val (meet stamp1 stamp2)"
  by (metis stamp_meet_is_valid_value1 stamp_meet_commutes assms)

subsubsection \<open>Validity of conditional expressions\<close>

lemma conditional_eval_implies_valid_value:
  assumes "[m,p] \<turnstile> cond \<mapsto> condv"
  assumes "expr = (if val_to_bool condv then expr1 else expr2)"
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  assumes "val \<noteq> UndefVal"
  assumes "valid_value condv (stamp_expr cond)"
  assumes "valid_value val (stamp_expr expr)"
  assumes "compatible (stamp_expr expr1) (stamp_expr expr2)"
  shows "valid_value val (stamp_expr (ConditionalExpr cond expr1 expr2))"
proof -
  have def: "meet (stamp_expr expr1) (stamp_expr expr2) \<noteq> IllegalStamp"
    by (smt (verit, best) Stamp.distinct(13,25) compatible.elims(2) meet.simps(1,2) assms(7))
  then have "valid_stamp (meet (stamp_expr expr1) (stamp_expr expr2))"
    by (smt (verit, best) compatible.elims(2) stamp_meet_is_valid_stamp valid_stamp.simps(2) assms)
  then show ?thesis
    by (smt (verit, best) compatible.elims(2) never_void stamp_expr.simps(6) stamp_meet_commutes def
        assms stamp_meet_is_valid_value)
qed

subsubsection \<open>Validity of Whole Expression Tree Evaluation\<close>

text \<open> TODO: find a way to encode that conditional expressions must have
  compatible (and valid) stamps?  One approach would be for all the 
  stamp\_expr operators to require that all input stamps are valid.\<close>

(*
experiment begin
lemma stamp_implies_valid_value:
  assumes "[m,p] \<turnstile> expr \<mapsto> val"
  shows "valid_value val (stamp_expr expr)"
  using assms proof (induction expr val)
  case (UnaryExpr expr val result op)
  then show ?case using eval_unary_implies_valid_value by simp
  next
    case (BinaryExpr expr1 val1 expr2 val2 result op)
    then show ?case using bin_eval_implies_valid_value by simp
  next
    case (ConditionalExpr cond condv expr expr1 expr2 val)
    have "compatible (stamp_expr expr1) (stamp_expr expr2)"
      using assms sorry
    then show ?case 
      using assms conditional_eval_implies_valid_value
      using ConditionalExpr.IH(1) ConditionalExpr.IH(2) ConditionalExpr.hyps(1) ConditionalExpr.hyps(2) ConditionalExpr.hyps(3) ConditionalExpr.hyps(4) by blast
  next
    case (ParameterExpr x1 x2)
    then show ?case by auto
  next
    case (LeafExpr x1 x2)
    then show ?case by auto
  next
    case (ConstantExpr x)
    then show ?case by auto
qed

lemma value_range:
  assumes "[m, p] \<turnstile> e \<mapsto> v"
  shows "v \<in> {val . valid_value val (stamp_expr e)}"
  using assms sorry
end
*)

definition wf_stamp :: "IRExpr \<Rightarrow> bool" where
  "wf_stamp e = (\<forall>m p v. ([m, p] \<turnstile> e \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr e))"

lemma stamp_under_defn:
  assumes "stamp_under (stamp_expr x) (stamp_expr y)"
  assumes "wf_stamp x \<and> wf_stamp y"
  assumes "([m, p] \<turnstile> x \<mapsto> xv) \<and> ([m, p] \<turnstile> y \<mapsto> yv)"
  shows "val_to_bool (bin_eval BinIntegerLessThan xv yv) \<or>
         (bin_eval BinIntegerLessThan xv yv) = UndefVal"
proof -
  have yval: "valid_value yv (stamp_expr y)"
    using assms wf_stamp_def by blast
  obtain b lx hi where xstamp: "stamp_expr x = IntegerStamp b lx hi"
    by (metis stamp_under.elims(2) assms(1))
  then obtain b' lo hy where ystamp: "stamp_expr y = IntegerStamp b' lo hy"
    by (meson stamp_under.elims(2) assms(1))
  obtain xvv where xvv: "xv = IntVal b xvv"
    by (metis assms(2,3) valid_int wf_stamp_def xstamp)
  then have xval: "valid_value (IntVal b xvv) (stamp_expr x)"
    using assms(2,3) wf_stamp_def by blast
  obtain yvv where yvv: "yv = IntVal b' yvv"
    by (metis valid_int ystamp yval)
  then have xval: "valid_value (IntVal b' yvv) (stamp_expr y)"
    using yval by blast
  have xunder: "int_signed_value b xvv \<le> hi"
    by (metis assms(2,3) wf_stamp_def xstamp valid_value.simps(1) xvv)
  have yunder: "lo \<le> int_signed_value b' yvv"
    by (metis ystamp valid_value.simps(1) yval yvv)
  have unwrap: "\<forall>cond. bool_to_val_bin b b cond = bool_to_val cond"
    by simp
  from xunder yunder have "int_signed_value b xvv < int_signed_value b' yvv"
    using assms(1) xstamp ystamp by force
  then have "(intval_less_than xv yv) = IntVal 32 1 \<or> (intval_less_than xv yv) = UndefVal"
    by (simp add: yvv xvv)
  then show ?thesis
    by force
qed

lemma stamp_under_defn_inverse:
  assumes "stamp_under (stamp_expr y) (stamp_expr x)"
  assumes "wf_stamp x \<and> wf_stamp y"
  assumes "([m, p] \<turnstile> x \<mapsto> xv) \<and> ([m, p] \<turnstile> y \<mapsto> yv)"
  shows "\<not>(val_to_bool (bin_eval BinIntegerLessThan xv yv)) \<or> (bin_eval BinIntegerLessThan xv yv) = UndefVal"
proof -
  have yval: "valid_value yv (stamp_expr y)"
    using assms wf_stamp_def by blast
  obtain b lo hx where xstamp: "stamp_expr x = IntegerStamp b lo hx"
    by (metis stamp_under.elims(2) assms(1))
  then obtain b' ly hi where ystamp: "stamp_expr y = IntegerStamp b' ly hi"
    by (meson stamp_under.elims(2) assms(1))
  obtain xvv where xvv: "xv = IntVal b xvv"
    by (metis assms(2,3) valid_int wf_stamp_def xstamp)
  then have xval: "valid_value (IntVal b xvv) (stamp_expr x)"
    using assms(2,3) wf_stamp_def by blast
  obtain yvv where yvv: "yv = IntVal b' yvv"
    by (metis valid_int ystamp yval)
  then have xval: "valid_value (IntVal b' yvv) (stamp_expr y)"
    using yval by simp
  have yunder: "int_signed_value b' yvv \<le> hi"
    by (metis ystamp valid_value.simps(1) yval yvv)
  have xover: "lo \<le> int_signed_value b xvv"
    by (metis assms(2,3) wf_stamp_def xstamp valid_value.simps(1) xvv)
  have unwrap: "\<forall>cond. bool_to_val_bin b b cond = bool_to_val cond"
    by simp
  from xover yunder have "int_signed_value b' yvv < int_signed_value b xvv"
    using assms(1) xstamp ystamp by force
  then have "(intval_less_than xv yv) = IntVal 32 0  \<or> (intval_less_than xv yv) = UndefVal"
    by (auto simp add: yvv xvv)
  then show ?thesis
    by force
qed

end