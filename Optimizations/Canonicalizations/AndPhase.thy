subsection \<open>AndNode Phase\<close>

theory AndPhase
  imports
    Common
    Proofs.StampEvalThms
begin

context stamp_mask
begin

lemma AndRightFallthrough: "(((and (not (\<down> x)) (\<up> y)) = 0)) \<longrightarrow> exp[x & y] \<ge> exp[y]"
  apply simp apply (rule impI; (rule allI)+)
  apply (rule impI)
  subgoal premises p for m p v
  proof -
    obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> xv"
      using p(2) by blast
    obtain yv where yv: "[m, p] \<turnstile> y \<mapsto> yv"
      using p(2) by blast
    have "v = val[xv & yv]"
      by (metis BinaryExprE bin_eval.simps(4) evalDet p(2) xv yv)
    then have "v = yv"
      by (smt (verit) eval_unused_bits_zero intval_and.elims new_int.elims new_int_bin.elims p(2) 
          unfold_binary xv yv p(1) not_down_up_mask_and_zero_implies_zero)
    then show ?thesis using yv by simp
  qed
  done

lemma AndLeftFallthrough: "(((and (not (\<down> y)) (\<up> x)) = 0)) \<longrightarrow> exp[x & y] \<ge> exp[x]"
  apply simp apply (rule impI; (rule allI)+)
  apply (rule impI)
  subgoal premises p for m p v
  proof -
    obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> xv"
      using p(2) by blast
    obtain yv where yv: "[m, p] \<turnstile> y \<mapsto> yv"
      using p(2) by blast
    have "v = val[xv & yv]"
      by (metis BinaryExprE bin_eval.simps(4) evalDet p(2) xv yv)
    then have "v = xv" 
      by (smt (verit) and.commute eval_unused_bits_zero intval_and.elims new_int.simps 
          new_int_bin.simps p(2) unfold_binary xv yv p(1) not_down_up_mask_and_zero_implies_zero)
    then show ?thesis using xv by simp
  qed
  done
end

phase AndNode  
  terminating size
begin

(* Word level proofs *)
lemma bin_and_nots:
 "(~x & ~y) = (~(x | y))"
  by simp

lemma bin_and_neutral:
 "(x & ~False) = x"
  by simp

(* Value level proofs *)
lemma val_and_equal:
  assumes "x = new_int b v"
  and     "val[x & x] \<noteq> UndefVal"
  shows   "val[x & x] = x"
   using assms by (cases x; auto)

lemma val_and_nots:
  "val[~x & ~y] = val[~(x | y)]"
  apply (cases x; cases y; auto) by (simp add: take_bit_not_take_bit)

lemma val_and_neutral:
  assumes "x = new_int b v"
  and     "val[x & ~(new_int b' 0)] \<noteq> UndefVal"
  shows   "val[x & ~(new_int b' 0)] = x"
   using assms apply (cases x; auto) apply (simp add: take_bit_eq_mask) 
   by presburger

(* Not sure if this one is written correctly *)
(*
lemma val_and_sign_extend:
  assumes "e = (1 << In)-1"
  shows "val[(intval_sign_extend In Out x) & (IntVal b e)] = intval_zero_extend In Out x"
  using assms apply (cases x; auto) 
  sorry

lemma val_and_sign_extend_2:
  assumes "e = (1 << In)-1 \<and> intval_and (intval_sign_extend In Out x) (IntVal 32 e) \<noteq> UndefVal"
  shows "val[(intval_sign_extend In Out x) &  (IntVal 32 e)] = intval_zero_extend In Out x"
  using assms apply (cases x;  auto) 
  sorry*)

(* Extras which were missing *)
lemma val_and_zero:
  assumes "x = new_int b v"
  shows   "val[x & (IntVal b 0)] = IntVal b 0"
   using assms by (cases x; auto) 

(* Exp level proofs *)
lemma exp_and_equal:
  "exp[x & x] \<ge> exp[x]"
   apply auto[1]
  by (smt (verit) evalDet intval_and.elims new_int.elims val_and_equal eval_unused_bits_zero)

lemma exp_and_nots:
  "exp[~x & ~y] \<ge> exp[~(x | y)]"
   apply (cases x; cases y; auto) using val_and_nots
  by fastforce+ 

lemma exp_sign_extend:
  assumes "e = (1 << In) - 1"
  shows   "BinaryExpr BinAnd (UnaryExpr (UnarySignExtend In Out) x) 
                             (ConstantExpr (new_int b e))
                           \<ge> (UnaryExpr (UnaryZeroExtend In Out) x)"
  apply auto[1]
  subgoal premises p for m p va
    proof - 
      obtain va where va: "[m,p] \<turnstile> x \<mapsto> va"
        using p(2) by auto
      then have "va \<noteq> UndefVal"
        by (simp add: evaltree_not_undef)
      then have 1: "intval_and (intval_sign_extend In Out va) (IntVal b (take_bit b e)) \<noteq> UndefVal"
        using evalDet p(1) p(2) va by blast
      then have 2: "intval_sign_extend In Out va \<noteq> UndefVal"
        by auto
      then have 21: "(0::nat) < b"
        using eval_bits_1_64 p(4) by blast
      then have 3: "b \<sqsubseteq> (64::nat)"
        using eval_bits_1_64 p(4) by blast
      then have 4: "- ((2::int) ^ b div (2::int)) \<sqsubseteq> sint (signed_take_bit (b - Suc (0::nat)) (take_bit b e))"
        by (simp add: "21" int_power_div_base signed_take_bit_int_greater_eq_minus_exp_word)
      then have 5: "sint (signed_take_bit (b - Suc (0::nat)) (take_bit b e)) < (2::int) ^ b div (2::int)"
        by (simp add: "21" "3" Suc_le_lessD int_power_div_base signed_take_bit_int_less_exp_word)
      then have 6: "[m,p] \<turnstile> UnaryExpr (UnaryZeroExtend In Out)
                 x \<mapsto> intval_and (intval_sign_extend In Out va) (IntVal b (take_bit b e))"
        apply (cases va; simp) 
        apply (simp add: \<open>(va::Value) \<noteq> UndefVal\<close>) defer 
         subgoal premises p for x3
          proof -
            have "va = ObjRef x3"
              using p(1) by auto
            then have "sint (signed_take_bit (b - Suc (0::nat)) (take_bit b e)) < (2::int) ^ b div (2::int)"
              by (simp add: "5")
            then show ?thesis
              using "2" intval_sign_extend.simps(3) p(1) by blast
          qed 
          
         subgoal premises p for x4
          proof -
            have sg1: "va = ObjStr x4"
              using "2" p(1) by auto
            then have "sint (signed_take_bit (b - Suc (0::nat)) (take_bit b e)) < (2::int) ^ b div (2::int)"
              by (simp add: "5")
            then show ?thesis
              using "1" sg1 by auto
          qed 

          (* Last subgoal*)
          subgoal premises p for x21 x22
            proof - 
              have sgg1: "va = IntVal x21 x22"
                by (simp add: p(1))
              then have sgg2: "sint (signed_take_bit (b - Suc (0::nat)) (take_bit b e)) < (2::int) ^ b div (2::int)"
                by (simp add: "5")
              then show ?thesis
                sorry
              qed
            done
      then show ?thesis
        by (metis evalDet p(2) va)
    qed 
  done 


(*lemma exp_and_neutral: 
  "exp[x & ~(const (new_int b 0))] \<ge> x"
  apply auto using val_and_neutral eval_unused_bits_zero sorry (*
  apply (cases x; simp) using val_and_neutral bin_eval.simps(4)  
  apply (smt (verit) BinaryExprE Value.collapse(1) intval_and.simps(12) intval_not.simps(2) 
         is_IntVal_def unary_eval.simps(3) unary_eval_int unfold_const64 unfold_unary) 
         using val_and_neutral_64 bin_eval.simps(4) 
  apply (metis (no_types, lifting) BinaryExprE UnaryExprE Value.collapse(1) bin_eval_int 
         intval_and.simps(12) intval_not.simps(2) is_IntVal_def unary_eval.simps(3) unfold_const64)
         using val_and_neutral_64 bin_eval.simps(4) unary_eval.simps(3)
  apply (smt (z3) BinaryExprE UnaryExprE Value.discI(2) Value.distinct(9) intval_and.elims 
         intval_not.simps(2) unfold_const64) 
         using val_and_neutral_64 bin_eval.simps(4) unary_eval.simps(3) bin_and_neutral 
               unfold_const64 intval_and.elims intval_not.simps(2) 
         sorry*)*)


(* Helpers *)
lemma val_and_commute[simp]:
   "val[x & y] = val[y & x]"
   apply (cases x; cases y; auto)
  by (simp add: word_bw_comms(1))

text \<open>Optimisations\<close>

optimization AndEqual: "x & x \<longmapsto> x"
  using exp_and_equal by blast

value AndEqual_code

value "exp[y & (const x)]"
optimization AndShiftConstantRight: "((const x) & y) \<longmapsto> y & (const x) 
                                         when Not (IsConstantExpr y)"
  using size_flip_binary by auto
value AndShiftConstantRight_code
value "export_rules AndShiftConstantRight_code"

optimization AndNots: "(~x) & (~y) \<longmapsto> ~(x | y)"
   apply (metis add_2_eq_Suc' less_SucI less_add_Suc1 not_less_eq size_binary_const size_non_add)
  using exp_and_nots by auto

(* Need to prove exp_sign_extend*)
optimization AndSignExtend: "BinaryExpr BinAnd (UnaryExpr (UnarySignExtend In Out) (x)) 
                                               (const (new_int b e))
                              \<longmapsto> (UnaryExpr (UnaryZeroExtend In Out) (x))
                                  when (e = (1 << In) - 1)"
   using exp_sign_extend by simp 

optimization AndNeutral: "(x & ~(const (IntVal b 0))) \<longmapsto> x 
   when (WellFormed x && IsStamp x (IntegerStamp b lo hi))"
   apply auto 
  by (smt (verit) Value.sel(1) eval_unused_bits_zero intval_and.elims intval_word.simps 
      new_int.simps new_int_bin.simps take_bit_eq_mask)


optimization AndRightFallThrough: "(x & y) \<longmapsto> y
                                when (((and (not (IRExpr_down x)) (IRExpr_up y)) = 0))"
  by (simp add: IRExpr_down_def IRExpr_up_def)

optimization AndLeftFallThrough: "(x & y) \<longmapsto> x
                                when (((and (not (IRExpr_down y)) (IRExpr_up x)) = 0))"
   by (simp add: IRExpr_down_def IRExpr_up_def) 


end (* End of AndPhase *)

end (* End of file *)