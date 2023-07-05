subsection \<open>LeftShiftNode Phase\<close>

theory LeftShiftPhase
  imports
    Common
    Proofs.StampEvalThms
begin

phase LeftShiftNode
  terminating size
begin


(*
fun shift_amount_new :: "iwidth \<Rightarrow> int64 \<Rightarrow> int64" where
  "shift_amount_new b val = unat (and val (if b = 64 then 0x3F else 0x1f))"
*)

(* Value level proofs *)
(* 64-bit version *)
lemma val_EliminateRHS_64:
  assumes "x = IntVal 64 vx"
  and     "y = IntVal 64 vy"
  and     "and vy (mask 6) = 0"
  and     "val[x << y] \<noteq> UndefVal"
  shows "val[x << y] = x"
  using assms apply (cases x; cases y; auto) 
  subgoal
    proof -
      have 1: "(and vy (63) = 0)"
        by (metis (no_types, lifting) Suc_1 add_2_eq_Suc' add_Suc_shift mask_1 mask_Suc_rec mult_2 
            numeral_Bit0 numeral_Bit1 numeral_One assms(3))
      then have 2: "(0::nat) mod 2 ^ LENGTH(64) = 0"
        by simp
      then have 3: "(vx << 0) = vx"
        unfolding shiftl_def by simp
      then have "take_bit LENGTH(64) ((vx << unat (and vy (63)))::64 word) = vx"
        unfolding Word.take_bit_length_eq 1 Word.unat_word_ariths(4) 2 3 by auto
      then show ?thesis
        by simp    
     qed
     done

lemma val_EliminateRHS_642:
  assumes "x = IntVal 64 vx"
  and     "y = IntVal 64 vy"
  and     "(shift_amount 64 vy) = 0"
  and     "val[x << y] \<noteq> UndefVal"
  shows "val[x << y] = x"
  using assms apply (cases x; cases y; auto) 
  subgoal
    proof -
       have 3: "(vx << 0) = vx"
        unfolding shiftl_def by simp
      then have "take_bit LENGTH(64) ((vx << 0)::64 word) = vx"
        unfolding Word.take_bit_length_eq by auto
      then show ?thesis
        by simp    
     qed
  done

(* All bit-widths *)
lemma val_EliminateRHS:
  assumes "x = IntVal bx vx"
  and     "bx = 32 | bx = 64"
  and     "y = IntVal by vy"
  and     "(shift_amount bx vy) = 0"
  and     "val[x << y] \<noteq> UndefVal"
  shows "val[x << y] = x"
  using assms apply (cases x; cases y; auto)
  subgoal (* 32-bit *)
  proof -
    have 1: "vx << (0::nat) = vx"
      unfolding shiftl_def by simp
    then have "take_bit 32 (vx << (0::nat)) = vx"
      unfolding Word.take_bit_length_eq 1 
      apply (cases vx; simp) 
      sorry
    then show ?thesis
       by simp
    qed
    subgoal (* 64-bit *)
    proof -
       have 3: "(vx << 0) = vx"
        unfolding shiftl_def by simp
      then have "take_bit LENGTH(64) ((vx << 0)::64 word) = vx"
        unfolding Word.take_bit_length_eq by auto
      then show ?thesis
        by simp    
     qed
   done

(* Exp level proofs *)
lemma exp_EliminateRHS:
  assumes "y = IntVal 64 vy"
  and     "and vy (mask 6) = 0" 
  and     "stamp_expr x = IntegerStamp 64 lo hi" 
  and     "wf_stamp x"
  shows "exp[x << const(y)] \<ge> x"
  unfolding bin_eval.simps(8) apply auto[1]
  subgoal premises p for m p xa
    proof -
      obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
        using p by auto
      then have 1: "wf_value y"
        by (auto simp: p(3))
      then have 2: "val[xa << y] \<noteq> UndefVal"
        using evalDet p(1,2) xa by blast
      then have "val[xa << y] = xa" 
        using assms val_EliminateRHS sorry
      then show ?thesis
        using evalDet p(1) xa by fastforce
    qed
  done

text \<open>Optimisations\<close>

optimization EliminateRHS_64: "(x << const(y)) \<longmapsto> x when 
                               (IsStamp x (IntegerStamp 64 lo hi) && 
                                WellFormed x)"
  using exp_EliminateRHS wf_stamp_def  bin_eval.simps(8)  sorry


end (* End of ShiftNode *)

end (* End of file *)