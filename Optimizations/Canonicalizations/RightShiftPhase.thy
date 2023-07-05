subsection \<open>RightShiftNode Phase\<close>

theory RightShiftPhase
  imports
    Common
    Proofs.StampEvalThms
begin

phase RightShiftNode
  terminating size
begin

(* Value level proofs *)
(* Has counter-example if x not 32-bit *)
lemma val_ReturnXOnZeroShift:
  assumes "val[x >> (IntVal 32 0)] \<noteq> UndefVal"
  and     "x = IntVal 32 xv"
  shows "val[x >> (IntVal 32 0)] = x"  
  unfolding assms(2) intval_right_shift.simps(1) apply auto
  sorry

(* Exp level proofs *)
lemma exp_ReturnXOnZeroShift:
  assumes "stamp_expr x = IntegerStamp 32 lo hi"
  and     "wf_stamp x"
  shows "exp[x >> const(IntVal 32 0)] \<ge> exp[x]" 
  apply auto
  subgoal premises p for m p xa
  proof - 
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p(1) by auto
    then have vx: "\<exists>vx. xa = IntVal 32 vx"
      by (metis valid_int assms wf_stamp_def)
    then have 1: "val[xa >> (IntVal 32 0)] \<noteq> UndefVal"
      using evalDet p(1,2) xa by blast
    then have 2: "wf_value (IntVal 32 0)"
      by (auto simp: p(3))
    then have equals: "xa = val[xa >> (IntVal 32 0)]"
      by (metis "1" val_ReturnXOnZeroShift vx)
    then have 3: "[m,p] \<turnstile> x \<mapsto> val[xa >> (IntVal 32 0)]"
      by (simp add: xa)
    then show ?thesis
      using evalDet p(1) xa by blast
  qed
  done

text \<open>Optimisations\<close>
(* Need to prove exp_ReturnXOnZeroShift *)
optimization ReturnXOnZeroShift: "(x >> const(new_int 32 0)) \<longmapsto> x when 
                                  ((stamp_expr x = IntegerStamp 32 lo hi) \<and> (wf_stamp x))"
   using exp_ReturnXOnZeroShift by fastforce

end (* End of RightShiftNode *)

end (* End of file *)