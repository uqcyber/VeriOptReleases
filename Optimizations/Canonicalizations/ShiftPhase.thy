subsection \<open>ShiftNode Phase\<close>

theory ShiftPhase
  imports 
    Common
begin

phase ShiftNode
  terminating size
begin

fun intval_log2 :: "Value \<Rightarrow> Value" where
  "intval_log2 (IntVal b v) = IntVal b (word_of_int (SOME e. v=2^e))" |
  "intval_log2 _ = UndefVal"

fun in_bounds :: "Value \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "in_bounds (IntVal b v) l h = (l < sint v \<and> sint v < h)" |
  "in_bounds _ l h = False"

lemma
  assumes "in_bounds (intval_log2 val_c) 0 32"
  shows "val[x << (intval_log2 val_c)] = val[x * val_c]"
  apply (cases val_c; auto) using intval_left_shift.simps(1) intval_mul.simps(1) intval_log2.simps(1)
  sorry

lemma e_intval:
  "n = intval_log2 val_c \<and> in_bounds n 0 32 \<longrightarrow>
    val[x << (intval_log2 val_c)] = val[x * val_c]"
proof (rule impI)
  assume "n = intval_log2 val_c \<and> in_bounds n 0 32"
  show "val[x << (intval_log2 val_c)] = val[x * val_c]"
    proof (cases "\<exists> v . val_c = IntVal 32 v")
      case True
      obtain vc where "val_c = IntVal 32 vc"
        using True by blast
      then have "n = IntVal 32 (word_of_int (SOME e. vc=2^e))"
        using \<open>n = intval_log2 val_c \<and> in_bounds n 0 32\<close> intval_log2.simps(1) by presburger
      then show ?thesis sorry
    next
      case False
      then have "\<exists> v . val_c = IntVal 64 v"
        sorry (* no longer true
        by (metis \<open>n = intval_log2 val_c \<and> in_bounds n 0 32\<close> in_bounds.simps(3) intval_log2.elims)*)
      then obtain vc where "val_c = IntVal 64 vc"
        by auto
      then have "n = IntVal 64 (word_of_int (SOME e. vc=2^e))"
        using \<open>n = intval_log2 val_c \<and> in_bounds n 0 32\<close> intval_log2.simps(1) by presburger
      then show ?thesis sorry
qed
qed

(*
optimization e:
  "x * (const c) \<longmapsto> x << (const n) when (n = intval_log2 c \<and> in_bounds n 0 32)"
  using e_intval BinaryExprE ConstantExprE bin_eval.simps(2,7) sorry
*)

end

end