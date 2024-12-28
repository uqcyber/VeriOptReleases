subsection \<open>ShiftNode Phase\<close>

theory ShiftPhase
  imports 
    Common
begin

subsection \<open>Integer\<close>

text \<open>
\begin{lstlisting}[language=java]

class Long {
    public static int numberOfLeadingZeros(long i) {
        int x = (int)(i >>> 32);
        return x == 0 ? 32 + Integer.numberOfLeadingZeros((int)i)
                : Integer.numberOfLeadingZeros(x);
    }
}

class Integer {
    public static int numberOfLeadingZeros(int i) {
        // HD, Count leading 0's
        if (i <= 0)
            return i == 0 ? 32 : 0;
        int n = 31;
        if (i >= 1 << 16) { n -= 16; i >>>= 16; }
        if (i >= 1 <<  8) { n -=  8; i >>>=  8; }
        if (i >= 1 <<  4) { n -=  4; i >>>=  4; }
        if (i >= 1 <<  2) { n -=  2; i >>>=  2; }
        return n - (i >>> 1);
    }
}
\end{lstlisting}
\<close>

(*fun numberOfLeadingZeros :: "32 word \<Rightarrow> nat" where
  "numberOfLeadingZeros i = 
    (if i = 0 then 32 else 0)
  "
*)

subsection \<open>CodeUtil\<close>

text \<open>
The @{text jdk.vm.ci.code.CodeUtil} class is used by the GraalVM compiler to perform
non-standard operations on integers.
\<close>

paragraph \<open>CodeUtil.isPowerOf2\<close>
text \<open>
The isPowerOf2 determines if a long is a power of 2 through bit manipulation.
Our encoding is based on it's definition.

\begin{lstlisting}[language=java]
public static boolean isPowerOf2(long val) {
    return val > 0 && (val & val - 1) == 0;
}
\end{lstlisting}

The isPowerOf2 operation is performed on longs,
so we should be safe here to define our function in terms of a 64-bit word.
\<close>

fun CodeUtil_isPowerOf2 :: "64 word \<Rightarrow> bool" where
  "CodeUtil_isPowerOf2 v = (0 <s v \<and> (and v (v - 1)) = 0)"

lemma positive_powers:
  "CodeUtil_isPowerOf2 v \<Longrightarrow> (0 <s v)"
  by simp

lemma some_bit_set:
  fixes v :: "64 word"
  assumes "v \<noteq> 0"
  shows "\<exists>n. bit v n"
  using assms
  by (metis bit_and_iff bit_eqI word_log_esimps(7))

lemma positive_bit_set_between:
  fixes v :: "64 word"
  assumes "0 <s v"
  shows "\<exists>n. 0 \<le> n \<and> n < 64 \<and> bit v n"
  using assms
  by (metis ValueThms.size64 bit_imp_le_length less_eq_nat.simps(1) signed.dual_order.strict_implies_not_eq some_bit_set wsst_TYs(3))

lemma has_set_bit:
  assumes "CodeUtil_isPowerOf2 v"
  shows "\<exists>n. 0 \<le> n \<and> n < 64 \<and> bit v n"
  using assms unfolding CodeUtil_isPowerOf2.simps
  using positive_bit_set_between by blast

lemma all_other_unset:
  assumes "CodeUtil_isPowerOf2 v"
  shows "\<exists>n. 0 \<le> n \<and> n < 64 \<and> bit v n \<and> (\<forall>n'. n' \<noteq> n \<longrightarrow> \<not>(bit v n'))"
proof -
  obtain n where n: "0 \<le> n \<and> n < 64 \<and> bit v n"
    using assms has_set_bit by presburger
  have "\<forall>n'. n' \<noteq> n \<longrightarrow> \<not>(bit v n')"
    using assms unfolding CodeUtil_isPowerOf2.simps sorry
  then show ?thesis
    using n by blast
qed

lemma distinct_bit:
  assumes "CodeUtil_isPowerOf2 v"
  assumes "bit v n"
  assumes "bit v n'"
  shows "n = n'"
  using assms all_other_unset
  by metis

paragraph \<open>CodeUtil.log2\<close>
text \<open>

\begin{lstlisting}[language=java]
public static int log2(long val) {
    assert val > 0;
    return (Long.SIZE - 1) - Long.numberOfLeadingZeros(val);
}
\end{lstlisting}
\<close>

fun CodeUtil_log2 :: "64 word \<Rightarrow> nat" where
  "CodeUtil_log2 v = (64 - 1 - (numberOfLeadingZeros v))"

lemma log2_highest_one_bit:
  fixes v :: "64 word"
  assumes "v > 0"
  shows "CodeUtil_log2 v = nat (highestOneBit v)"
proof -
  have "highestOneBit v < 64"
    using highestOneBit_top by auto
  then show ?thesis
  unfolding CodeUtil_log2.simps numberOfLeadingZeros_def
  unfolding ValueThms.size64 by auto
qed

lemma log2_has_bit_set:
  assumes "CodeUtil_log2 x = i"
  assumes "x > 0"
  shows "0 \<le> i \<and> i < 64 \<and> bit x i"
  apply (rule conjI) defer apply (rule conjI) defer defer
  using assms unfolding CodeUtil_log2.simps 
  apply blast
  using assms(1) apply fastforce
  using assms log2_highest_one_bit highestOneBitElim
  by (metis MaxOrNeg_def highestOneBitNeg highestOneBit_def less_le nat_int)


paragraph \<open>Combine isPowerOf2 and log2\<close>

lemma log2_powerOf2:
  assumes "CodeUtil_isPowerOf2 x"
  assumes "CodeUtil_log2 x = i"
  shows "0 \<le> i \<and> i < 64 \<and> bit x i \<and> (\<forall>n'. n' \<noteq> i \<longrightarrow> \<not>(bit x n'))"
  using assms distinct_bit
  by (metis log2_has_bit_set positive_powers signed.dual_order.strict_implies_not_eq word_gt_0)

lemma is_push_bit:
  assumes "0 \<le> i \<and> i < 64 \<and> bit x i \<and> (\<forall>n'. n' \<noteq> i \<longrightarrow> \<not>(bit x n'))"
  shows "x = push_bit i 1"
  using assms unfolding bit_iff_odd push_bit_eq_mult apply auto sorry

lemma log2_base:
  assumes "CodeUtil_isPowerOf2 x"
  assumes "CodeUtil_log2 x = i"
  shows "x = 2^i"
  using assms log2_powerOf2 push_bit_of_1 is_push_bit
  by fastforce

lemma shift_opt:
  assumes "CodeUtil_isPowerOf2 x"
  assumes "CodeUtil_log2 x = i"
  shows "a * x = a << i"
  using assms
  by (metis log2_base shiftl_power)

(*
lemma
  assumes "c > 0"
  assumes "CodeUtil_isPowerOf2 c"
  assumes "val[a * IntVal b c] \<noteq> UndefVal"
  shows "val[a * IntVal b c] = val[a << IntVal b (word_of_nat (CodeUtil_log2 c))]"
proof -
  obtain av where "a = IntVal b av"
    by (smt (z3) assms(3) intval_bits.simps intval_mul.elims new_int_bin.simps)
  have "intval_mul a (IntVal b c) = IntVal b (take_bit b (av * c))"
    by (simp add: \<open>a = IntVal b av\<close>)
  have "intval_left_shift a (IntVal b (word_of_nat (CodeUtil_log2 c))) = IntVal b (take_bit b ((av << shift_amount b (word_of_nat (CodeUtil_log2 c)))))"
    using \<open>a = IntVal b av\<close> eval_thms(90) new_int.simps by presburger
  
  then show ?thesis
  proof (cases "b = 64")
    case True
    then show ?thesis sorry
  next
    case False
    have "shift_amount b (word_of_nat (CodeUtil_log2 c)) = (CodeUtil_log2 c) mod 32"
      using False unfolding shift_amount.simps apply (simp del: CodeUtil_log2.simps) using shift_amount_32 log2_has_bit_set sorry
    then show ?thesis sorry
  qed
*)

                                        
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


optimization e[nogen]:
  when "(Value c)..isPowerOf2()"
  "x * (const c) \<longmapsto> let n = intval_log2 c in x << (const n)"
  using e_intval BinaryExprE ConstantExprE bin_eval.simps(2,7) sorry

end

end