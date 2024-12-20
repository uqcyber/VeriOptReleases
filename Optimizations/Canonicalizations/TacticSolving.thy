theory TacticSolving
  imports Common
begin

fun size :: "IRExpr \<Rightarrow> nat" where
  "size (UnaryExpr op e) = (size e) * 2" |
  "size (BinaryExpr BinAdd x y) = (size x) + ((size y) * 2)" |
  "size (BinaryExpr op x y) = (size x) + (size y)" |
  "size (ConditionalExpr c t f) = (size c) + (size t) + (size f) + 2" |
  "size (ConstantExpr c) = 1" |
  "size (ParameterExpr ind s) = 2" |
  "size (LeafExpr nid s) = 2" |
  "size (ConstantVar c) = 2" |
  "size (VariableExpr x s) = 2"

lemma size_pos[simp]: "0 < size y"
  apply (induction y; auto?)
  subgoal premises prems for op a b
    using prems by (induction op; auto)
  done

phase TacticSolving
  terminating size
begin

subsection \<open>AddNode\<close>
(*lemma val_add_left_negate_to_sub:
  "val[-x + y] \<approx> val[y - x]"
  apply simp by (cases x; cases y; auto)

lemma exp_add_left_negate_to_sub:
  "exp[-x + y] \<ge> exp[y - x]"
  using val_add_left_negate_to_sub by auto*)

lemma value_approx_implies_refinement:
  assumes "lhs \<approx> rhs"
  assumes "\<forall>m p v. ([m, p] \<turnstile> elhs \<mapsto> v) \<longrightarrow> v = lhs"
  assumes "\<forall>m p v. ([m, p] \<turnstile> erhs \<mapsto> v) \<longrightarrow> v = rhs"
  assumes "\<forall>m p v1 v2. ([m, p] \<turnstile> elhs \<mapsto> v1) \<longrightarrow> ([m, p] \<turnstile> erhs \<mapsto> v2)"
  shows "elhs \<ge> erhs"
  by (metis assms(4) le_expr_def evaltree_not_undef)

method explore_cases for x y :: Value =
  (cases x; cases y; auto)

method explore_cases_bin for x :: IRExpr =
  (cases x; auto)

method obtain_approx_eq for lhs rhs x y :: Value =
  (rule meta_mp[where P="lhs \<approx> rhs"], defer_tac, explore_cases x y)

method obtain_eval for exp::IRExpr and val::Value =
  (rule meta_mp[where P="\<And>m p v. ([m, p] \<turnstile> exp \<mapsto> v) \<Longrightarrow> v = val"], defer_tac)

method solve for lhs rhs x y :: Value =
  (match conclusion in "size _ < size _" \<Rightarrow> \<open>simp\<close>)?,
  (match conclusion in "(elhs::IRExpr) \<ge> (erhs::IRExpr)" for elhs erhs \<Rightarrow> \<open>
    (obtain_approx_eq lhs rhs x y)?\<close>)

print_methods
(*
    (simp del: well_formed_equal_def le_expr_def)?;
    ((rule allI)+)?\<close>)*)
thm BinaryExprE
optimization opt_add_left_negate_to_sub:
  "-x + y \<longmapsto> y - x"
  (*defer apply simp apply (rule allI)+ apply (rule impI)
   apply (subgoal_tac "\<forall>x1. [m, p] \<turnstile> exp[-x + y] \<mapsto> x1") defer
  *)
   apply (solve "val[-x1 + y1]" "val[y1 - x1]" x1 y1)
  apply simp apply auto[1] using evaltree_not_undef sorry
(*
  apply (obtain_eval "exp[-x + y]" "val[-x1 + y1]")
  

  apply (rule BinaryExprE)
  apply (rule allI)+ sorry
  apply (auto simp: unfold_evaltree) sorry*)
  (*
   defer apply (test "val[-x1 + y1]" "val[y1 - x1]" x1 y1)
   apply (rule meta_mp[where P="val[-x1 + y1] \<approx> val[y1 - x1]"])
    prefer 2 apply (cases x1; cases y1; auto)
   apply (subgoal_tac "val[-x1 + y1] \<approx> val[y1 - x1]")
    apply (cases x1; cases y1; auto)
  using exp_add_left_negate_to_sub apply simp
  unfolding size.simps by simp*)

subsection \<open>NegateNode\<close>

lemma val_distribute_sub: 
 "val[-(x-y)] \<approx> val[y-x]" 
  by (cases x; cases y; auto) 

optimization DistributeSub: "-(x-y) \<longmapsto> (y-x)" 
  using val_distribute_sub unfold_binary unfold_unary by auto

lemma val_xor_self_is_false:
  assumes "x = IntVal 32 v"
  shows "val[x ^ x] \<approx> val[false]"
  by (cases x; auto simp: assms)

definition wf_stamp :: "IRExpr \<Rightarrow> bool" where
  "wf_stamp e = (\<forall>m p v. ([m, p] \<turnstile> e \<mapsto> v) \<longrightarrow> valid_value v (stamp_expr e))"

lemma bit_wf_stamp:
  assumes "wf_stamp x"
  assumes "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
  assumes "stamp_expr x = IntegerStamp b' l h d u"
  shows "b = b'"
  using assms unfolding wf_stamp_def using valid_value.simps(1)
  using valid_value.elims(2) by fastforce

lemma exp_xor_self_is_false: 
  assumes "stamp_expr x = IntegerStamp 32 l h d u"
  assumes "wf_stamp x"
  shows "exp[x ^ x] \<ge> exp[false]"
  apply simp apply (rule allI)+ apply (rule impI)
  subgoal premises p for m p v
  proof -
    obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> IntVal 32 xv"
      using p bit_wf_stamp
      by (metis EvalTreeE(5) assms(1) assms(2) valid_value_elims(3) wf_stamp_def)
    then have e: "[m, p] \<turnstile> BinaryExpr BinXor x x \<mapsto> intval_xor (IntVal 32 xv) (IntVal 32 xv)"
      using p
      using evalDet by auto
    then have c: "[m, p] \<turnstile> (ConstantExpr (IntVal 32 0)) \<mapsto> (IntVal 32 0)"
      using wf_value_def valid_value.simps constantAsStamp.simps
      by (metis ConstantExpr IntVal0 Value.inject(1) eval_bits_1_64 new_int.simps validDefIntConst xv)
    have "intval_xor (IntVal 32 xv) (IntVal 32 xv) = IntVal 32 0"
      unfolding intval_xor.simps new_int_bin.simps by auto
    then show ?thesis using p e evalDet
      by (metis c)
  qed
  done

lemma val_or_commute[simp]:
   "val[x | y] = val[y | x]"
  by (cases x; cases y; auto simp: or.commute)

lemma val_xor_commute[simp]:
   "val[x ^ y] = val[y ^ x]"
  by (cases x; cases y; auto simp: word_bw_comms(3))

lemma val_and_commute[simp]:
   "val[x & y] = val[y & x]"
  by (cases x; cases y; auto simp: word_bw_comms(1))

lemma exp_or_commutative:
  "exp[x | y] \<ge> exp[y | x]"
  by auto 

lemma exp_xor_commutative:
  "exp[x ^ y] \<ge> exp[y ^ x]"
  by auto 

lemma exp_and_commutative:
  "exp[x & y] \<ge> exp[y & x]"
  by auto

(*
text \<open>--- --- New Optimisations - submitted and added into Graal ---\<close>
lemma OrInverseVal:
  assumes "n = IntVal 32 v"
  shows "val[n | ~n] \<approx> new_int 32 (-1)"
  apply (auto simp: assms)[1]
  by (metis bit.disj_cancel_right mask_eq_take_bit_minus_one take_bit_or)

optimization OrInverse: "exp[n | ~n] \<longmapsto> (const (new_int 32 (not 0)))
                        when (stamp_expr n = IntegerStamp 32 l h \<and> wf_stamp n)"
   apply (auto simp: Suc_lessI)[1]
  subgoal premises p for m p xa xaa
  proof -
    obtain nv where nv: "[m,p] \<turnstile> n \<mapsto> nv"
      using p(3) by auto
    obtain nbits nvv where nvv: "nv = IntVal nbits nvv"
      by (metis evalDet evaltree_not_undef intval_logic_negation.cases intval_not.simps(3,4,5) nv
          p(5,6))
    then have width: "nbits = 32"
      by (metis Value.inject(1) nv p(1,2) valid_int wf_stamp_def)
    then have stamp: "constantAsStamp (IntVal 32 (mask 32)) =
                  (IntegerStamp 32 (int_signed_value 32 (mask 32)) (int_signed_value 32 (mask 32)))"
      by auto
    have wf: "wf_value (IntVal 32 (mask 32))"
      unfolding wf_value_def stamp apply auto[1] by eval+
    then have unfoldOr: "val[nv | ~nv] = (new_int 32 (or (not nvv) nvv))"
      using intval_or.simps OrInverseVal nvv width by auto
    then have eq: "val[nv | ~nv] = new_int 32 (not 0)"
      by (simp add: unfoldOr)
    then show ?thesis
      by (metis bit.compl_zero evalDet local.wf new_int.elims nv p(3,5) take_bit_minus_one_eq_mask
          unfold_const)
  qed
  done

optimization OrInverse2: "exp[~n | n] \<longmapsto> (const (new_int 32 (not 0)))
                        when (stamp_expr n = IntegerStamp 32 l h \<and> wf_stamp n)"
   using OrInverse exp_or_commutative by auto

lemma XorInverseVal:
  assumes "n = IntVal 32 v"
  shows "val[n \<oplus> ~n] \<approx> new_int 32 (-1)"
  apply (auto simp: assms)[1]
  by (metis (no_types, opaque_lifting) bit.compl_zero bit.xor_compl_right bit.xor_self take_bit_xor
      mask_eq_take_bit_minus_one)

optimization XorInverse: "exp[n \<oplus> ~n] \<longmapsto> (const (new_int 32 (not 0)))
                        when (stamp_expr n = IntegerStamp 32 l h \<and> wf_stamp n)"
  apply (auto simp: Suc_lessI)[1]
  subgoal premises p for m p xa xaa
  proof-
    obtain xv where xv: "[m,p] \<turnstile> n \<mapsto> xv"
      using p(3) by auto
    obtain xb xvv where xvv: "xv = IntVal xb xvv"
      by (metis evalDet evaltree_not_undef intval_logic_negation.cases intval_not.simps(3,4,5) xv
          p(5,6))
    have rhsDefined: "[m,p] \<turnstile> (ConstantExpr (IntVal 32 (mask 32))) \<mapsto> (IntVal 32 (mask 32))"
      by (metis ConstantExpr add.right_neutral add_less_cancel_left neg_one_value numeral_Bit0
          new_int_unused_bits_zero not_numeral_less_zero validDefIntConst zero_less_numeral
          verit_comp_simplify1(3) wf_value_def)
    have w32: "xb=32"
      by (metis Value.inject(1) p(1,2) valid_int xv xvv wf_stamp_def)
    then have unfoldNot: "val[(\<not>xv)] = new_int xb (not xvv)"
      by (simp add: xvv)
    have unfoldXor: "val[xv \<oplus> (\<not>xv)] =
                    (if xb=xb then (new_int xb (xor xvv (not xvv))) else UndefVal)"
      using intval_xor.simps(1) XorInverseVal w32 xvv by auto
    then have rhs: "val[xv \<oplus> (\<not>xv)] = new_int 32 (mask 32)"
      using unfoldXor w32 by auto
    then show ?thesis
      by (metis evalDet neg_one.elims neg_one_value p(3,5) rhsDefined xv)
  qed
  done

optimization XorInverse2: "exp[(~n) \<oplus> n] \<longmapsto> (const (new_int 32 (not 0)))
                        when (stamp_expr n = IntegerStamp 32 l h \<and> wf_stamp n)"
   using XorInverse exp_xor_commutative by auto

lemma AndSelfVal:
  assumes "n = IntVal 32 v"
  shows "val[~n & n] = new_int 32 0"
  apply (auto simp: assms)[1]
  by (metis take_bit_and take_bit_of_0 word_and_not)

optimization AndSelf: "exp[(~n) & n] \<longmapsto> (const (new_int 32 (0)))
                        when (stamp_expr n = IntegerStamp 32 l h \<and> wf_stamp n)"
  apply (auto simp: Suc_lessI)[1] unfolding size.simps
  by (metis (no_types) val_and_commute ConstantExpr IntVal0 Value.inject(1) evalDet wf_stamp_def
      eval_bits_1_64 new_int.simps validDefIntConst valid_int wf_value_def AndSelfVal)

optimization AndSelf2: "exp[n & (~n)] \<longmapsto> (const (new_int 32 (0)))
                        when (stamp_expr n = IntegerStamp 32 l h \<and> wf_stamp n)"
  using AndSelf exp_and_commutative by auto

lemma NotXorToXorVal:
  assumes "x = IntVal 32 xv"
  assumes "y = IntVal 32 yv"
  shows "val[(~x) \<oplus> (~y)] = val[x \<oplus> y]" 
  apply (auto simp: assms)[1]
  by (metis (no_types, opaque_lifting) bit.xor_compl_left bit.xor_compl_right take_bit_xor 
      word_not_not) 

lemma NotXorToXorExp:
  assumes "stamp_expr x = IntegerStamp 32 lx hx"
  assumes "wf_stamp x"
  assumes "stamp_expr y = IntegerStamp 32 ly hy"
  assumes "wf_stamp y"
  shows "exp[(~x) \<oplus> (~y)] \<ge> exp[x \<oplus> y]" 
  apply auto[1]
  subgoal premises p for m p xa xb
    proof -
      obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
        using p by blast
      obtain xb where xb: "[m,p] \<turnstile> y \<mapsto> xb"
        using p by blast
      then have a: "val[(~xa) \<oplus> (~xb)] = val[xa \<oplus> xb]" 
        by (metis assms valid_int wf_stamp_def xa xb NotXorToXorVal)
      then show ?thesis
        by (metis BinaryExpr bin_eval.simps(8) evalDet p(1,2,4) xa xb)
    qed 
  done

optimization NotXorToXor: "exp[(~x) \<oplus> (~y)] \<longmapsto> (x \<oplus> y)
                        when (stamp_expr x = IntegerStamp 32 lx hx \<and> wf_stamp x) \<and>
                             (stamp_expr y = IntegerStamp 32 ly hy \<and> wf_stamp y)"
  using NotXorToXorExp by simp

end

text \<open>--- New optimisations - submitted, not added into Graal yet ---\<close>

context stamp_mask
begin

(* Extension to old Or optimisation 
   x | y \<mapsto> -1 when (downMask x | downMask y == -1)
*)

lemma ExpIntBecomesIntValArbitrary:
  assumes "stamp_expr x = IntegerStamp b xl xh"
  assumes "wf_stamp x"
  assumes "valid_value v (IntegerStamp b xl xh)"
  assumes "[m,p] \<turnstile> x \<mapsto> v"
  shows "\<exists>xv. v = IntVal b xv"
  using assms by (simp add: IRTreeEvalThms.valid_value_elims(3)) 

lemma OrGeneralization:
  assumes "stamp_expr x = IntegerStamp b xl xh"
  assumes "stamp_expr y = IntegerStamp b yl yh"
  assumes "stamp_expr exp[x | y] = IntegerStamp b el eh"
  assumes "wf_stamp x"
  assumes "wf_stamp y"
  assumes "wf_stamp exp[x | y]"
  assumes "(or (\<down>x) (\<down>y)) = not 0" 
  shows "exp[x | y] \<ge> exp[(const (new_int b (not 0)))]"
  using assms apply auto[1]
  subgoal premises p for m p xvv yvv
  proof -
    obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
      by (metis p(1,3,9) valid_int wf_stamp_def)
    obtain yv where yv: "[m, p] \<turnstile> y \<mapsto> IntVal b yv"
      by (metis p(2,4,10) valid_int wf_stamp_def)
    obtain evv where ev: "[m, p] \<turnstile> exp[x | y] \<mapsto> IntVal b evv"
      by (metis BinaryExpr bin_eval.simps(7) unfold_binary p(5,9,10,11) valid_int wf_stamp_def
          assms(3))
    then have rhsWf: "wf_value (new_int b (not 0))"
      by (metis eval_bits_1_64 new_int.simps new_int_take_bits validDefIntConst wf_value_def)
    then have rhs: "(new_int b (not 0)) = val[IntVal b xv | IntVal b yv]" 
      using assms word_ao_absorbs(1)
      by (metis (no_types, opaque_lifting) bit.de_Morgan_conj word_bw_comms(2) xv down_spec
          word_not_not yv bit.disj_conj_distrib intval_or.simps(1) new_int_bin.simps ucast_id
          or.right_neutral)
    then have notMaskEq: "(new_int b (not 0)) = (new_int b (mask b))"
      by auto
    then show ?thesis 
      by (metis neg_one.elims neg_one_value p(9,10) rhsWf unfold_const evalDet xv yv rhs)
    qed
    done
end

phase TacticSolving
  terminating size
begin

(* Add
   x + ~x \<mapsto> -1 
*)

lemma constEvalIsConst: 
  assumes "wf_value n"
  shows "[m,p] \<turnstile> exp[(const (n))] \<mapsto> n"  
  by (simp add: assms IRTreeEval.evaltree.ConstantExpr)

lemma ExpAddCommute:
  "exp[x + y] \<ge> exp[y + x]"
  by (auto simp add: Values.intval_add_sym)

lemma AddNotVal:
  assumes "n = IntVal bv v"
  shows "val[n + (~n)] = new_int bv (not 0)"
  by (auto simp: assms)

lemma AddNotExp:
  assumes "stamp_expr n = IntegerStamp b l h"
  assumes "wf_stamp n"
  shows "exp[n + (~n)] \<ge> exp[(const (new_int b (not 0)))]"
  apply auto[1]
  subgoal premises p for m p x xa
  proof -
    have xaDef: "[m,p] \<turnstile> n \<mapsto> xa"
      by (simp add: p)
    then have xaDef2: "[m,p] \<turnstile> n \<mapsto> x"
      by (simp add: p)
    then have "xa = x" 
      using p by (simp add: evalDet)
    then obtain xv where xv: "xa = IntVal b xv"
      by (metis valid_int wf_stamp_def xaDef2 assms)
    have toVal: "[m,p] \<turnstile> exp[n + (~n)] \<mapsto> val[xa + (~xa)]"
      by (metis UnaryExpr bin_eval.simps(1) evalDet p unary_eval.simps(3) unfold_binary xaDef)
    have wfInt: "wf_value (new_int b (not 0))"
      using validDefIntConst xaDef by (simp add: eval_bits_1_64 xv wf_value_def) 
    have toValRHS: "[m,p] \<turnstile> exp[(const (new_int b (not 0)))] \<mapsto> new_int b (not 0)"
      using wfInt by (simp add: constEvalIsConst)
    have isNeg1: "val[xa + (~xa)] = new_int b (not 0)"
      by (simp add: xv)
    then show ?thesis
      using toValRHS by (simp add: \<open>(xa::Value) = (x::Value)\<close>)
    qed 
   done

optimization AddNot: "exp[n + (~n)] \<longmapsto> (const (new_int b (not 0)))
                        when (stamp_expr n = IntegerStamp b l h \<and> wf_stamp n)"
   apply (simp add: Suc_lessI) using AddNotExp by force

optimization AddNot2: "exp[(~n) + n] \<longmapsto> (const (new_int b (not 0)))
                        when (stamp_expr n = IntegerStamp b l h \<and> wf_stamp n)"
   apply (simp add: Suc_lessI) using AddNot ExpAddCommute by simp

(* 
  ~e == e \<mapsto> false
 *)

lemma TakeBitNotSelf:
  "(take_bit 32 (not e) = e) = False"
  by (metis even_not_iff even_take_bit_eq zero_neq_numeral)

lemma ValNeverEqNotSelf:
  assumes "e = IntVal 32 ev"
  shows "val[intval_equals (\<not>e) e] = val[bool_to_val False]"
  by (simp add: TakeBitNotSelf assms)

lemma ExpIntBecomesIntVal:
  assumes "stamp_expr x = IntegerStamp 32 xl xh"
  assumes "wf_stamp x"
  assumes "valid_value v (IntegerStamp 32 xl xh)"
  assumes "[m,p] \<turnstile> x \<mapsto> v"
  shows "\<exists>xv. v = IntVal 32 xv"
  using assms by (simp add: IRTreeEvalThms.valid_value_elims(3)) 

lemma ExpNeverNotSelf:
  assumes "stamp_expr x = IntegerStamp 32 xl xh"
  assumes "wf_stamp x"
  shows "exp[BinaryExpr BinIntegerEquals (\<not>x) x] \<ge>
         exp[(const (bool_to_val False))]" 
  using assms apply auto[1]
  subgoal premises p for m p xa xaa
  proof -
    obtain xa where xa: "[m,p] \<turnstile> x \<mapsto> xa"
      using p(5) by auto
    then obtain xv where xv: "xa = IntVal 32 xv"
      by (metis p(1,2) valid_int wf_stamp_def)
    then have lhsVal: "[m,p] \<turnstile> exp[BinaryExpr BinIntegerEquals (\<not>x) x] \<mapsto> 
                               val[intval_equals (\<not>xa) xa]" 
      by (metis p(3,4,5,6) unary_eval.simps(3) evaltree.BinaryExpr bin_eval.simps(13) xa UnaryExpr 
          evalDet)
    have wfVal: "wf_value (IntVal 32 0)" 
      using wf_value_def
      by (metis IntVal0 intval_word.simps nat_le_linear new_int.simps numeral_le_iff wf_value_def
          semiring_norm(71,76) validDefIntConst verit_comp_simplify1(3) zero_less_numeral)
    then have rhsVal: "[m,p] \<turnstile> exp[(const (bool_to_val False))] \<mapsto> val[bool_to_val False]"
      by auto
    then have valEq: "val[intval_equals (\<not>xa) xa] = val[bool_to_val False]" 
      using ValNeverEqNotSelf by (simp add: xv)
    then show ?thesis
      by (metis bool_to_val.simps(2) evalDet p(3,5) rhsVal xa)
   qed
  done

optimization NeverEqNotSelf: "exp[BinaryExpr BinIntegerEquals (\<not>x) x] \<longmapsto> 
                              exp[(const (bool_to_val False))]
                        when (stamp_expr x = IntegerStamp 32 xl xh \<and> wf_stamp x)"
  apply (simp add: Suc_lessI) using ExpNeverNotSelf by force

text \<open>--- New optimisations - not submitted / added into Graal yet ---\<close>
(* 
  (x ^ y) == x \<mapsto> y == 0
  x == (x ^ y) \<mapsto> y == 0 
  (x ^ y) == y \<mapsto> x == 0 
  y == (x ^ y) \<mapsto> x == 0
 *)
lemma BinXorFallThrough:
  shows "bin[(x \<oplus> y) = x] \<longleftrightarrow> bin[y = 0]"
  by (metis xor.assoc xor.left_neutral xor_self_eq)

lemma valXorEqual:
  assumes "x = new_int 32 xv"
  assumes "val[x \<oplus> x] \<noteq> UndefVal"
  shows "val[x \<oplus> x] = val[new_int 32 0]"
  using assms by (cases x; auto)

lemma valXorAssoc:
  assumes "x = new_int b xv"
  assumes "y = new_int b yv"
  assumes "z = new_int b zv"
  assumes "val[(x \<oplus> y) \<oplus> z] \<noteq> UndefVal"
  assumes "val[x \<oplus> (y \<oplus> z)] \<noteq> UndefVal"
  shows "val[(x \<oplus> y) \<oplus> z] = val[x \<oplus> (y \<oplus> z)]"
  by (simp add: xor.commute xor.left_commute assms)

lemma valNeutral:
  assumes "x = new_int b xv"
  assumes "val[x \<oplus> (new_int b 0)] \<noteq> UndefVal"
  shows "val[x \<oplus> (new_int b 0)] = val[x]"
  using assms by (auto; meson)

lemma ValXorFallThrough:
  assumes "x = new_int b xv"
  assumes "y = new_int b yv"
  shows "val[intval_equals (x \<oplus> y) x] = val[intval_equals y (new_int b 0)]"
  by (simp add: assms BinXorFallThrough)

lemma ValEqAssoc:
  "val[intval_equals x y] = val[intval_equals y x]"
  apply (cases x; cases y; auto) by (metis (full_types) bool_to_val.simps)

lemma ExpEqAssoc:
  "exp[BinaryExpr BinIntegerEquals x y] \<ge> exp[BinaryExpr BinIntegerEquals y x]"
  by (auto simp add: ValEqAssoc)

lemma ExpXorBinEqCommute:
  "exp[BinaryExpr BinIntegerEquals (x \<oplus> y) y] \<ge> exp[BinaryExpr BinIntegerEquals (y \<oplus> x) y]"
  using exp_xor_commutative mono_binary by blast

lemma ExpXorFallThrough:
  assumes "stamp_expr x = IntegerStamp b xl xh"
  assumes "stamp_expr y = IntegerStamp b yl yh"
  assumes "wf_stamp x"
  assumes "wf_stamp y"
  shows "exp[BinaryExpr BinIntegerEquals (x \<oplus> y) x] \<ge>
         exp[BinaryExpr BinIntegerEquals y (const (new_int b 0))]"
  using assms apply auto[1]
  subgoal premises p for m p xa xaa ya
  proof -
    obtain b xv where xa: "[m,p] \<turnstile> x \<mapsto> new_int b xv"
      using intval_equals.elims 
      by (metis new_int.simps eval_unused_bits_zero p(1,3,5) wf_stamp_def valid_int)
    obtain yv where ya: "[m,p] \<turnstile> y \<mapsto> new_int b yv"
      by (metis Value.inject(1) wf_stamp_def p(1,2,3,4,8) eval_unused_bits_zero xa new_int.simps
          valid_int)
    then have wfVal: "wf_value (new_int b 0)"
      by (metis eval_bits_1_64 new_int.simps new_int_take_bits validDefIntConst wf_value_def xa)
    then have eval: "[m,p] \<turnstile> exp[BinaryExpr BinIntegerEquals y (const (new_int b 0))] \<mapsto> 
                             val[intval_equals (xa \<oplus> ya) xa]" 
      by (metis (no_types, lifting) ValXorFallThrough constEvalIsConst bin_eval.simps(13) evalDet xa
          p(5,6,7,8) unfold_binary ya)
    then show ?thesis
      by (metis evalDet new_int.elims p(1,3,5,7) take_bit_of_0 valid_value.simps(1) wf_stamp_def xa)
   qed 
  done

lemma ExpXorFallThrough2:
  assumes "stamp_expr x = IntegerStamp b xl xh"
  assumes "stamp_expr y = IntegerStamp b yl yh"
  assumes "wf_stamp x"
  assumes "wf_stamp y"
  shows "exp[BinaryExpr BinIntegerEquals (x \<oplus> y) y] \<ge>
         exp[BinaryExpr BinIntegerEquals x (const (new_int b 0))]"
  by (meson assms dual_order.trans ExpXorBinEqCommute ExpXorFallThrough)

optimization XorFallThrough1: "exp[BinaryExpr BinIntegerEquals (x \<oplus> y) x] \<longmapsto> 
                               exp[BinaryExpr BinIntegerEquals y (const (new_int b 0))]
                        when (IsIntegerStamp x && WellFormed x) && 
                             (IsIntegerStamp x && WellFormed y)"
  using ExpXorFallThrough by force

optimization XorFallThrough2: "exp[BinaryExpr BinIntegerEquals x (x \<oplus> y)] \<longmapsto> 
                               exp[BinaryExpr BinIntegerEquals y (const (new_int b 0))]
                        when (stamp_expr x = IntegerStamp b xl xh \<and> wf_stamp x) \<and> 
                             (stamp_expr y = IntegerStamp b yl yh \<and> wf_stamp y)"
  using ExpXorFallThrough ExpEqAssoc by force

optimization XorFallThrough3: "exp[BinaryExpr BinIntegerEquals (x \<oplus> y) y] \<longmapsto> 
                               exp[BinaryExpr BinIntegerEquals x (const (new_int b 0))]
                        when (stamp_expr x = IntegerStamp b xl xh \<and> wf_stamp x) \<and> 
                             (stamp_expr y = IntegerStamp b yl yh \<and> wf_stamp y)"
  using ExpXorFallThrough2 by force

optimization XorFallThrough4: "exp[BinaryExpr BinIntegerEquals y (x \<oplus> y)] \<longmapsto> 
                               exp[BinaryExpr BinIntegerEquals x (const (new_int b 0))]
                        when (stamp_expr x = IntegerStamp b xl xh \<and> wf_stamp x) \<and> 
                             (stamp_expr y = IntegerStamp b yl yh \<and> wf_stamp y)"
  using ExpXorFallThrough2 ExpEqAssoc by force

end

context stamp_mask
begin

(* Ian's optimisation, and it's Or equivalent
    x & y \<mapsto> x when x.up \<in> y.Down
    x | y \<mapsto> y when x.up \<in> y.Down

    x.up \<in> y.Down means (x.up & y.Down = x.up), 
               equiv to (x.up | y.Down = y.Down)
*)

lemma inEquivalence:
  assumes "[m, p] \<turnstile> y \<mapsto> IntVal b yv"
  assumes "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
  shows "(and (\<up>x) yv) = (\<up>x) \<longleftrightarrow> (or (\<up>x) yv) = yv"
  by (metis word_ao_absorbs(3) word_ao_absorbs(4))

lemma inEquivalence2:
  assumes "[m, p] \<turnstile> y \<mapsto> IntVal b yv"
  assumes "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
  shows "(and (\<up>x) (\<down>y)) = (\<up>x) \<longleftrightarrow> (or (\<up>x) (\<down>y)) = (\<down>y)"
  by (metis word_ao_absorbs(3) word_ao_absorbs(4))

(* x | y \<mapsto> y when x.up \<in> y.Down *)
lemma RemoveLHSOrMask:
  assumes "(and (\<up>x) (\<down>y)) = (\<up>x)"
  assumes "(or (\<up>x) (\<down>y)) = (\<down>y)"
  shows "exp[x | y] \<ge> exp[y]"
  using assms apply auto[1]
  subgoal premises p for m p v
  proof -
    obtain b ev where exp: "[m, p] \<turnstile> exp[x | y] \<mapsto> IntVal b ev" 
      by (metis BinaryExpr bin_eval.simps(7) p(3,4,5) bin_eval_new_int new_int.simps)
    from exp obtain yv where yv: "[m, p] \<turnstile> y \<mapsto> IntVal b yv"
      apply (subst (asm) unfold_binary_width) by force+
    from exp obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
      apply (subst (asm) unfold_binary_width) by force+
    then have "yv = (or xv yv)"
      using assms yv xv apply auto[1]
      by (metis (no_types, opaque_lifting) down_spec ucast_id up_spec word_ao_absorbs(1) word_or_not
          word_ao_equiv word_log_esimps(3) word_oa_dist word_oa_dist2)
    then have "(IntVal b yv) = val[(IntVal b xv) | (IntVal b yv)]"
      apply auto[1] using eval_unused_bits_zero yv by presburger
    then show ?thesis    
      by (metis p(3,4) evalDet xv yv)
  qed
  done

(* x & y \<mapsto> x when x.up \<in> y.Down *)
lemma RemoveRHSAndMask:
  assumes "(and (\<up>x) (\<down>y)) = (\<up>x)"
  assumes "(or (\<up>x) (\<down>y)) = (\<down>y)"
  shows "exp[x & y] \<ge> exp[x]"
  using assms apply auto[1]
  subgoal premises p for m p v
  proof -
    obtain b ev where exp: "[m, p] \<turnstile> exp[x & y] \<mapsto> IntVal b ev"
      by (metis BinaryExpr bin_eval.simps(6) p(3,4,5) new_int.simps bin_eval_new_int)
    from exp obtain yv where yv: "[m, p] \<turnstile> y \<mapsto> IntVal b yv"
      apply (subst (asm) unfold_binary_width) by force+
    from exp obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
      apply (subst (asm) unfold_binary_width) by force+
    then have "IntVal b xv = val[(IntVal b xv) & (IntVal b yv)]"
      apply auto [1]
      by (smt (verit, ccfv_threshold) or.right_neutral not_down_up_mask_and_zero_implies_zero p(1)
          bit.conj_cancel_right word_bw_comms(1) eval_unused_bits_zero yv word_bw_assocs(1)
          word_ao_absorbs(4) or_eq_not_not_and)
    then show ?thesis     
      by (metis p(3,4) yv xv evalDet)
   qed
  done

(* Ian's new And optimisation
    x & y \<mapsto> 0 when x.up & y.up = 0
*)
lemma ReturnZeroAndMask:
  assumes "stamp_expr x = IntegerStamp b xl xh"
  assumes "stamp_expr y = IntegerStamp b yl yh"
  assumes "stamp_expr exp[x & y] = IntegerStamp b el eh"
  assumes "wf_stamp x"
  assumes "wf_stamp y"
  assumes "wf_stamp exp[x & y]"
  assumes "(and (\<up>x) (\<up>y)) = 0"
  shows "exp[x & y] \<ge> exp[const (new_int b 0)]"
  using assms apply auto[1]
  subgoal premises p for m p v
  proof -
    obtain yv where yv: "[m, p] \<turnstile> y \<mapsto> IntVal b yv"
      by (metis valid_int wf_stamp_def assms(2,5) p(2,4,10) wf_stamp_def)
    obtain xv where xv: "[m, p] \<turnstile> x \<mapsto> IntVal b xv"
      by (metis valid_int wf_stamp_def assms(1,4) p(3,9) wf_stamp_def)
    obtain ev where exp: "[m, p] \<turnstile> exp[x & y] \<mapsto> IntVal b ev"
      by (metis BinaryExpr bin_eval.simps(6) p(5,9,10,11) assms(3) valid_int wf_stamp_def)
    then have wfVal: "wf_value (new_int b 0)"
      by (metis eval_bits_1_64 new_int.simps new_int_take_bits validDefIntConst wf_value_def)
    then have lhsEq: "IntVal b ev = val[(IntVal b xv) & (IntVal b yv)]"
      by (metis bin_eval.simps(6) yv xv evalDet exp unfold_binary)
    then have newIntEquiv: "new_int b 0 = IntVal b ev" 
      apply auto[1] by (smt (z3) p(6) eval_unused_bits_zero xv yv up_mask_and_zero_implies_zero)
    then have isZero: "ev = 0"
      by auto
    then show ?thesis
      by (metis evalDet lhsEq newIntEquiv p(9,10) unfold_const wfVal xv yv)
   qed
   done

end

phase TacticSolving
  terminating size
begin


(* 
 (x ^ y) == (x ^ z) \<mapsto> y == z
 (x ^ y) == (z ^ x) \<mapsto> y == z
 (y ^ x) == (x ^ z) \<mapsto> y == z
 (y ^ x) == (z ^ x) \<mapsto> y == z
 *)

lemma binXorIsEqual:
  "bin[((x \<oplus> y) = (x \<oplus> z))] \<longleftrightarrow> bin[(y = z)]"
  by (metis (no_types, opaque_lifting) BinXorFallThrough xor.left_commute xor_self_eq)

lemma binXorIsDeterministic:
  assumes "y \<noteq> z"
  shows "bin[x \<oplus> y] \<noteq> bin[x \<oplus> z]"
  by (auto simp add: binXorIsEqual assms)

lemma ValXorSelfIsZero:
  assumes "x = IntVal b xv"
  shows "val[x \<oplus> x] = IntVal b 0" 
  by (simp add: assms)

lemma ValXorSelfIsZero2:
  assumes "x = new_int b xv"
  shows "val[x \<oplus> x] = IntVal b 0" 
  by (simp add: assms)

lemma ValXorIsAssociative:
  assumes "x = IntVal b xv"
  assumes "y = IntVal b yv"
  assumes "val[(x \<oplus> y)] \<noteq> UndefVal"
  shows "val[(x \<oplus> y) \<oplus> y] = val[x \<oplus> (y \<oplus> y)]"
  by (auto simp add: word_bw_lcs(3) assms) 

lemma ValXorIsAssociative2:
  assumes "x = new_int b xv"
  assumes "y = new_int b yv"
  assumes "val[(x \<oplus> y)] \<noteq> UndefVal"
  shows "val[(x \<oplus> y) \<oplus> y] = val[x \<oplus> (y \<oplus> y)]"
  using ValXorIsAssociative by (simp add: assms)

lemma XorZeroIsSelf64:
  assumes "x = IntVal 64 xv"
  assumes "val[x \<oplus> (IntVal 64 0)] \<noteq> UndefVal"
  shows  "val[x \<oplus> (IntVal 64 0)] = x" 
  using assms apply (cases x; auto)
  subgoal
  proof -
    have "take_bit (LENGTH(64)) xv = xv"
      unfolding Word.take_bit_length_eq by simp
    then show ?thesis
      by auto
   qed
  done

lemma ValXorElimSelf64:
  assumes "x = IntVal 64 xv"
  assumes "y = IntVal 64 yv"
  assumes "val[x \<oplus> y] \<noteq> UndefVal"
  assumes "val[y \<oplus> y] \<noteq> UndefVal"
  shows "val[x \<oplus> (y \<oplus> y)] = x"
  proof -
    have removeRhs: "val[x \<oplus> (y \<oplus> y)] = val[x \<oplus> (IntVal 64 0)]"
      by (simp add: assms(2))
    then have XorZeroIsSelf: "val[x \<oplus> (IntVal 64 0)] = x"
      using XorZeroIsSelf64 by (simp add: assms(1))
    then show ?thesis
      by (simp add: removeRhs)
  qed

lemma ValXorIsReverse64:
  assumes "x = IntVal 64 xv"
  assumes "y = IntVal 64 yv"
  assumes "z = IntVal 64 zv"
  assumes "z = val[x \<oplus> y]"
  assumes "val[x \<oplus> y] \<noteq> UndefVal"
  assumes "val[z \<oplus> y] \<noteq> UndefVal"
  shows "val[z \<oplus> y] = x"
  using ValXorIsAssociative ValXorElimSelf64 assms(1,2,4,5) by force

lemma valXorIsEqual_64:
  assumes "x = IntVal 64 xv"
  assumes "val[x \<oplus> y] \<noteq> UndefVal"
  assumes "val[x \<oplus> z] \<noteq> UndefVal"
  shows "val[intval_equals (x \<oplus> y) (x \<oplus> z)] = val[intval_equals y z]"
  using assms apply (cases x; cases y; cases z; auto)
  subgoal premises p for yv zv apply (cases "(yv = zv)"; simp)
  subgoal premises p
  proof -
    have isFalse: "bool_to_val (yv = zv) = bool_to_val False"
      by (simp add: p)
    then have unfoldTakebityv: "take_bit LENGTH(64) yv = yv"
      using take_bit_length_eq by blast
    then have unfoldTakebitzv: "take_bit LENGTH(64) zv = zv"
      using take_bit_length_eq by blast
    then have unfoldTakebitxv: "take_bit LENGTH(64) xv = xv"
      using take_bit_length_eq by blast
    then have lhs: "(xor (take_bit LENGTH(64) yv) (take_bit LENGTH(64) xv) =
                     xor (take_bit LENGTH(64) zv) (take_bit LENGTH(64) xv)) = (False)"
      unfolding unfoldTakebityv unfoldTakebitzv unfoldTakebitxv
      by (simp add: binXorIsEqual word_bw_comms(3) p)
    then show ?thesis
      by (simp add: isFalse)
    qed
   done
  done

lemma ValXorIsDeterministic_64:
  assumes "x = IntVal 64 xv"
  assumes "y = IntVal 64 yv"
  assumes "z = IntVal 64 zv"
  assumes "val[x \<oplus> y] \<noteq> UndefVal"
  assumes "val[x \<oplus> z] \<noteq> UndefVal"
  assumes "yv \<noteq> zv"
  shows "val[x \<oplus> y] \<noteq> val[x \<oplus> z]" 
  by (smt (verit, best) ValXorElimSelf64 ValXorIsAssociative ValXorSelfIsZero Value.distinct(1)
      assms Value.inject(1) val_xor_commute valXorIsEqual_64)

lemma ExpIntBecomesIntVal_64:
  assumes "stamp_expr x = IntegerStamp 64 xl xh"
  assumes "wf_stamp x"
  assumes "valid_value v (IntegerStamp 64 xl xh)"
  assumes "[m,p] \<turnstile> x \<mapsto> v"
  shows "\<exists>xv. v = IntVal 64 xv"
  using assms by (simp add: IRTreeEvalThms.valid_value_elims(3)) 

lemma expXorIsEqual_64:
  assumes "stamp_expr x = IntegerStamp 64 xl xh"
  assumes "stamp_expr y = IntegerStamp 64 yl yh"
  assumes "stamp_expr z = IntegerStamp 64 zl zh"
  assumes "wf_stamp x"
  assumes "wf_stamp y"
  assumes "wf_stamp z"
    shows "exp[BinaryExpr BinIntegerEquals (x \<oplus> y) (x \<oplus> z)] \<ge>
           exp[BinaryExpr BinIntegerEquals y z]"
  using assms apply auto[1]
  subgoal premises p for m p x1 y1 x2 z1
  proof -
    obtain xVal where xVal: "[m,p] \<turnstile> x \<mapsto> xVal"
      using p(8) by simp
    obtain yVal where yVal: "[m,p] \<turnstile> y \<mapsto> yVal"
      using p(9) by simp
    obtain zVal where zVal: "[m,p] \<turnstile> z \<mapsto> zVal"
      using p(12) by simp
    obtain xv where xv: "xVal = IntVal 64 xv"
      by (metis p(1) p(4) wf_stamp_def xVal ExpIntBecomesIntVal_64)
    then have rhs: "[m,p] \<turnstile> exp[BinaryExpr BinIntegerEquals y z] \<mapsto> val[intval_equals yVal zVal]"
      by (metis BinaryExpr bin_eval.simps(13) evalDet p(7,8,9,10,11,12,13) valXorIsEqual_64 xVal 
          yVal zVal)
    then show ?thesis
      by (metis xv evalDet p(8,9,10,11,12,13) valXorIsEqual_64 xVal yVal zVal)
  qed
  done

(* 64 bit versions *)
optimization XorIsEqual_64_1: "exp[BinaryExpr BinIntegerEquals (x \<oplus> y) (x \<oplus> z)] \<longmapsto> 
                             exp[BinaryExpr BinIntegerEquals y z]
                        when (stamp_expr x = IntegerStamp 64 xl xh \<and> wf_stamp x) \<and> 
                             (stamp_expr y = IntegerStamp 64 yl yh \<and> wf_stamp y) \<and> 
                             (stamp_expr z = IntegerStamp 64 zl zh \<and> wf_stamp z)"
  using expXorIsEqual_64 by force

optimization XorIsEqual_64_2: "exp[BinaryExpr BinIntegerEquals (x \<oplus> y) (z \<oplus> x)] \<longmapsto> 
                             exp[BinaryExpr BinIntegerEquals y z]
                        when (stamp_expr x = IntegerStamp 64 xl xh \<and> wf_stamp x) \<and> 
                             (stamp_expr y = IntegerStamp 64 yl yh \<and> wf_stamp y) \<and> 
                             (stamp_expr z = IntegerStamp 64 zl zh \<and> wf_stamp z)" 
  by (meson dual_order.trans mono_binary exp_xor_commutative expXorIsEqual_64) 

optimization XorIsEqual_64_3: "exp[BinaryExpr BinIntegerEquals (y \<oplus> x) (x \<oplus> z)] \<longmapsto> 
                             exp[BinaryExpr BinIntegerEquals y z]
                        when (stamp_expr x = IntegerStamp 64 xl xh \<and> wf_stamp x) \<and> 
                             (stamp_expr y = IntegerStamp 64 yl yh \<and> wf_stamp y) \<and> 
                             (stamp_expr z = IntegerStamp 64 zl zh \<and> wf_stamp z)"
  by (meson dual_order.trans mono_binary exp_xor_commutative expXorIsEqual_64) 

optimization XorIsEqual_64_4: "exp[BinaryExpr BinIntegerEquals (y \<oplus> x) (z \<oplus> x)] \<longmapsto> 
                             exp[BinaryExpr BinIntegerEquals y z]
                        when (stamp_expr x = IntegerStamp 64 xl xh \<and> wf_stamp x) \<and> 
                             (stamp_expr y = IntegerStamp 64 yl yh \<and> wf_stamp y) \<and> 
                             (stamp_expr z = IntegerStamp 64 zl zh \<and> wf_stamp z)"
  by (meson dual_order.trans mono_binary exp_xor_commutative expXorIsEqual_64) 

(*
XorEqZero
  (x ^ y) == 0 \<mapsto> (x == y)
 *)

lemma unwrap_bool_to_val:
  shows "(bool_to_val a = bool_to_val b) = (a = b)"
  apply auto[1] using bool_to_val.elims by fastforce+

lemma take_bit_size_eq:
  shows "take_bit 64 a = take_bit LENGTH(64) (a::64 word)"
  by auto

lemma xorZeroIsEq:
  "bin[(xor xv yv) = 0] = bin[xv = yv]"
  by (metis binXorIsEqual xor_self_eq)

lemma valXorEqZero_64:
  assumes "val[(x \<oplus> y)] \<noteq> UndefVal"
  assumes "x = IntVal 64 xv"
  assumes "y = IntVal 64 yv"
  shows "val[intval_equals (x \<oplus> y) ((IntVal 64 0))] = val[intval_equals (x) (y)]"
  using assms apply (cases x; cases y; auto)
  unfolding unwrap_bool_to_val take_bit_size_eq Word.take_bit_length_eq by (simp add: xorZeroIsEq)

lemma expXorEqZero_64:
  assumes "stamp_expr x = IntegerStamp 64 xl xh"
  assumes "stamp_expr y = IntegerStamp 64 yl yh"
  assumes "wf_stamp x"
  assumes "wf_stamp y"
    shows "exp[BinaryExpr BinIntegerEquals (x \<oplus> y) (const (IntVal 64 0))] \<ge>
           exp[BinaryExpr BinIntegerEquals (x) (y)]"
  using assms apply auto[1]
  subgoal premises p for m p x1 y1
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p by blast
    obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> yv"
      using p by fast
    obtain xvv where xvv: "xv = IntVal 64 xvv"
      by (metis p(1,3) wf_stamp_def xv ExpIntBecomesIntVal_64)
    obtain yvv where yvv: "yv = IntVal 64 yvv"
      by (metis p(2,4) wf_stamp_def yv ExpIntBecomesIntVal_64)
    have rhs: "[m,p] \<turnstile> exp[BinaryExpr BinIntegerEquals (x) (y)] \<mapsto> val[intval_equals xv yv]"
      by (smt (z3) BinaryExpr ValEqAssoc ValXorSelfIsZero Value.distinct(1) bin_eval.simps(13) xvv
          evalDet p(5,6,7,8) valXorIsEqual_64 xv yv)
    then show ?thesis
      by (metis evalDet p(6,7,8) valXorEqZero_64 xv xvv yv yvv)
  qed
  done

optimization XorEqZero_64: "exp[BinaryExpr BinIntegerEquals (x \<oplus> y) (const (IntVal 64 0))] \<longmapsto>
                            exp[BinaryExpr BinIntegerEquals (x) (y)]
                      when (stamp_expr x = IntegerStamp 64 xl xh \<and> wf_stamp x) \<and>
                           (stamp_expr y = IntegerStamp 64 yl yh \<and> wf_stamp y)"
  using expXorEqZero_64 by fast

(*
XorEqNeg1
  (x ^ y) == -1 \<mapsto> (x == \<not>y)
 *)

lemma xorNeg1IsEq:
  "bin[(xor xv yv) = (not 0)] = bin[xv = not yv]"
  using xorZeroIsEq by fastforce

lemma valXorEqNeg1_64:
  assumes "val[(x \<oplus> y)] \<noteq> UndefVal"
  assumes "x = IntVal 64 xv"
  assumes "y = IntVal 64 yv"
  shows "val[intval_equals (x \<oplus> y) (IntVal 64 (not 0))] = val[intval_equals (x) (\<not>y)]"
  using assms apply (cases x; cases y; auto)
  unfolding unwrap_bool_to_val take_bit_size_eq Word.take_bit_length_eq using xorNeg1IsEq by auto

lemma expXorEqNeg1_64:
  assumes "stamp_expr x = IntegerStamp 64 xl xh"
  assumes "stamp_expr y = IntegerStamp 64 yl yh"
  assumes "wf_stamp x"
  assumes "wf_stamp y"
    shows "exp[BinaryExpr BinIntegerEquals (x \<oplus> y) (const (IntVal 64 (not 0)))] \<ge>
           exp[BinaryExpr BinIntegerEquals (x) (\<not>y)]"
  using assms apply auto[1]
  subgoal premises p for m p x1 y1
  proof -
    obtain xv where xv: "[m,p] \<turnstile> x \<mapsto> xv"
      using p by blast
    obtain yv where yv: "[m,p] \<turnstile> y \<mapsto> yv"
      using p by fast
    obtain xvv where xvv: "xv = IntVal 64 xvv"
      by (metis p(1,3) wf_stamp_def xv ExpIntBecomesIntVal_64)
    obtain yvv where yvv: "yv = IntVal 64 yvv"
      by (metis p(2,4) wf_stamp_def yv ExpIntBecomesIntVal_64)
    obtain nyv where nyv: "[m,p] \<turnstile> exp[(\<not>y)] \<mapsto> nyv"
      by (metis ValXorSelfIsZero2 Value.distinct(1) intval_not.simps(1) yv yvv intval_xor.simps(2)
          UnaryExpr unary_eval.simps(3))
    then have nyvEq: "val[\<not>yv] = nyv"
      using evalDet yv by fastforce
    obtain nyvv where nyvv: "nyv = IntVal 64 nyvv"
      using nyvEq intval_not.simps yvv by force
    have notUndef: "val[intval_equals xv (\<not>yv)] \<noteq> UndefVal"
      using bool_to_val.elims nyvEq nyvv xvv by auto
    have rhs: "[m,p] \<turnstile> exp[BinaryExpr BinIntegerEquals (x) (\<not>y)] \<mapsto> val[intval_equals xv (\<not>yv)]"
      by (metis BinaryExpr bin_eval.simps(13) notUndef nyv nyvEq xv)
    then show ?thesis
      by (metis bit.compl_zero evalDet p(6,7,8) rhs valXorEqNeg1_64 xvv yvv xv yv)
  qed
  done

optimization XorEqNeg1_64: "exp[BinaryExpr BinIntegerEquals (x \<oplus> y) (const (IntVal 64 (not 0)))] \<longmapsto>
                            exp[BinaryExpr BinIntegerEquals (x) (\<not>y)]
                      when (stamp_expr x = IntegerStamp 64 xl xh \<and> wf_stamp x) \<and>
                           (stamp_expr y = IntegerStamp 64 yl yh \<and> wf_stamp y)"
  using expXorEqNeg1_64 apply auto (* termination proof *) sorry
*)

end

end