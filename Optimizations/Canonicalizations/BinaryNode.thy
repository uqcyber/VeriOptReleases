subsection \<open>BinaryNode Phase\<close>

theory BinaryNode
  imports
    Common
begin

phase BinaryNode 
  terminating size
begin

optimization BinaryFoldConstant[nogen]: "BinaryExpr op (const v1) (const v2) \<longmapsto> ConstantExpr (bin_eval op v1 v2)"
  unfolding le_expr_def
  apply (rule allI impI)+
  subgoal premises bin for m p v
    apply (rule BinaryExprE[OF bin])
    subgoal premises prems for x y
    proof -
      have x: "x = v1" 
        using prems by auto
      have y: "y = v2" 
        using prems by auto
      have xy: "v = bin_eval op x y" 
        by (simp add: prems x y)
      have int: "\<exists> b vv . v = new_int b vv" 
        using bin_eval_new_int prems by fast
      show ?thesis
        by (metis ConstantExpr prems(1) x y int bin eval_bits_1_64 new_int.simps new_int_take_bits 
            wf_value_def validDefIntConst)
      qed
    done
  done

end

end