section \<open>Graph Type Class Instantiations\<close>

theory
  IRGraphSort
imports
  Graph.IRGraph
begin

text \<open>
An @{typ IRGraph} can be treated as an instantiation of
various type classes such as the equal type class.

Here we define the instantiations for all type classes
of which @{typ IRGraph} belongs.
\<close>


subsection \<open>Equal Instance\<close>
text \<open>
The following is an incorrect definition of equality
which is used to allow code generation of the Canonicalization
phase. Without this we have to use the values command to generate
all possible results of the canonicalization phase.

Note that we should be able to find a correct equality definition
in terms of the ids, kind, and stamp function. However, we are
yet to find a satisfactory definition as yet.
\<close>
definition IRGraph_equal :: "IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool" where
  "IRGraph_equal g1 g2 = (as_set g1 = as_set g2)"

lemma graph_eq:
  fixes g1 g2 :: IRGraph
  shows "g1 = g2 \<longleftrightarrow> IRGraph_equal g1 g2"
  unfolding IRGraph_equal_def sorry

instantiation IRGraph :: equal
begin

definition equal_IRGraph :: "IRGraph \<Rightarrow> IRGraph \<Rightarrow> bool" where
  "equal_IRGraph = IRGraph_equal"

instance proof
  fix g1 g2 :: IRGraph
  show "equal_class.equal g1 g2 \<longleftrightarrow> (g1 = g2)"
    apply standard
    unfolding equal_IRGraph_def using graph_eq by auto
qed
end

end