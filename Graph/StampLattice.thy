section \<open>Stamps: Type and Range Information\<close>

theory StampLattice
imports
  Values
  HOL.Lattices
begin

subsection \<open>Void Stamp\<close>
text \<open>
The VoidStamp represents a type with no associated values.
The VoidStamp lattice is therefore a simple single element lattice.
\<close>
datatype void =
  VoidStamp

instantiation void :: order
begin

definition less_eq_void :: "void \<Rightarrow> void \<Rightarrow> bool" where
  "less_eq_void a b = True"

definition less_void :: "void \<Rightarrow> void \<Rightarrow> bool" where
  "less_void a b = False"

instance
  apply standard
  apply (simp add: less_eq_void_def less_void_def)+
  by (metis (full_types) void.exhaust)

end

instantiation void :: semilattice_inf
begin

definition inf_void :: "void \<Rightarrow> void \<Rightarrow> void" where
  "inf_void a b = VoidStamp"

instance
  apply standard
  by (simp add: less_eq_void_def)+

end

instantiation void :: semilattice_sup
begin

definition sup_void :: "void \<Rightarrow> void \<Rightarrow> void" where
  "sup_void a b = VoidStamp"

instance
  apply standard
  by (simp add: less_eq_void_def)+

end

instantiation void :: bounded_lattice
begin

definition bot_void :: "void" where
  "bot_void = VoidStamp"

definition top_void :: "void" where
  "top_void = VoidStamp"

instance
  apply standard
  by (simp add: less_eq_void_def)+

end

text \<open>Definition of the stamp type\<close>
datatype stamp =
  intstamp int64 int64 \<comment>\<open>Type: Integer; Range: Lower Bound \& Upper Bound\<close>
(*
  | floatstamp \<comment>\<open>Type: Float; Range: Lower Bound \& Upper Bound\<close>
  | objectstamp classname \<comment>\<open>Type: Object Instance; Range: Upper Bound Superclass\<close>
*)

subsection \<open>Stamp Lattice\<close>

text_raw \<open>\input{lattice}\\\<close>

subsubsection \<open>Stamp Order\<close>
text \<open>
Defines an ordering on the stamp type.

One stamp is less than another if the valid values
for the stamp are a strict subset of the other stamp.
\<close>
instantiation stamp :: order
begin

fun less_eq_stamp :: "stamp \<Rightarrow> stamp \<Rightarrow> bool" where
  "less_eq_stamp (intstamp l1 u1) (intstamp l2 u2) = ({l1..u1} \<subseteq> {l2..u2})"

fun less_stamp :: "stamp \<Rightarrow> stamp \<Rightarrow> bool" where
  "less_stamp (intstamp l1 u1) (intstamp l2 u2) = ({l1..u1} \<subset> {l2..u2})"

lemma less_le_not_le:
  fixes x y :: stamp
  shows "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
  by (metis subset_not_subset_eq stamp.exhaust less_stamp.simps less_eq_stamp.simps)

lemma order_refl:
  fixes x :: stamp
  shows "x \<le> x"
  by (metis stamp.exhaust dual_order.refl less_eq_stamp.simps)

lemma order_trans:
  fixes x y z :: stamp
  shows "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
proof -
  fix x :: stamp and y :: stamp and z :: stamp
  assume "x \<le> y"
  assume "y \<le> z"
  obtain l1 u1 where xdef: "x = intstamp l1 u1"
    using stamp.exhaust by auto
  obtain l2 u2 where ydef: "y = intstamp l2 u2"
    using stamp.exhaust by auto
  obtain l3 u3 where zdef: "z = intstamp l3 u3"
    using stamp.exhaust by auto
  have s1: "{l1..u1} \<le> {l2..u2}"
    using \<open>x \<le> y\<close> by (simp add: ydef xdef)
  have s2: "{l2..u2} \<le> {l3..u3}"
    using \<open>y \<le> z\<close> by (simp add: zdef ydef)
  from s1 s2 have "{l1..u1} \<le> {l3..u3}"
    by (meson dual_order.trans)
  then show "x \<le> z"
    by (simp add: zdef xdef)
qed

lemma antisym:
  fixes x y :: stamp
  shows "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
proof -
  fix x :: stamp
  fix y :: stamp
  assume xlessy: "x \<le> y"
  assume ylessx: "y \<le> x"
  obtain l1 u1 where xdef: "x = intstamp l1 u1"
    using stamp.exhaust by auto
  obtain l2 u2 where ydef: "y = intstamp l2 u2"
    using stamp.exhaust by auto
  from xlessy have s1: "{l1..u1} \<subseteq> {l2..u2}"
    by (simp add: ydef xdef)
  from ylessx have s2: "{l2..u2} \<subseteq> {l1..u1}"
    by (simp add: ydef xdef)
  have "{l1..u1} \<subseteq> {l2..u2} \<Longrightarrow> {l2..u2} \<subseteq> {l1..u1} \<Longrightarrow> {l1..u1} = {l2..u2}"
    by auto
  then have s3: "{l1..u1} = {l2..u2} \<Longrightarrow> (l1 = l2) \<and> (u1 = u2)"
    (* not true *)
    (* consider: 
       {1..0} = {-1..-1}
    *)
    sorry
  then have "(l1 = l2) \<and> (u1 = u2) \<Longrightarrow> x = y"
    using xdef ydef by fastforce
  then show "x = y"
    using s1 s2 s3 by fastforce
qed

instance
  apply standard
  by (simp add: antisym order_trans order_refl less_le_not_le)+
end

subsubsection \<open>Stamp Join\<close>
text \<open>
Defines the @{emph \<open>join\<close>} operation for stamps.

For any two stamps, the @{emph \<open>join\<close>} is defined as the intersection
of the valid values for the stamp.
\<close>
instantiation stamp :: semilattice_inf
begin

notation inf (infix "\<sqinter>" 65)

fun inf_stamp :: "stamp \<Rightarrow> stamp \<Rightarrow> stamp" where
  "inf_stamp (intstamp l1 u1) (intstamp l2 u2) = intstamp (max l1 l2) (min u1 u2)"

lemma inf_le1: 
  fixes x y :: stamp
  shows "(x \<sqinter> y) \<le> x"
proof -
  fix x :: stamp
  fix y :: stamp
  obtain l1 u1 where xdef: "x = intstamp l1 u1"
    using stamp.exhaust by auto
  obtain l2 u2 where ydef: "y = intstamp l2 u2"
    using stamp.exhaust by auto
  have joindef: "x \<sqinter> y = intstamp (max l1 l2) (min u1 u2)"
    (is "?join = intstamp ?l3 ?u3")
    by (simp add: ydef xdef)
  have leq: "{?l3..?u3} \<subseteq> {l1..u1}"
    by simp
  have "(x \<sqinter> y) \<le> x = ({?l3..?u3} \<subseteq> {l1..u1})"
    using joindef by (simp add: xdef)
  then show "(x \<sqinter> y) \<le> x"
    by (simp add: leq)
qed

lemma inf_le2:
  fixes x y :: stamp
  shows "(x \<sqinter> y) \<le> y"
proof -
  fix x :: stamp
  fix y :: stamp
  obtain l1 u1 where xdef: "x = intstamp l1 u1"
    using stamp.exhaust by auto
  obtain l2 u2 where ydef: "y = intstamp l2 u2"
    using stamp.exhaust by auto
  have joindef: "x \<sqinter> y = intstamp (max l1 l2) (min u1 u2)"
    (is "?join = intstamp ?l3 ?u3")
    by (simp add: ydef xdef)
  have leq: "{?l3..?u3} \<subseteq> {l2..u2}"
    by simp
  have "(x \<sqinter> y) \<le> y = ({?l3..?u3} \<subseteq> {l2..u2})"
    using joindef by (simp add: ydef)
  then show "(x \<sqinter> y) \<le> y"
    by (simp add: leq)
qed

lemma inf_greatest:
  fixes x y z :: stamp
  shows "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> (y \<sqinter> z)"
proof -
  fix x y z :: stamp
  assume xlessy: "x \<le> y"
  assume xlessz: "x \<le> z"
  obtain l1 u1 where xdef: "x = intstamp l1 u1"
    using stamp.exhaust by auto
  obtain l2 u2 where ydef: "y = intstamp l2 u2"
    using stamp.exhaust by auto
  obtain l3 u3 where zdef: "z = intstamp l3 u3"
    using stamp.exhaust by auto
  obtain l4 u4 where yzdef: "y \<sqinter> z = intstamp l4 u4"
    by (meson inf_stamp.elims)
  have max4: "l4 = max l2 l3"
    using yzdef by (simp add: zdef ydef)
  have min4: "u4 = min u2 u3"
    using yzdef by (simp add: zdef ydef)
  have "{l1..u1} \<subseteq> {l2..u2}"
    using xlessy by (simp add: ydef xdef)
  have "{l1..u1} \<subseteq> {l3..u3}"
    using xlessz by (simp add: zdef xdef)
  have leq: "{l1..u1} \<subseteq> {l4..u4}"
    using \<open>{l1..u1} \<subseteq> {l2..u2}\<close> \<open>{l1..u1} \<subseteq> {l3..u3}\<close> by (simp add: min4 max4)
  have "x \<le> (y \<sqinter> z) = ({l1..u1} \<subseteq> {l4..u4})"
    by (simp add: xdef yzdef)
  then show "x \<le> (y \<sqinter> z)"
    using leq by simp
qed

instance
  apply standard
  by (simp add: inf_greatest inf_le2 inf_le1)+
end


subsubsection \<open>Stamp Meet\<close>
text \<open>
Defines the @{emph \<open>meet\<close>} operation for stamps.

For any two stamps, the @{emph \<open>meet\<close>} is defined as the union
of the valid values for the stamp.
\<close>
instantiation stamp :: semilattice_sup
begin

notation sup (infix "\<squnion>" 65)

fun sup_stamp :: "stamp \<Rightarrow> stamp \<Rightarrow> stamp" where
  "sup_stamp (intstamp l1 u1) (intstamp l2 u2) = intstamp (min l1 l2) (max u1 u2)"

lemma sup_ge1: 
  fixes x y :: stamp
  shows "x \<le> x \<squnion> y"
proof -
  fix x :: stamp
  fix y :: stamp
  obtain l1 u1 where xdef: "x = intstamp l1 u1"
    using stamp.exhaust by auto
  obtain l2 u2 where ydef: "y = intstamp l2 u2"
    using stamp.exhaust by auto
  have joindef: "x \<squnion> y = intstamp (min l1 l2) (max u1 u2)"
    (is "?join = intstamp ?l3 ?u3")
    by (simp add: ydef xdef)
  have leq: "{l1..u1} \<subseteq> {?l3..?u3}"
    by simp
  have "x \<le> x \<squnion> y = ({l1..u1} \<subseteq> {?l3..?u3})"
    using joindef by (simp add: xdef)
  then show "x \<le> x \<squnion> y"
    by (simp add: leq)
qed

lemma sup_ge2:
  fixes x y :: stamp
  shows "y \<le> x \<squnion> y"
proof -
  fix x :: stamp
  fix y :: stamp
  obtain l1 u1 where xdef: "x = intstamp l1 u1"
    using stamp.exhaust by auto
  obtain l2 u2 where ydef: "y = intstamp l2 u2"
    using stamp.exhaust by auto
  have joindef: "x \<squnion> y = intstamp (min l1 l2) (max u1 u2)"
    (is "?join = intstamp ?l3 ?u3")
    by (simp add: ydef xdef)
  have leq: "{l2..u2} \<subseteq> {?l3..?u3}" (is "?subset_thesis")
    by simp
  have "?thesis = (?subset_thesis)"
    by (metis StampLattice.sup_ge1 max.commute min.commute sup_stamp.elims less_eq_stamp.simps 
        sup_stamp.simps)
  then show "?thesis"
    by simp
qed

lemma sup_least:
  fixes x y z :: stamp
  shows "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> ((y \<squnion> z) \<le> x)"
proof -
  fix x y z :: stamp
  assume xlessy: "y \<le> x"
  assume xlessz: "z \<le> x"
  obtain l1 u1 where xdef: "x = intstamp l1 u1"
    using stamp.exhaust by auto
  obtain l2 u2 where ydef: "y = intstamp l2 u2"
    using stamp.exhaust by auto
  obtain l3 u3 where zdef: "z = intstamp l3 u3"
    using stamp.exhaust by auto
  have yzdef: "y \<squnion> z = intstamp (min l2 l3) (max u2 u3)"
    (is "?meet = intstamp ?l4 ?u4")
    by (simp add: ydef zdef)
  have s1: "{l2..u2} \<subseteq> {l1..u1}"
    using xlessy by (simp add: ydef xdef)
  have s2: "{l3..u3} \<subseteq> {l1..u1}"
    using xlessz by (simp add: zdef xdef)
  have leq: "{?l4..?u4} \<subseteq> {l1..u1}" (is ?subset_thesis)
    (* why is this such a hard proof? *)
    by (metis (no_types, opaque_lifting) inf.orderE inf_stamp.simps max.bounded_iff max.cobounded2 
        min.bounded_iff min.cobounded2 stamp.inject xdef xlessy ydef zdef atLeastatMost_subset_iff 
        xlessz)
  have "(y \<squnion> z \<le> x) = ?subset_thesis"
    by (simp add: xdef yzdef)
  then show "(y \<squnion> z \<le> x)"
    using leq by simp
qed

instance
  apply standard
  by (simp add: sup_least sup_ge2 sup_ge1)+
end


subsubsection \<open>Stamp Bounds\<close>
text \<open>
Defines the top and bottom elements of the stamp lattice.

This poses an interesting question as our stamp type is a
union of the various @{emph \<open>Stamp\<close>} subclasses, e.g.
@{emph \<open>IntegerStamp\<close>}, @{emph \<open>ObjectStamp\<close>}, etc.

Each subclass should preferably have its own unique
top and bottom element, i.e. An @{emph \<open>IntegerStamp\<close>}
would have the top element of the full range of integers
allowed by the bit width and a bottom of a range with no integers.
While the @{emph \<open>ObjectStamp\<close>} should have @{emph \<open>Object\<close>}
as the top and @{emph \<open>Void\<close>} as the bottom element.
\<close>
instantiation stamp :: bounded_lattice
begin

notation bot ("\<bottom>" 50)
notation top ("\<top>" 50)

definition width_min :: "nat \<Rightarrow> int64" where
  "width_min bits = -(2^(bits-1))"

definition width_max :: "nat \<Rightarrow> int64" where
  "width_max bits = (2^(bits-1)) - 1"

value "(sint (width_min 64), sint (width_max 64))"
value "max_word::int64"

lemma
  assumes "x = width_min 64"
  assumes "y = width_max 64"
  shows "sint x < sint y"
  by (simp add: assms width_max_def width_min_def)

text \<open>
Note that this definition is valid for unsigned integers only.

The bottom and top element for signed integers would be
(- 9223372036854775808, 9223372036854775807).

For unsigned we have
(0, 18446744073709551615).

For Java we are likely to be more concerned with signed integers.
To use the appropriate bottom and top for signed integers we
would need to change our definition of less\_eq from
{l1..u1} <= {l2..u2}
to
{sint l1..sint u1} <= {sint l2..sint u2}

We may still find an unsigned integer stamp useful.
I plan to investigate the Java code to see if this is useful
and then apply the changes to switch to signed integers.
\<close>
definition "bot_stamp = intstamp (-1) 0"
definition "top_stamp = intstamp 0 (-1)"

lemma bot_least:
  fixes a :: stamp
  shows "(\<bottom>) \<le> a"
proof -
  obtain min max where bot_def:"\<bottom> = intstamp max min"
    by (simp add: bot_stamp_def)
  have "min < max"
    using bot_def word_gt_0 unfolding bot_stamp_def by fastforce
  then have "{max..min} = {}"
    by (simp add: bot_def)
  then show ?thesis
    using less_eq_stamp.simps by (simp add: stamp.induct bot_stamp_def)
qed

lemma top_greatest:
  fixes a :: stamp
  shows "a \<le> (\<top>)"
proof -
  obtain min max where top_def:"\<top> = intstamp min max"
    by (simp add: top_stamp_def)
  have max_is_max: "\<not>(\<exists> n. n > max)"
    by (metis stamp.inject top_def top_stamp_def word_order.extremum_strict)
  have min_is_min: "\<not>(\<exists> n. n < min)"
    by (metis not_less_iff_gr_or_eq stamp.inject top_def top_stamp_def word_coorder.not_eq_extremum)
  have "\<not>(\<exists> l u. {min..max} < {l..u})"
    by (metis atLeastatMost_psubset_iff not_less min_is_min max_is_max)
  then show ?thesis
    unfolding top_stamp_def using less_eq_stamp.elims(3) by fastforce
qed

instance
  apply standard
  by (simp add: top_greatest bot_least)+
end


subsection \<open>Java Stamp Methods\<close>
text \<open>
The following are methods from the Java Stamp class,
they are the methods primarily used for optimizations.
\<close>
definition is_unrestricted :: "stamp \<Rightarrow> bool" where
  "is_unrestricted s = (\<top> = s)"

fun is_empty :: "stamp \<Rightarrow> bool" where
  "is_empty s = (\<bottom> = s)"

fun as_constant :: "stamp \<Rightarrow> Value option" where
  "as_constant (intstamp l u) = (if (card {l..u}) = 1
    then Some (IntVal 64 (SOME x. x \<in> {l..u}))
    else None)"

definition always_distinct :: "stamp \<Rightarrow> stamp \<Rightarrow> bool" where
  "always_distinct stamp1 stamp2 = (\<bottom> = (stamp1 \<sqinter> stamp2))"

definition never_distinct :: "stamp \<Rightarrow> stamp \<Rightarrow> bool" where
  "never_distinct stamp1 stamp2 = 
    (as_constant stamp1 = as_constant stamp2 \<and> as_constant stamp1 \<noteq> None)"

subsection \<open>Mapping to Values\<close>
fun valid_value :: "stamp => Value => bool" where
  "valid_value (intstamp l u) (IntVal b v) = (v \<in> {l..u})" |
  "valid_value (intstamp l u) _ = False"

text \<open>
The @{const valid_value} function is used to map a stamp instance
to the values that are allowed by the stamp.

It would be nice if there was a slightly more integrated way
to perform this mapping as it requires some infrastructure
to prove some fairly simple properties.
\<close>
lemma bottom_range_empty:
  "\<not>(valid_value (\<bottom>) v)"
  unfolding bot_stamp_def using valid_value.elims(2) by fastforce

lemma join_values:
  assumes "joined = x_stamp \<sqinter> y_stamp"
  shows "valid_value joined x \<longleftrightarrow> (valid_value x_stamp x \<and> valid_value y_stamp x)"
proof (cases x)
  case UndefVal
  then show ?thesis
    using valid_value.elims(2) by auto
(* WAS:
next
  case (IntVal32 x2)
  then show ?thesis
    using valid_value.elims(2) by blast
*)
next
  case (IntVal b x3)
  obtain lx ux where xdef: "x_stamp = intstamp lx ux"
    using stamp.exhaust by auto
  obtain ly uy where ydef: "y_stamp = intstamp ly uy"
    using stamp.exhaust by auto
  obtain v where "x = IntVal b v"
    by (simp add: IntVal)
  have "joined = intstamp (max lx ly) (min ux uy)"
    (is "joined = intstamp ?lj ?uj")
    by (simp add: xdef ydef assms)
  then have "valid_value joined (IntVal b v) = (v \<in> {?lj..?uj})"
    by simp
  then show ?thesis
    using \<open>x = IntVal b v\<close> by (auto simp add: ydef xdef)
next
  case (ObjRef x5)
  then show ?thesis
    using valid_value.elims(2) by auto
next
  case (ObjStr x6)
  then show ?thesis
    using valid_value.elims(2) by auto
next
  case (ArrayVal x51 x52)
  then show ?thesis
    using valid_value.elims(2) by blast
qed

lemma disjoint_empty:
  fixes x_stamp y_stamp :: stamp
  assumes "\<bottom> = x_stamp \<sqinter> y_stamp"
  shows "\<not>(valid_value x_stamp x \<and> valid_value y_stamp x)"
  using bottom_range_empty by (simp add: join_values assms)

experiment begin
text \<open>A possible equivalent alternative to the definition of less\_eq\<close>
fun less_eq_alt :: "'a::ord \<times> 'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool" where
  "less_eq_alt (l1, u1) (l2, u2) = ((\<not> l1 \<le> u1) \<or> l2 \<le> l1 \<and> u1 \<le> u2)"

text \<open>Proof equivalence\<close>
lemma 
  fixes l1 l2 u1 u2 :: int
  assumes "l1 \<le> u1 \<and> l2 \<le> u2"
  shows "{l1..u1} \<subseteq> {l2..u2} = ((l1 \<ge> l2) \<and> (u1 \<le> u2))"
  by (simp add: assms)

lemma 
  fixes l1 l2 u1 u2 :: int
  shows "{l1..u1} \<subseteq> {l2..u2} = less_eq_alt (l1, u1) (l2, u2)"
  by simp
end

subsection \<open>Generic Integer Stamp\<close>

text \<open>
Experimental definition of integer stamps generically,
restricting the datatype to only allow valid ranges and
the bottom integer element (max\_int..min\_int).
\<close>

lemma 
  assumes "(x::int) > 0"
  shows "(2 ^ x)/2 = (2 ^ (x - 1))"
  sorry

definition max_signed_int :: "'a::len word" where
  "max_signed_int = (2 ^ (LENGTH('a) - 1)) - 1"

definition min_signed_int :: "'a::len word" where
  "min_signed_int = -(2 ^ (LENGTH('a) - 1))"

definition int_bottom :: "'a::len word \<times> 'a word" where
  "int_bottom = (max_signed_int, min_signed_int)"

definition int_top :: "'a::len word \<times> 'a word" where
  "int_top = (min_signed_int, max_signed_int)"

(*
definition signed_gt_eq :: "'a::len word \<Rightarrow> 'a word \<Rightarrow> bool" where
  "signed_gt_eq a b = (sint a \<ge> sint a)"

definition signed_gt :: "'a::len word \<Rightarrow> 'a word \<Rightarrow> bool" where
  "signed_gt a b = (sint a > sint a)"

interpretation wor: ordering_top \<open>signed_gt_eq\<close> \<open>signed_gt\<close> \<open>max_signed_int :: 'a::len word\<close>
  apply (standard) sledgehammer
*)

lemma
  fixes x :: "'a::len word"
  shows "sint x \<le> sint (((2 ^ (LENGTH('a) - 1)) - 1)::'a word)"
  using sint_greater_eq sorry (*
  by (smt (z3) Euclidean_Division.pos_mod_bound int_word_sint sint_0 sint_lt two_less_eq_exp_length word_of_int_2p_len)
  *)

(* helpful: sint_greater_eq *)
value "sint (0::1 word)"
value "sint (1::1 word)"
value "sint (((2 ^ 0) - 1)::1 word)"

value "sint (((2 ^ 31) - 1)::32 word)"

lemma max_signed:
  fixes a :: "'a::len word"
  shows "sint a \<le> sint (max_signed_int::'a word)"
proof (cases "sint a = sint (max_signed_int::'a word)")
  case True
  then show ?thesis 
    by simp
next
  case False
  have "sint a < sint (max_signed_int::'a word)"
    using False unfolding max_signed_int_def sorry
  then show ?thesis 
    by simp
qed

lemma min_signed:
  fixes a :: "'a::len word"
  shows "sint a \<ge> sint (min_signed_int::'a word)"
  sorry

value "max_signed_int :: 32 word"
value "int_bottom::(32 word \<times> 32 word)"
value "sint (2147483647::32 word)"
value "sint (2147483648::32 word)"

typedef (overloaded) ('a::len) intstamp = 
  "{bounds :: ('a word, 'a word) prod . ((fst bounds) \<le>s (snd bounds) \<or> bounds = int_bottom)}"
proof -
  show ?thesis
    by blast
qed

setup_lifting type_definition_intstamp

lift_definition lower :: "('a::len) intstamp \<Rightarrow> 'a word"
  is "prod.fst \<circ> Rep_intstamp" .

lift_definition upper :: "('a::len) intstamp \<Rightarrow> 'a word"
  is "prod.snd \<circ> Rep_intstamp" .

lift_definition lower_int :: "('a::len) intstamp \<Rightarrow> int"
  is "sint \<circ> prod.fst" .

lift_definition upper_int :: "('a::len) intstamp \<Rightarrow> int"
  is "sint \<circ> prod.snd" .

lift_definition range :: "('a::len) intstamp \<Rightarrow> int set"
  is "\<lambda> (l, u). {sint l..sint u}" .

lift_definition bounds :: "('a::len) intstamp \<Rightarrow> ('a word \<times> 'a word)"
  is Rep_intstamp .

lift_definition is_bottom :: "('a::len) intstamp \<Rightarrow> bool"
  is "\<lambda> x. x = int_bottom" .

lift_definition from_bounds :: "('a::len word \<times> 'a word) \<Rightarrow> 'a intstamp"
  is "Abs_intstamp" .

instantiation intstamp :: (len) order
begin

definition less_eq_intstamp :: "'a intstamp \<Rightarrow> 'a intstamp \<Rightarrow> bool" where
  "less_eq_intstamp s1 s2 = (range s1 \<subseteq> range s2)"

definition less_intstamp :: "'a intstamp \<Rightarrow> 'a intstamp \<Rightarrow> bool" where
  "less_intstamp s1 s2 = (range s1 \<subset> range s2)"

value "int_bottom::(1 word \<times> 1 word)"
value "sint (0::1 word)"
value "sint (1::1 word)"

value "int_bottom::(2 word \<times> 2 word)"
value "sint (1::2 word)"
value "sint (2::2 word)"
value "sint ((2 ^ (LENGTH(32) - 1) - 1)::32 word) > sint ((- (2 ^ (LENGTH(32) - 1)))::32 word)"

lemma bottom_is_bottom:
  assumes "is_bottom s"
  shows "s \<le> a"
proof -
  have boundsdef: "bounds s = int_bottom"
    by (metis assms bounds.transfer is_bottom.rep_eq)
  obtain min max where "bounds s = (max, min)"
    by fastforce
  then have "max \<noteq> min"
    by (metis boundsdef dual_order.eq_iff fst_conv int_bottom_def less_minus_one_simps(1) max_signed 
        min_signed not_less sint_0 sint_n1 snd_conv)
  then have "sint min < sint max"
    by (metis \<open>bounds s = (max, min)\<close> boundsdef max_signed boundsdef int_bottom_def signed_word_eqI
        order.not_eq_order_implies_strict prod.sel(1))
  then have "range s = {}"
    by (simp add: \<open>bounds s = (max, min)\<close> bounds.transfer range_def)
  then show ?thesis
    by (simp add: StampLattice.less_eq_intstamp_def)
qed

lemma bounds_has_value:
  fixes x y :: int
  assumes "x < y"
  shows "card {x..y} > 0"
  using assms by simp

lemma bounds_has_no_value:
  fixes x y :: int
  assumes "x < y"
  shows "card {y..x} = 0"
  by (simp add: assms)

lemma bottom_unique: 
  fixes a s :: "'a intstamp"
  assumes "is_bottom s"
  shows "a \<le> s \<longleftrightarrow> is_bottom a"
proof -
  have "\<forall>x. sint (fst (bounds x)) \<le> sint (snd (bounds x)) \<or> is_bottom x"
    using Rep_intstamp by (auto simp add: word_sle_eq is_bottom_def bounds_def)
  then have "\<forall>x. (card (range x)) > 0 \<or> is_bottom x"
    by (simp add: bounds.transfer case_prod_beta range_def)
  obtain min max where boundsdef: "bounds s = (max, min)"
    by fastforce
  have nooverlap: "sint min < sint max"
    by (metis assms bounds.transfer boundsdef fst_conv int_bottom_def is_bottom.rep_eq min_signed 
        order.not_eq_order_implies_strict signed_word_eqI sint_0 snd_conv verit_la_disequality 
        zero_neq_one max_signed)
  have "range s = {sint max..sint min}"
    by (simp add: bounds.transfer boundsdef range.rep_eq)
  then have "card (range s) = 0"
    by (simp add: nooverlap)
  then have "\<forall>x. (card (range x)) > 0 \<longrightarrow> s < x"
    by (auto simp add: less_intstamp_def \<open>StampLattice.range s = {sint max..sint min}\<close>)
  then show ?thesis
    by (meson \<open>\<forall>x. 0 < card (StampLattice.range x) \<or> is_bottom x\<close> bottom_is_bottom less_intstamp_def
        less_eq_intstamp_def leD)
qed

lemma bottom_antisym:
  assumes "is_bottom x"
  shows "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  using assms proof (cases "is_bottom y")
case True
  then show ?thesis
    by (metis Rep_intstamp_inverse assms is_bottom.rep_eq)
next
  case False
  assume "y \<le> x"
  have "\<not>(y \<le> x)"
    by (simp add: assms False bottom_unique)
  then show ?thesis
    by (simp add: \<open>y \<le> x\<close>)
qed

lemma int_antisym:
  fixes x y :: "'a intstamp"
  shows "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
proof -
  fix x :: "'a intstamp"
  fix y :: "'a intstamp"
  assume xlessy: "x \<le> y"
  assume ylessx: "y \<le> x"
  obtain l1 u1 where xdef: "bounds x = (l1, u1)"
    by fastforce
  obtain l2 u2 where ydef: "bounds y = (l2, u2)"
    by fastforce
  from xlessy have s1: "{sint l1..sint u1} \<subseteq> {sint l2..sint u2}" (is "?xlessy")
    using xdef ydef less_eq_intstamp_def by (simp add: range_def bounds_def)
  from ylessx have s2: "{sint l2..sint u2} \<subseteq> {sint l1..sint u1}" (is "?ylessx")
    using xdef ydef less_eq_intstamp_def by (simp add: range_def bounds_def)
  show "x = y" proof (cases "is_bottom x")
    case True
    then show ?thesis 
      by (simp add: ylessx xlessy bottom_antisym)
  next
    case False
    then show ?thesis
      sorry
  qed
qed

instance
  apply standard
  using less_eq_intstamp_def less_intstamp_def apply (simp; blast)
  by (simp add: int_antisym less_eq_intstamp_def)+
end

value "take_bit LENGTH(63) 20::int"
value "take_bit LENGTH(63) ((-20)::int)"
value "bit (20::int64) (63::nat)"
value "bit ((-20)::int64) (63::nat)"

value "((-20)::int64) < (20::int64)"

value "take_bit LENGTH(63) ((-20)::int)"

lift_definition smax :: "'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is "\<lambda> a b. (if (sint a) \<le> (sint b) then b else a)" .

lift_definition smin :: "'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word"
  is "\<lambda> a b. (if (sint a) \<le> (sint b) then a else b)" .

instantiation intstamp :: (len) semilattice_inf
begin

notation inf (infix "\<sqinter>" 65)

definition join_bounds :: "'a intstamp \<Rightarrow> 'a intstamp \<Rightarrow> ('a word \<times> 'a word)" where
  "join_bounds s1 s2 = (smax (lower s1) (lower s2), smin (upper s1) (upper s2))"

definition join_or_bottom :: "'a intstamp \<Rightarrow> 'a intstamp \<Rightarrow> ('a word \<times> 'a word)" where
  "join_or_bottom s1 s2 = (let bound = (join_bounds s1 s2) in 
    if sint (fst bound) \<ge> sint (snd bound) then int_bottom else bound)"

definition inf_intstamp :: "'a intstamp \<Rightarrow> 'a intstamp \<Rightarrow> 'a intstamp" where
  "inf_intstamp s1 s2 = from_bounds (join_or_bottom s1 s2)"

lemma always_valid:
  fixes s1 s2 :: "'a intstamp"
  shows "Rep_intstamp (from_bounds (join_or_bottom s1 s2)) = join_or_bottom s1 s2"
  by (smt (z3) join_or_bottom_def from_bounds.transfer from_bounds_def mem_Collect_eq word_sle_eq 
      Abs_intstamp_inverse)

lemma invalid_join:
  fixes s1 s2 :: "'a intstamp"
  assumes "bound = join_bounds s1 s2"
  assumes "sint (fst bound) \<ge> sint (snd bound)"
  shows "from_bounds int_bottom = s1 \<sqinter> s2"
  using assms by (simp add: join_or_bottom_def inf_intstamp_def)

lemma unfold_bounds:
  "bounds x = (lower x, upper x)"
  by (simp add: bounds.transfer lower.rep_eq upper.rep_eq)

lemma int_inf_le1: 
  fixes x y :: "'a intstamp"
  shows "(x \<sqinter> y) \<le> x"
proof (cases "is_bottom (x \<sqinter> y)")
  case True
  then show ?thesis
    by (simp add: bottom_is_bottom)
next
  case False
  then show ?thesis
  using False proof -
  obtain l1 u1 where xdef: "lower x = l1 \<and> upper x = u1"
    by simp
  obtain l2 u2 where ydef: "lower y = l2 \<and> upper y = u2"
    by simp
  have joindef: "x \<sqinter> y = from_bounds ((smax l1 l2, smin u1 u2))"
    (is "x \<sqinter> y = from_bounds (?l3, ?u3)")
    by (smt (z3) StampLattice.inf_intstamp_def StampLattice.join_bounds_def always_valid False
        is_bottom.rep_eq join_or_bottom_def xdef ydef)
  have leq: "{sint ?l3..sint ?u3} \<subseteq> {sint l1..sint u1}"
    by (smt (z3) atLeastatMost_subset_iff smax.transfer smin.transfer)
  have "(x \<sqinter> y) \<le> x = ({sint ?l3..sint ?u3} \<subseteq> {sint l1..sint u1})"
    by (smt (z3) xdef less_eq_intstamp_def StampLattice.always_valid unfold_bounds ydef range.rep_eq
        StampLattice.join_or_bottom_def bounds.abs_eq case_prod_conv inf_intstamp_def False
        is_bottom.rep_eq join_bounds_def)
  then show "(x \<sqinter> y) \<le> x"
    using leq by simp
qed
qed

lemma int_inf_le2: 
  fixes x y :: "'a intstamp"
  shows "(x \<sqinter> y) \<le> y"
proof (cases "is_bottom (x \<sqinter> y)")
  case True
  then show ?thesis
    by (simp add: bottom_is_bottom)
next
  case False
  then show ?thesis
  using False proof -
  obtain l1 u1 where xdef: "lower x = l1 \<and> upper x = u1"
    by simp
  obtain l2 u2 where ydef: "lower y = l2 \<and> upper y = u2"
    by simp
  have joindef: "x \<sqinter> y = from_bounds ((smax l1 l2, smin u1 u2))"
    (is "x \<sqinter> y = from_bounds (?l3, ?u3)")
    by (smt (z3) False StampLattice.inf_intstamp_def StampLattice.join_bounds_def always_valid ydef
        is_bottom.rep_eq join_or_bottom_def xdef)
  have leq: "{sint ?l3..sint ?u3} \<subseteq> {sint l1..sint u1}"
    by (smt (z3) atLeastatMost_subset_iff smax.transfer smin.transfer)
  have "(x \<sqinter> y) \<le> y = ({sint ?l3..sint ?u3} \<subseteq> {sint l2..sint u2})"
    by (smt (z3) less_eq_intstamp_def False StampLattice.always_valid unfold_bounds range.rep_eq
        StampLattice.join_or_bottom_def bounds.abs_eq case_prod_conv inf_intstamp_def xdef ydef
        is_bottom.rep_eq join_bounds_def)
  then show "(x \<sqinter> y) \<le> y"
    by (smt (z3) atLeastatMost_subset_iff smax.transfer smin.transfer)
qed
qed

lemma
  assumes "x \<le> y"
  assumes "is_bottom y"
  shows "is_bottom x"
  using assms by (auto simp add: bottom_unique bottom_is_bottom)

lemma int_inf_greatest:
  fixes x y :: "'a intstamp"
  shows "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<sqinter> z"
  sorry

instance
  apply standard
  by (simp add: local.int_inf_greatest local.int_inf_le2 local.int_inf_le1)+

end

instantiation intstamp :: (len) semilattice_sup
begin

notation sup (infix "\<squnion>" 65)

instance apply standard sorry

end

instantiation intstamp :: (len) bounded_lattice
begin

notation bot ("\<bottom>" 50)
notation top ("\<top>" 50)

definition "bot_intstamp = int_bottom"
definition "top_intstamp = int_top"

instance apply standard sorry

end

value "sint (0::1 word)"
value "sint (1::1 word)"

datatype Stamp =
  BottomStamp |
  TopStamp |
  VoidStamp |
  (*Int1Stamp "1 uintstamp" |*)
  Int8Stamp "8 intstamp" |
  Int16Stamp "16 intstamp" |
  Int32Stamp "32 intstamp" |
  Int64Stamp "64 intstamp"

instantiation Stamp :: order
begin

fun less_eq_Stamp :: "Stamp \<Rightarrow> Stamp \<Rightarrow> bool" where
  "less_eq_Stamp BottomStamp _ = True" |
  "less_eq_Stamp _ TopStamp = True" |
  "less_eq_Stamp VoidStamp VoidStamp = True" |
  "less_eq_Stamp (Int8Stamp v1) (Int8Stamp v2) = (v1 \<le> v2)" |
  "less_eq_Stamp (Int16Stamp v1) (Int16Stamp v2) = (v1 \<le> v2)" |
  "less_eq_Stamp (Int32Stamp v1) (Int32Stamp v2) = (v1 \<le> v2)" |
  "less_eq_Stamp (Int64Stamp v1) (Int64Stamp v2) = (v1 \<le> v2)" |
  "less_eq_Stamp _ _ = False"

fun less_Stamp :: "Stamp \<Rightarrow> Stamp \<Rightarrow> bool" where
  "less_Stamp BottomStamp BottomStamp = False" |
  "less_Stamp BottomStamp _ = True" |
  "less_Stamp TopStamp TopStamp = False" |
  "less_Stamp _ TopStamp = True" |
  "less_Stamp VoidStamp VoidStamp = False" |
  "less_Stamp (Int8Stamp v1) (Int8Stamp v2) = (v1 < v2)" |
  "less_Stamp (Int16Stamp v1) (Int16Stamp v2) = (v1 < v2)" |
  "less_Stamp (Int32Stamp v1) (Int32Stamp v2) = (v1 < v2)" |
  "less_Stamp (Int64Stamp v1) (Int64Stamp v2) = (v1 < v2)" |
  "less_Stamp _ _ = False"

instance
  apply standard sorry
end

instantiation Stamp :: semilattice_inf
begin

notation inf (infix "\<sqinter>" 65)

fun inf_Stamp :: "Stamp \<Rightarrow> Stamp \<Rightarrow> Stamp" where
  "inf_Stamp BottomStamp _ = BottomStamp" |
  "inf_Stamp _ BottomStamp = BottomStamp" |
  "inf_Stamp TopStamp _ = TopStamp" |
  "inf_Stamp _ TopStamp = TopStamp" |
  "inf_Stamp VoidStamp VoidStamp = VoidStamp" |
  "inf_Stamp (Int8Stamp v1) (Int8Stamp v2) = Int8Stamp (v1 \<sqinter> v2)" |
  "inf_Stamp (Int16Stamp v1) (Int16Stamp v2) = Int16Stamp (v1 \<sqinter> v2)" |
  "inf_Stamp (Int32Stamp v1) (Int32Stamp v2) = Int32Stamp (v1 \<sqinter> v2)" |
  "inf_Stamp (Int64Stamp v1) (Int64Stamp v2) = Int64Stamp (v1 \<sqinter> v2)"

instance
  apply standard sorry
end

instantiation Stamp :: semilattice_sup
begin

notation sup (infix "\<squnion>" 65)

fun sup_Stamp :: "Stamp \<Rightarrow> Stamp \<Rightarrow> Stamp" where
  "sup_Stamp BottomStamp _ = BottomStamp" |
  "sup_Stamp _ BottomStamp = BottomStamp" |
  "sup_Stamp TopStamp _ = TopStamp" |
  "sup_Stamp _ TopStamp = TopStamp" |
  "sup_Stamp VoidStamp VoidStamp = VoidStamp" |
  "sup_Stamp (Int8Stamp v1) (Int8Stamp v2) = Int8Stamp (v1 \<squnion> v2)" |
  "sup_Stamp (Int16Stamp v1) (Int16Stamp v2) = Int16Stamp (v1 \<squnion> v2)" |
  "sup_Stamp (Int32Stamp v1) (Int32Stamp v2) = Int32Stamp (v1 \<squnion> v2)" |
  "sup_Stamp (Int64Stamp v1) (Int64Stamp v2) = Int64Stamp (v1 \<squnion> v2)"

instance
  apply standard sorry
end

instantiation Stamp :: bounded_lattice
begin

notation bot ("\<bottom>" 50)
notation top ("\<top>" 50)

definition top_Stamp :: "Stamp" where
  "top_Stamp = TopStamp"
definition bot_Stamp :: "Stamp" where
  "bot_Stamp = BottomStamp"

instance
  apply standard apply (simp add: bot_Stamp_def)
  by (smt (verit, del_insts) less_eq_Stamp.simps(13) less_eq_Stamp.simps(2) sup.coboundedI1
      sup_Stamp.simps(2))

end

lemma [code]: "Rep_intstamp (from_bounds (l, u)) = (l, u)"
  using Abs_intstamp_inverse from_bounds.rep_eq
  sorry

code_datatype Abs_intstamp
(*
value "Int32Stamp (from_bounds (2::32 word, 5::32 word)) \<sqinter> Int32Stamp (from_bounds (2::32 word, 5::32 word))"
*)
end