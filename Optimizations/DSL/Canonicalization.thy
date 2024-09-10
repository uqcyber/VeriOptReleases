subsection \<open>Canonicalization DSL\<close>

theory Canonicalization
  imports
    Markup
    Phase
    CodeGenAlt
    "HOL-Eisbach.Eisbach"
  keywords
    "phase" :: thy_decl and 
    "terminating" :: quasi_command and
    "print_phases" :: diag and
    "export_phases" :: thy_decl and
    "optimization" :: thy_goal_defn (*and
    "gencode" :: thy_decl*)
begin

print_methods

ML \<open>
datatype 'a Rewrite =
  Rule of 'a * 'a * term option

type rewrite = {
  name: binding,
  rewrite: term Rewrite,
  proofs: thm list,
  code: thm list,
  source: term
}

structure RewriteRule : Rule =
struct
type T = rewrite;

(*
fun pretty_rewrite ctxt (Transform (from, to)) = 
      Pretty.block [
        Syntax.pretty_term ctxt from,
        Pretty.str " \<mapsto> ",
        Syntax.pretty_term ctxt to
      ]
  | pretty_rewrite ctxt (Conditional (from, to, cond)) = 
      Pretty.block [
        Syntax.pretty_term ctxt from,
        Pretty.str " \<mapsto> ",
        Syntax.pretty_term ctxt to,
        Pretty.str " when ",
        Syntax.pretty_term ctxt cond
      ]
  | pretty_rewrite _ _ = Pretty.str "not implemented"*)

fun pretty_thm ctxt thm =
  (Proof_Context.pretty_fact ctxt ("", [thm]))

fun pretty ctxt obligations t =
  let
    val is_skipped = Thm_Deps.has_skip_proof (#proofs t);

    val warning = (if is_skipped 
      then [Pretty.str "(proof skipped)", Pretty.brk 0]
      else []);

    val obligations = (if obligations
      then [Pretty.big_list 
              "obligations:"
              (map (pretty_thm ctxt) (#proofs t)),
            Pretty.brk 0]
      else []);      

    fun pretty_bind binding =
      Pretty.markup 
        (Position.markup (Binding.pos_of binding) Markup.position)
        [Pretty.str (Binding.name_of binding)];

  in
  Pretty.block ([
    pretty_bind (#name t), Pretty.str ": ",
    Syntax.pretty_term ctxt (#source t), Pretty.fbrk
  ] @ obligations @ warning)
  end
end

structure RewritePhase = DSL_Phase(RewriteRule);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>phase\<close> "enter an optimization phase"
   (Parse.binding --| Parse.$$$ "terminating" -- Parse.const --| Parse.begin
     >> (Toplevel.begin_main_target true o RewritePhase.setup));

fun print_phases print_obligations ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun print phase = RewritePhase.pretty print_obligations phase ctxt
  in 
    map print (RewritePhase.phases thy)
  end

fun print_optimizations print_obligations thy =
  print_phases print_obligations thy |> Pretty.writeln_chunks

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_phases\<close>
    "print debug information for optimizations"
    (Parse.opt_bang >>
      (fn b => Toplevel.keep ((print_optimizations b) o Toplevel.context_of)));

fun export_phases thy name =
  let
    val state = Toplevel.make_state (SOME thy);
    val ctxt = Toplevel.context_of state;
    val content = Pretty.string_of (Pretty.chunks (print_phases false ctxt));
    val cleaned = YXML.content_of content;    


    val filename = Path.explode (name^".rules");
    val directory = Path.explode "optimizations";
    val path = Path.binding (
                Path.append directory filename,
                Position.none);
    val thy' = thy |> Generated_Files.add_files (path, (Bytes.string content));

    val _ = Export.export thy' path [YXML.parse cleaned];

    val _ = writeln (Export.message thy' (Path.basic "optimizations"));
  in
    thy'
  end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>export_phases\<close>
    "export information about encoded optimizations"
    (Parse.path >>
      (fn name => Toplevel.theory (fn state => export_phases state name)))
\<close>

ML_file "rewrites.ML"
             
subsubsection \<open>Semantic Preservation Obligation\<close>

fun rewrite_preservation :: "(IRExpr, IRExpr) Rewrite \<Rightarrow> bool" where
  "rewrite_preservation (Transform x y) = (y \<le> x)" |
  "rewrite_preservation (Conditional x y conds) = (\<exists>conds'. base_semantics conds conds' \<and> coerce_to_bool conds' True \<longrightarrow> (y \<le> x))"

subsubsection \<open>Termination Obligation\<close>

fun rewrite_termination :: "(IRExpr, IRExpr) Rewrite \<Rightarrow> (IRExpr \<Rightarrow> nat) \<Rightarrow> bool" where
  "rewrite_termination (Transform x y) trm = (trm x > trm y)" |
  "rewrite_termination (Conditional x y conds) trm = (\<forall>conds'. base_semantics conds conds' \<and> coerce_to_bool conds' True \<longrightarrow> (trm x > trm y))"

fun intval :: "(Value, Value) Rewrite \<Rightarrow> bool" where
  "intval (Transform x y) = (x \<noteq> UndefVal \<and> y \<noteq> UndefVal \<longrightarrow> x = y)" |
  "intval (Conditional x y conds) = (\<forall>conds'. base_semantics conds conds' \<and> coerce_to_bool conds' True \<longrightarrow> (x = y))"

subsubsection \<open>Standard Termination Measure\<close>

fun size :: "IRExpr \<Rightarrow> nat" where
  unary_size:
  "size (UnaryExpr op x) = (size x) + 2" |
  (*"size (BinaryExpr BinSub x y) = (size x) + (size y) + 3" |
  "size (BinaryExpr BinMul x y) = (size x) + (size y) + 3" |*)
  bin_const_size:
  "size (BinaryExpr op x (ConstantExpr cy)) = (size x) + 2" |
  bin_size:
  "size (BinaryExpr op x y) = (size x) + (size y) + 2" |
  cond_size:
  "size (ConditionalExpr c t f) = (size c) + (size t) + (size f) + 2" |
  const_size:
  "size (ConstantExpr c) = 1" |
  param_size:
  "size (ParameterExpr ind s) = 2" |
  leaf_size:
  "size (LeafExpr nid s) = 2" |
  "size (ConstantVar c) = 2" |
  "size (VariableExpr x s) = 2"

subsubsection \<open>Automated Tactics\<close>

named_theorems size_simps "size simplication rules"

method unfold_optimization =
  (unfold rewrite_preservation.simps, unfold rewrite_termination.simps,
    unfold intval.simps,
    rule conjE, simp, simp del: le_expr_def, force?)
  | (unfold rewrite_preservation.simps, unfold rewrite_termination.simps,
    rule conjE, simp, simp del: le_expr_def, force?)

method unfold_size =
  (((unfold size.simps, simp add: size_simps del: le_expr_def)?
  ; (simp add: size_simps del: le_expr_def)?
  ; (auto simp: size_simps)?
  ; (unfold size.simps)?)[1])
  

print_methods

ML \<open>
structure System : RewriteSystem =
struct
val preservation = @{const rewrite_preservation};
val termination = @{const rewrite_termination};
val intval = @{const intval};
end

structure DSL = DSL_Rewrites(System);

(*val long_keyword =
  Parse_Spec.includes >> K "" ||
  Parse_Spec.long_statement_keyword;

val long_statement =
  Scan.optional (Parse_Spec.thm_name ":" --| Scan.ahead long_keyword) Binding.empty_atts --
  Scan.optional Parse_Spec.includes [] -- Parse_Spec.long_statement
    >> (fn ((binding, includes), (elems, concl)) => (true, binding, includes, elems, concl));

val short_statement =
  Parse_Spec.statement -- Parse_Spec.if_statement -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) =>
      (false, Binding.empty_atts, [], [Element.Fixes fixes, Element.Assumes assumes],
        Element.Shows shows));
*)

fun rewrite_cmd ((thm_name, whens), thm) =
let
in
 DSL.rewrite_cmd ((thm_name, whens), thm)
end

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>optimization\<close>
    "define an optimization and open proof obligation"
    ((Parse_Spec.thm_name ":" -- (Scan.repeat (Parse.$$$ "when" -- Parse.term)) -- Parse.term)
        >> rewrite_cmd);
\<close>

subsection \<open>Code Generation\<close>

(*
definition generate :: "Rules \<Rightarrow> string" where
  "generate = (generate_statement 0) o export_rules"

ML \<open>
fun replaceSubstring (original: string, target: string, replacement: string): string =
    let
        val targetLength = String.size target
        val originalLength = String.size original

        fun replaceHelper (pos: int, acc: string): string =
            if pos + targetLength <= originalLength then
                let
                    val currentSubstr = String.substring (original, pos, targetLength)
                    val nextChar = String.substring (original, pos, 1)
                    val updatedAcc = if currentSubstr = target then acc ^ replacement else acc ^ nextChar
                    val jump = if currentSubstr = target then targetLength else 1
                in
                    replaceHelper (pos + jump, updatedAcc)
                end
            else
                acc ^ String.extract (original, pos, NONE)

    in
        replaceHelper (0, "")
    end

fun gencode thy name term =
  let
    val state = Toplevel.make_state (SOME thy);
    val ctxt = Toplevel.context_of state;
    val code = (Syntax.check_term ctxt (Syntax.parse_term ctxt term));
    val export = 
    ((Const ("Canonicalization.generate", @{typ "Rules \<Rightarrow> string"}))
      $ code);
    val value = Code_Evaluation.dynamic_value_strict ctxt export;
    val content = Pretty.string_of (Syntax.pretty_term ctxt value);
    val content = replaceSubstring (content, "\<newline>", "\n") (* Replace newlines *)
    val content = String.substring (content, 2, (String.size content) - 4) (* Strip quotes *)

    val cleaned = YXML.content_of content;


    val filename = Path.explode (name^".java");
    val directory = Path.explode "optimizations";
    val path = Path.binding (
                Path.append directory filename,
                Position.none);
    val thy' = thy |> Generated_Files.add_files (path, (Bytes.string content));

    val _ = Export.export thy' path [YXML.parse cleaned];

    val _ = writeln (Export.message thy' (Path.basic "optimizations"));
  in
    thy'
  end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>gencode\<close>
    "generate an optimized optimization code"
    (Parse.path -- Parse.term >>
      (fn (name, term) => Toplevel.theory (fn state => gencode state name term)))
\<close>
*)

end