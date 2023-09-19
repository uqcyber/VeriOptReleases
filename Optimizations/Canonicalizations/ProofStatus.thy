theory ProofStatus
  imports
    AbsPhase
    AddPhase
    AndPhase
    ConditionalPhase
    MulPhase
    NegatePhase
    NewAnd
    NotPhase
    OrPhase
    ShiftPhase
    SignedDivPhase
    SignedRemPhase
    SubPhase
    TacticSolving
    XorPhase
  keywords
    "gencode" :: thy_decl
begin

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
    val state = Toplevel.theory_toplevel thy;
    val ctxt = Toplevel.context_of state;
    val code = (Syntax.check_term ctxt (Syntax.parse_term ctxt term));
    val export = 
    ((Const ("ProofStatus.generate", @{typ "Rules \<Rightarrow> string"}))
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


gencode "Test" "choice [ZeroSubtractValue_code]"

print_phases

gencode "ConditionalCode" "( (optimized_export (
  choice [
  FlipX2_code,
  FlipX_code,
  NormalizeX2_code,
  NormalizeX_code,
  ConditionalEqualIsRHS_code,
  ConditionalEliminateKnownLess_code,
  ConditionBoundsY_code,
  ConditionBoundsX_code,
  ConditionalEqualBranches_code,
  DefaultFalseBranch_code,
  DefaultTrueBranch_code,
  NegateConditionFlipBranches_code])))"

print_phases

gencode "PaperNaive" "(optimized_export
  (choice [Identity, Evaluate, Shift, LeftConst]))"

gencode "PaperStategy" "(optimized_export
  (LeftConst \<then> (choice [Identity, Evaluate] else Shift)))"

gencode "PaperNoOpt" "(
  (choice [Identity, Evaluate, Shift, LeftConst]))"

gencode "AllOpts" "(
  (choice [
  EliminateRedundantFalse_code,
  DistributeSub_code,
  opt_add_left_negate_to_sub_code,
  SubNegativeValue_code,
  SubThenSubLeft_code,
  SubThenAddRight_code,
  SubThenAddLeft_code,
  SubAfterSubLeft_code,
  SubAfterAddLeft_code,
  SubAfterAddRight_code,
  OrNotOperands_code,
  EliminateRedundantFalse_code,
  OrEqual_code,
  NotCancel_code,
  RedundantRHSXOr_code,
  RedundantRHSYOr_code,
  RedundantLHSXOr_code,
  RedundantLHSYOr_code,
  DistributeSubtraction_code,
  NegateCancel_code,
  EliminateRedundantNegative_code,
  FlipX2_code,
  FlipX_code,
  NormalizeX2_code,
  NormalizeX_code,
  ConditionalEqualIsRHS_code,
  ConditionalEliminateKnownLess_code,
  ConditionBoundsY_code,
  ConditionBoundsX_code,
  ConditionalEqualBranches_code,
  DefaultFalseBranch_code,
  DefaultTrueBranch_code,
  NegateConditionFlipBranches_code,
  AndNots_code,
  AndShiftConstantRight_code,
  AndEqual_code,
  AddLeftNegateToSub_code,
  AddRightNegateToSub_code,
  RedundantAddSub_code,
  RedundantSubAdd2_code,
  RedundantSubAdd_code,
  AddNeutral_code,
  AddShiftConstantRight_code,
  AbsNegate_code,
  AbsIdempotence_code,
  AndRightFallThrough_code,
  AndLeftFallThrough_code
  ]))"

declare [[show_types=false]]
print_phases
print_phases!

print_methods

print_theorems

thm opt_add_left_negate_to_sub
thm_oracles AbsNegate

export_phases \<open>Full\<close>


value "export_rules (optimized_export (EliminateRedundantFalse_code else XorSelfIsFalse_code))"

(* -1 is very very slow for code generation *)
value "optimized_export (XorInverse2_code else XorInverse_code else OrInverse2_code else OrInverse_code)"

value "export_rules (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (
  SubNegativeValue_code else
  SubThenSubLeft_code else
  SubThenAddRight_code else
  SubThenAddLeft_code else
  SubAfterSubLeft_code else
  SubAfterAddLeft_code else
  SubAfterAddRight_code))))))))))))))))"

value "export_rules (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (
  choice [
  SubNegativeValue_code,
  SubThenSubLeft_code,
  SubThenAddRight_code,
  SubThenAddLeft_code,
  SubAfterSubLeft_code,
  SubAfterAddLeft_code,
  SubAfterAddRight_code]))))))))))))))))"

value " (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (
  choice [
  SubThenAddRight_code,
  SubThenAddLeft_code,
  SubAfterAddLeft_code,
  SubAfterAddRight_code]))))))))))))))))"

value " (optimized_export 
  (SubThenAddRight_code else
  SubThenAddLeft_code) else
  (SubAfterAddLeft_code else
  SubAfterAddRight_code))"

value "export_rules (optimized_export (
  OrRightFallthrough_code else
  OrLeftFallthrough_code else
  OrNotOperands_code else
  EliminateRedundantFalse_code else
  OrEqual_code))"

value "export_rules (optimized_export (
  NotCancel_code))"

value "export_rules (optimized_export (
  RedundantRHSXOr_code else
  RedundantRHSYOr_code else
  RedundantLHSXOr_code else
  RedundantLHSYOr_code))"

value "export_rules (optimized_export (
  DistributeSubtraction_code else
  NegateCancel_code))"

value "export_rules (optimized_export (
  EliminateRedundantNegative_code))"

value "export_rules (optimized_export (
  choice [
  ConditionalEqualIsRHS_code,
  ConditionalEliminateKnownLess_code,
  ConditionBoundsY_code,
  ConditionBoundsX_code,
  ConditionalEqualBranches_code,
  DefaultFalseBranch_code,
  DefaultTrueBranch_code,
  NegateConditionFlipBranches_code]))"

value "export_rules (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (
  FlipX2_code else
  FlipX_code else
  NormalizeX2_code else
  NormalizeX_code else
  ConditionalEqualIsRHS_code else
  ConditionalEliminateKnownLess_code else
  ConditionBoundsY_code else
  ConditionBoundsX_code else
  ConditionalEqualBranches_code else
  DefaultFalseBranch_code else
  DefaultTrueBranch_code else
  NegateConditionFlipBranches_code))))))))))))))))"


value "export_rules (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (
  ConditionalEqualIsRHS_code else
  ConditionalEqualBranches_code else
  DefaultFalseBranch_code else
  DefaultTrueBranch_code else
  NegateConditionFlipBranches_code))))))))))))))))"

value "export_rules (optimized_export (
  AndLeftFallThrough_code else
  AndRightFallThrough_code else
  AndNots_code else
  AndEqual_code))"

value "export_rules (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (optimized_export (
  AddLeftNegateToSub_code else
  AddRightNegateToSub_code else
  RedundantAddSub_code else
  RedundantSubAdd2_code else
  RedundantSubAdd_code else
  AddNeutral_code))))))))))))))))"

value "export_rules (optimized_export (
  AbsNegate_code else
  AbsIdempotence_code))"

end