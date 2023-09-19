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
begin

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