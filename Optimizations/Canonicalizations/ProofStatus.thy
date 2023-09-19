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

print_phases

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

thm opt_add_left_negate_to_sub
thm_oracles AbsNegate

export_phases \<open>Full\<close>

end