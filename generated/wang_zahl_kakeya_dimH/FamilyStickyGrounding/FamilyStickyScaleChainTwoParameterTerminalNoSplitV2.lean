import FamilyStickyGrounding.FamilyStickyScaleChainTwoParameterRecoveredEndpointV2
import FamilyStickyGrounding.FamilyStickyScaleChainSelectedIdentityAutomaticAllLargeProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainTwoParameterTerminalNoSplitV2

open Submission.Kakeya.Uniformity
open FamilyStickyDeltaMaxFiniteChainV2
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainTerminalFiniteSearchV1
open FamilyStickyScaleChainConstantBearingStoppingEndpointV1
open FamilyStickyScaleChainReservedExponentProfileV1
open FamilyStickyScaleChainActualStoppingUpstreamClosureV1
open FamilyStickyScaleChainDividingFiniteNodeProducerV1
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1
open FamilyStickyScaleChainFirstNonLargeAdjacentCardBudgetProducerV1
open FamilyStickyScaleChainTwoExponentStoppingCoreV2
open FamilyStickyScaleChainTwoParameterRecoveredEndpointV2
open FamilyStickyScaleChainSelectedIdentityAutomaticAllLargeProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyCapturedTubeBoxWidthV1

noncomputable section

/-!
# Paper-shaped terminal no-split endpoint

The stopping construction in the source paper terminates with the literal
statement that there is no buffered scale whose actual coarse `Delta_max` is
strictly below the next threshold.  Negating that strict split already gives
the middle lower bound with constant one.  Consequently this route needs
neither a rooted localization tree nor relevant-node certificates nor the
small-delta absorption used by the finite-node fallback.

The only numerical inputs left at the selected interval are the exact global
product comparison and the adjacent comparison.  A later theorem derives the
adjacent comparison from finite cardinality, leaving the paper's global
product invariant and terminal no-split invariant as the two honest residuals.
-/

variable {delta : NNReal} {gapEpsilon targetExponent : Real}
  {depth chainDepth N : Nat} {profile : Nat -> Real}
  {S : FiniteScaleSequence delta depth}

/-- The literal terminal alternative at one selected interval. -/
def SelectedActualTerminalNoSplit
    (A : ActualIntervalCovers S) (gapEpsilon : Real)
    (profile : Nat -> Real) (stage : Nat) (m : Fin depth) : Prop :=
  Not (exists rho, S.IsBuffered gapEpsilon m rho /\
    A.coarseValueAt m rho < splitThreshold S profile stage m rho)

/-- Exact selected numerical comparisons and the paper's terminal no-split
alternative directly produce the corrected two-exponent witness. -/
theorem exists_twoExponentWitnessAtNonLargeStep_of_numericalBudgets_and_terminalNoSplit
    (A : ActualIntervalCovers S)
    (B : BufferedChainFamily depth chainDepth)
    (stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N)
    (room : TargetExponentRoom profile stage targetExponent)
    (m : Fin depth) (not_large : Not (S.IsLarge gapEpsilon m))
    (budgets : SelectedNumericalBudgets B A profile stage m)
    (terminalNoSplit : SelectedActualTerminalNoSplit
      A gapEpsilon profile stage m) :
    Nonempty (TwoExponentKatzTaoDividingWitness delta N gapEpsilon
      targetExponent profile) := by
  refine ⟨{
    tau := S.tau m
    theta := S.theta m
    stage := stage
    stage_pos := stage_pos
    stage_le := stage_le
    targetRoom := room
    delta_le_tau := S.delta_le_tau m
    tau_le_theta := S.tau_le_theta m
    theta_le_one := S.theta_le_one m
    long := le_of_not_ge not_large
    globalValue := (B.finiteChain m).deltaMax 0
    adjacentValue := A.adjacentCoarseValue m
    middleValue := A.coarseValueAt m
    global_upper := ?_
    adjacent_upper := ?_
    middle_lower := ?_ }⟩
  · exact FiniteDeltaMaxChain.global_le_exponent_of_productBudget
      (B.finiteChain m) (S.theta m) (profile (stage - 1))
      (FamilyStickyScaleChainFiniteDeltaMaxBridgeV1.MultiscaleTubeHierarchy.BufferedTestBodyChain.productBudget_of_local_endpoint_le
        (B.datum m) (requiredGlobalPowerAt S profile stage m)
        (by
          simpa [actualGlobalProductAt, actualGlobalEndpointRatioAt] using
            budgets.1))
  · simpa [requiredAdjacentPowerAt] using budgets.2
  · intro rho lower upper
    exact le_of_not_gt fun strict =>
      terminalNoSplit ⟨rho, ⟨lower, upper⟩, by
        simpa [splitThreshold] using strict⟩

#print axioms exists_twoExponentWitnessAtNonLargeStep_of_numericalBudgets_and_terminalNoSplit


/-! ## Recovered profile without localization loss -/

variable {eta : Nat -> Real}
  {iota : Type*} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

theorem selectedProfileV2_pred_eq_recoveredProfileV2_pred
    (eta : Nat -> Real) {stage : Nat} (stage_pos : 1 <= stage)
    (targetExponent : Real) :
    selectedProfileV2 eta stage targetExponent (stage - 1) =
      recoveredProfileV2 eta stage targetExponent (stage - 1) := by
  rw [selectedProfileV2_pred eta stage_pos targetExponent,
    recoveredProfileV2, recoveredReservedProfile_pred eta stage_pos]

/-- The reserve-and-absorb route and the literal no-split route use exactly
the same predecessor powers, so selected numerical budgets transport without
any inequality or small-delta loss. -/
theorem selectedNumericalBudgets_recovered_of_selected
    {m : Fin depth}
    (B : BufferedChainFamily depth chainDepth)
    (A : ActualIntervalCovers S)
    (stage : Nat) (stage_pos : 1 <= stage)
    (budgets : SelectedNumericalBudgets B A
      (selectedProfileV2 eta stage targetExponent) stage m) :
    SelectedNumericalBudgets B A
      (recoveredProfileV2 eta stage targetExponent) stage m := by
  unfold SelectedNumericalBudgets at budgets ⊢
  simpa [requiredGlobalPowerAt, requiredAdjacentPowerAt,
    selectedProfileV2_pred_eq_recoveredProfileV2_pred
      eta stage_pos targetExponent] using budgets


/-- Terminal no-split only reads the profile at the selected stage. Since
the recovered profile agrees there with eta, the paper stopping invariant is
independent of the later choice of targetExponent. -/
theorem selectedActualTerminalNoSplit_recoveredProfileV2_iff
    (A : ActualIntervalCovers S) (stage : Nat) (m : Fin depth) :
    SelectedActualTerminalNoSplit A gapEpsilon
        (recoveredProfileV2 eta stage targetExponent) stage m ↔
      SelectedActualTerminalNoSplit A gapEpsilon eta stage m := by
  simp [SelectedActualTerminalNoSplit, splitThreshold]

/-- At the computed first non-large interval, selected numerical budgets and
literal terminal no-split give the recovered V2 witness directly. Unlike the
finite-node fallback, this paper-shaped endpoint needs no rooted tree,
relevant-node lower bounds, localization constant, or recovery threshold. -/
theorem exists_twoExponentRecoveredLiteralWitnessV2_of_selectedNumericalBudgets_and_terminalNoSplit
    (C : CoherentStickyMultiscaleCover fine)
    (B : BufferedChainFamily depth chainDepth)
    (stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N)
    (strict_room : eta stage < targetExponent)
    (not_all_large : Not (S.AllStepsLarge gapEpsilon))
    (budgets : SelectedNumericalBudgets B
      (C.toActualIntervalCovers S)
      (selectedProfileV2 eta stage targetExponent) stage
      (firstNonLargeStep S gapEpsilon not_all_large))
    (terminalNoSplit : SelectedActualTerminalNoSplit
      (C.toActualIntervalCovers S) gapEpsilon
      (recoveredProfileV2 eta stage targetExponent) stage
      (firstNonLargeStep S gapEpsilon not_all_large)) :
    Nonempty (TwoExponentKatzTaoDividingWitness delta N gapEpsilon
      targetExponent (recoveredProfileV2 eta stage targetExponent)) := by
  have room : TargetExponentRoom
      (recoveredProfileV2 eta stage targetExponent) stage targetExponent := by
    constructor
    simpa using strict_room.le
  exact exists_twoExponentWitnessAtNonLargeStep_of_numericalBudgets_and_terminalNoSplit
    (C.toActualIntervalCovers S) B stage stage_pos stage_le room
    (firstNonLargeStep S gapEpsilon not_all_large)
    (firstNonLargeStep_not_large S gapEpsilon not_all_large)
    (selectedNumericalBudgets_recovered_of_selected B
      (C.toActualIntervalCovers S) stage stage_pos budgets)
    terminalNoSplit


/-- Minimal selected-interval paper interface: the exact global product
invariant and terminal no-split invariant suffice. Both are stated using eta,
so the recursive stopping construction is independent of targetExponent.
Finite cardinality supplies the adjacent comparison. -/
theorem exists_twoExponentRecoveredLiteralWitnessV2_of_globalProduct_and_terminalNoSplit
    (C : CoherentStickyMultiscaleCover fine)
    (B : BufferedChainFamily depth chainDepth)
    (stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta stage < targetExponent)
    (not_all_large : Not (S.AllStepsLarge gapEpsilon))
    (globalProduct : actualGlobalProductAt B
        (firstNonLargeStep S gapEpsilon not_all_large) <=
      requiredGlobalPowerAt S eta stage
        (firstNonLargeStep S gapEpsilon not_all_large))
    (terminalNoSplit : SelectedActualTerminalNoSplit
      (C.toActualIntervalCovers S) gapEpsilon eta stage
      (firstNonLargeStep S gapEpsilon not_all_large))
    (gap_pos : 0 < gapEpsilon)
    (delta_pos : 0 < delta)
    (delta_le : delta <= firstNonLargeAdjacentCardThreshold iota gapEpsilon
      (eta (stage - 1))) :
    Nonempty (TwoExponentKatzTaoDividingWitness delta N gapEpsilon
      targetExponent (recoveredProfileV2 eta stage targetExponent)) := by
  have profile_pred_pos :
      0 < recoveredProfileV2 eta stage targetExponent (stage - 1) := by
    rw [recoveredProfileV2, recoveredReservedProfile_pred eta stage_pos]
    have eta_zero_le_pred : eta 0 <= eta (stage - 1) :=
      eta_monotone (Nat.zero_le _)
    linarith
  have recoveredGlobalProduct : actualGlobalProductAt B
        (firstNonLargeStep S gapEpsilon not_all_large) <=
      requiredGlobalPowerAt S
        (recoveredProfileV2 eta stage targetExponent) stage
        (firstNonLargeStep S gapEpsilon not_all_large) := by
    simpa [requiredGlobalPowerAt, recoveredProfileV2,
      recoveredReservedProfile_pred eta stage_pos] using globalProduct
  have recoveredDeltaLe :
      delta <= firstNonLargeAdjacentCardThreshold iota gapEpsilon
        (recoveredProfileV2 eta stage targetExponent (stage - 1)) := by
    simpa [recoveredProfileV2,
      recoveredReservedProfile_pred eta stage_pos] using delta_le
  have recoveredTerminalNoSplit : SelectedActualTerminalNoSplit
      (C.toActualIntervalCovers S) gapEpsilon
      (recoveredProfileV2 eta stage targetExponent) stage
      (firstNonLargeStep S gapEpsilon not_all_large) :=
    (selectedActualTerminalNoSplit_recoveredProfileV2_iff
      (C.toActualIntervalCovers S) stage
      (firstNonLargeStep S gapEpsilon not_all_large)).2 terminalNoSplit
  have recoveredBudgets : SelectedNumericalBudgets B
      (C.toActualIntervalCovers S)
      (recoveredProfileV2 eta stage targetExponent) stage
      (firstNonLargeStep S gapEpsilon not_all_large) :=
    firstNonLarge_selectedNumericalBudgets_of_global_and_card
      C S B (recoveredProfileV2 eta stage targetExponent) stage
      not_all_large gap_pos profile_pred_pos delta_pos recoveredDeltaLe
      recoveredGlobalProduct
  have selectedBudgets : SelectedNumericalBudgets B
      (C.toActualIntervalCovers S)
      (selectedProfileV2 eta stage targetExponent) stage
      (firstNonLargeStep S gapEpsilon not_all_large) := by
    unfold SelectedNumericalBudgets at recoveredBudgets ⊢
    simpa [requiredGlobalPowerAt, requiredAdjacentPowerAt,
      selectedProfileV2_pred_eq_recoveredProfileV2_pred
        eta stage_pos targetExponent] using recoveredBudgets
  exact
    exists_twoExponentRecoveredLiteralWitnessV2_of_selectedNumericalBudgets_and_terminalNoSplit
      C B stage stage_pos stage_le strict_room not_all_large
      selectedBudgets recoveredTerminalNoSplit
/-! ## Identity-cover final outcome with the honest paper residuals -/


/-- The top-level identity outcome now states both non-large residuals using
eta itself, matching a stopping construction performed before targetExponent
is chosen. The relevant-node/localization route remains a finite fallback. -/
theorem identityTwoParameterFinalOutcomeV2_of_globalProduct_and_terminalNoSplit
    (fine : UniformTubeFamily delta iota)
    (T : FiniteScaleSequence delta depth)
    (hdepth : 0 < depth)
    (B : BufferedChainFamily depth chainDepth)
    (slot : Fin N)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta (oneBasedStage slot) < targetExponent)
    (gap_pos : 0 < gapEpsilon)
    (delta_pos : 0 < delta)
    (delta_le : delta <= firstNonLargeAdjacentCardThreshold iota gapEpsilon
      (eta (oneBasedStage slot - 1)))
    (globalProduct : forall hnot : Not (T.AllStepsLarge gapEpsilon),
      actualGlobalProductAt B
          (firstNonLargeStep T gapEpsilon hnot) <=
        requiredGlobalPowerAt T eta (oneBasedStage slot)
          (firstNonLargeStep T gapEpsilon hnot))
    (terminalNoSplit : forall hnot : Not (T.AllStepsLarge gapEpsilon),
      SelectedActualTerminalNoSplit
        ((identityRadiusCoherentCover fine).toActualIntervalCovers T)
        gapEpsilon eta (oneBasedStage slot)
        (firstNonLargeStep T gapEpsilon hnot)) :
    (T.AllStepsLarge gapEpsilon /\
        (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
          ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1)
          (((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) *
            (Fintype.card iota : ENNReal))) \/
      Nonempty (TwoExponentKatzTaoDividingWitness delta N gapEpsilon
        targetExponent
        (recoveredProfileV2 eta (oneBasedStage slot) targetExponent)) := by
  by_cases hall : T.AllStepsLarge gapEpsilon
  · exact Or.inl ⟨hall,
      identityIsStickyAtEveryScale_of_allStepsLarge
        fine T hdepth delta_pos hall⟩
  · exact Or.inr
      (exists_twoExponentRecoveredLiteralWitnessV2_of_globalProduct_and_terminalNoSplit
        (identityRadiusCoherentCover fine) B
        (oneBasedStage slot) (oneBasedStage_pos slot) (oneBasedStage_le slot)
        eta_monotone two_le_zero strict_room hall
        (globalProduct hall) (terminalNoSplit hall)
        gap_pos delta_pos delta_le)

#print axioms selectedNumericalBudgets_recovered_of_selected
#print axioms selectedActualTerminalNoSplit_recoveredProfileV2_iff
#print axioms exists_twoExponentRecoveredLiteralWitnessV2_of_selectedNumericalBudgets_and_terminalNoSplit
#print axioms exists_twoExponentRecoveredLiteralWitnessV2_of_globalProduct_and_terminalNoSplit
#print axioms identityTwoParameterFinalOutcomeV2_of_globalProduct_and_terminalNoSplit

end
end FamilyStickyScaleChainTwoParameterTerminalNoSplitV2
