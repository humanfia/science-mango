import FamilyStickyGrounding.FamilyStickyScaleChainTwoParameterLocalizationV2
import FamilyStickyGrounding.FamilyStickyScaleChainSelectedGlobalAdjacentRecoveredProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainTwoParameterRecoveredEndpointV2

open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainRootedRefinementTreeV1
open FamilyStickyScaleChainActualStrictLossWithConstantV1
open FamilyStickyScaleChainConstantBearingStoppingEndpointV1
open FamilyStickyScaleChainConstantExponentLossEndpointV1
open FamilyStickyScaleChainReservedExponentProfileV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
open FamilyStickyScaleChainActualSmallDeltaRecoveredEndpointV1
open FamilyStickyScaleChainDividingFiniteNodeProducerV1
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1
open FamilyStickyScaleChainFirstNonLargeRelevantNodeProducerV1
open FamilyStickyScaleChainFirstNonLargeAdjacentCardBudgetProducerV1
open FamilyStickyScaleChainSelectedGlobalExponentProducerV1
open FamilyStickyScaleChainTwoParameterLocalizationV2

noncomputable section

/-!
# Two-parameter recovered endpoint

The scale-gap exponent and the target profile exponent play different roles.
`gapEpsilon` controls `AllStepsLarge`, longness, and localization, while
`targetExponent` supplies room for the exponent loss used to absorb the
finite localization constant.  This module keeps those parameters separate
all the way through the recovered literal witness.

In particular, no comparison between `eta stage` and `gapEpsilon` is used.
The only room assumption is the honest target-profile inequality
`eta stage < targetExponent`.
-/

universe u

variable {delta : NNReal} {gapEpsilon targetExponent : Real}
  {outerDepth chainDepth N : Nat}
  {S : FiniteScaleSequence delta outerDepth}
  {eta : Nat -> Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-! ## Separated profiles and thresholds -/

/-- Spend half of the room below the independent target exponent. -/
def halfRoom
    (eta : Nat -> Real) (stage : Nat) (targetExponent : Real) : Real :=
  (targetExponent - eta stage) / 2

theorem halfRoom_pos
    {eta : Nat -> Real} {stage : Nat} {targetExponent : Real}
    (strict_room : eta stage < targetExponent) :
    0 < halfRoom eta stage targetExponent := by
  rw [halfRoom]
  linarith

theorem eta_add_halfRoom_le_targetExponent
    {eta : Nat -> Real} {stage : Nat} {targetExponent : Real}
    (strict_room : eta stage < targetExponent) :
    eta stage + halfRoom eta stage targetExponent <= targetExponent := by
  rw [halfRoom]
  linarith

/-- The profile used to construct the constant-bearing witness. -/
def selectedProfileV2
    (eta : Nat -> Real) (stage : Nat) (targetExponent : Real) :
    Nat -> Real :=
  reserveTailLoss eta stage (halfRoom eta stage targetExponent)

/-- The literal profile after the localization constant has been absorbed. -/
def recoveredProfileV2
    (eta : Nat -> Real) (stage : Nat) (targetExponent : Real) :
    Nat -> Real :=
  recoveredReservedProfile eta stage (halfRoom eta stage targetExponent)

@[simp]
theorem selectedProfileV2_at
    (eta : Nat -> Real) (stage : Nat) (targetExponent : Real) :
    selectedProfileV2 eta stage targetExponent stage =
      eta stage + halfRoom eta stage targetExponent := by
  simp [selectedProfileV2]

@[simp]
theorem selectedProfileV2_pred
    (eta : Nat -> Real) {stage : Nat} (stage_pos : 1 <= stage)
    (targetExponent : Real) :
    selectedProfileV2 eta stage targetExponent (stage - 1) =
      eta (stage - 1) := by
  simp [selectedProfileV2, stage_pos]

@[simp]
theorem recoveredProfileV2_at
    (eta : Nat -> Real) (stage : Nat) (targetExponent : Real) :
    recoveredProfileV2 eta stage targetExponent stage = eta stage := by
  simp [recoveredProfileV2]

theorem two_le_selectedProfileV2_at
    {eta : Nat -> Real} {stage : Nat} {targetExponent : Real}
    (two_le_eta_stage : (2 : Real) <= eta stage)
    (strict_room : eta stage < targetExponent) :
    (2 : Real) <= selectedProfileV2 eta stage targetExponent stage := by
  rw [selectedProfileV2_at]
  linarith [halfRoom_pos strict_room]

/-- Exact small-delta threshold which absorbs the actual strict-localization
constant using room below `targetExponent`, not below `gapEpsilon`. -/
def actualRecoveredThresholdV2
    (eta : Nat -> Real) (stage : Nat) (gapEpsilon targetExponent : Real)
    (iota : Type*) [Fintype iota] : NNReal :=
  smallDeltaExponentLossThreshold
    (actualStrictLocalizationConstant iota) gapEpsilon
      (halfRoom eta stage targetExponent)

theorem actualRecoveredThresholdV2_pos
    (eta : Nat -> Real) (stage : Nat) (gapEpsilon targetExponent : Real)
    (iota : Type*) [Fintype iota] :
    0 < actualRecoveredThresholdV2
      eta stage gapEpsilon targetExponent iota := by
  exact smallDeltaExponentLossThreshold_pos
    (actualStrictLocalizationConstant iota) gapEpsilon
      (halfRoom eta stage targetExponent)

theorem actualRecoveredThresholdV2_le_one
    {eta : Nat -> Real} {stage : Nat} {gapEpsilon targetExponent : Real}
    (iota : Type*) [Fintype iota]
    (gap_pos : 0 < gapEpsilon)
    (strict_room : eta stage < targetExponent) :
    actualRecoveredThresholdV2 eta stage gapEpsilon targetExponent iota <= 1 := by
  exact smallDeltaExponentLossThreshold_le_one
    (actualStrictLocalizationConstant iota) gap_pos
      (halfRoom_pos strict_room)

/-- One threshold for the automatic adjacent-card budget and the independent
recovered-profile constant absorption. -/
def selectedGlobalAdjacentRecoveredThresholdV2
    (eta : Nat -> Real) (stage : Nat) (gapEpsilon targetExponent : Real)
    (iota : Type*) [Fintype iota] : NNReal :=
  min
    (firstNonLargeAdjacentCardThreshold iota gapEpsilon
      (selectedProfileV2 eta stage targetExponent (stage - 1)))
    (actualRecoveredThresholdV2
      eta stage gapEpsilon targetExponent iota)

theorem selectedGlobalAdjacentRecoveredThresholdV2_pos
    (eta : Nat -> Real) (stage : Nat) (gapEpsilon targetExponent : Real)
    (iota : Type*) [Fintype iota] :
    0 < selectedGlobalAdjacentRecoveredThresholdV2
      eta stage gapEpsilon targetExponent iota := by
  exact lt_min
    (firstNonLargeAdjacentCardThreshold_pos iota gapEpsilon
      (selectedProfileV2 eta stage targetExponent (stage - 1)))
    (actualRecoveredThresholdV2_pos
      eta stage gapEpsilon targetExponent iota)

theorem delta_le_adjacentThresholdV2_of_le_combined
    {stage : Nat}
    (delta_le : delta <= selectedGlobalAdjacentRecoveredThresholdV2
      eta stage gapEpsilon targetExponent iota) :
    delta <= firstNonLargeAdjacentCardThreshold iota gapEpsilon
      (selectedProfileV2 eta stage targetExponent (stage - 1)) :=
  delta_le.trans (min_le_left _ _)

theorem delta_le_actualRecoveredThresholdV2_of_le_combined
    {stage : Nat}
    (delta_le : delta <= selectedGlobalAdjacentRecoveredThresholdV2
      eta stage gapEpsilon targetExponent iota) :
    delta <= actualRecoveredThresholdV2
      eta stage gapEpsilon targetExponent iota :=
  delta_le.trans (min_le_right _ _)

/-! ## Recovered endpoint from selected numerical inputs -/

/-- A non-large gap step produces a V1 literal dividing witness with the
recovered target profile.  The hypothesis `2 <= eta stage` is the minimal
lower-exponent input required by the quadratic localization estimate; strict
room alone cannot imply it.  There is deliberately no hypothesis comparing
`eta stage` with `gapEpsilon`. -/
theorem exists_recoveredLiteralWitnessV2_of_selectedNumericalBudgets
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N)
    (two_le_eta_stage : (2 : Real) <= eta stage)
    (strict_room : eta stage < targetExponent)
    (not_all_large : Not (S.AllStepsLarge gapEpsilon))
    (budgets : SelectedNumericalBudgets B
      (C.toActualIntervalCovers S)
      (selectedProfileV2 eta stage targetExponent) stage
      (firstNonLargeStep S gapEpsilon not_all_large))
    (V : VerifiedRelevantStepNodeLowerBounds
      (epsilon := gapEpsilon)
      (profile := selectedProfileV2 eta stage targetExponent)
      (stage := stage) (C.toActualIntervalCovers S) R
      (firstNonLargeStep S gapEpsilon not_all_large))
    (gap_pos : 0 < gapEpsilon)
    (delta_pos : 0 < delta)
    (delta_le : delta <= actualRecoveredThresholdV2
      eta stage gapEpsilon targetExponent iota) :
    Nonempty (KatzTaoDividingWitness delta N gapEpsilon
      (recoveredProfileV2 eta stage targetExponent)) := by
  let W : KatzTaoConstantDividingWitness delta N gapEpsilon
      (reserveTailLoss eta stage (halfRoom eta stage targetExponent))
      (actualStrictLocalizationConstant iota) :=
    constantWitnessAtNonLargeStep_twoParameter
      C R B stage stage_pos stage_le gap_pos.le
      (firstNonLargeStep S gapEpsilon not_all_large)
      (firstNonLargeStep_not_large S gapEpsilon not_all_large)
      (by simpa [selectedProfileV2] using budgets)
      (by simpa [selectedProfileV2] using V)
      (by
        simpa [selectedProfileV2] using
          two_le_selectedProfileV2_at two_le_eta_stage strict_room)
      delta_pos
  have W_stage : W.stage = stage := by
    rfl
  have tau_pos : 0 < W.tau :=
    delta_pos.trans_le W.delta_le_tau
  have loss_budget : SmallDeltaExponentLossBudget delta gapEpsilon
      (actualStrictLocalizationConstant iota)
      (halfRoom eta stage targetExponent) :=
    smallDeltaExponentLossBudget_of_le_threshold
      (actualStrictLocalizationConstant_ne_top iota)
      gap_pos (halfRoom_pos strict_room) delta_pos delta_le
  have endpoint :=
    exists_literalWitness_for_recoveredReservedProfile
      W W_stage delta_pos tau_pos loss_budget
  simpa [recoveredProfileV2] using endpoint

/-! ## Fully automatic adjacent budget from selected global estimates -/

theorem selectedProfileV2_pred_pos_of_stoppingData
    {eta : Nat -> Real} {stage : Nat} (stage_pos : 1 <= stage)
    {targetExponent : Real}
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0) :
    0 < selectedProfileV2 eta stage targetExponent (stage - 1) := by
  rw [selectedProfileV2_pred eta stage_pos targetExponent]
  have eta_zero_le_pred : eta 0 <= eta (stage - 1) :=
    eta_monotone (Nat.zero_le _)
  linarith

/-- Pointwise selected global estimates plus the common small-delta bound
automatically supply the adjacent budget, then invoke the two-parameter
recovered endpoint above. -/
theorem exists_recoveredLiteralWitnessV2_of_selectedGlobalEstimates
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (stage : Nat) (stage_pos : 1 <= stage) (stage_le : stage <= N)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta stage < targetExponent)
    (not_all_large : Not (S.AllStepsLarge gapEpsilon))
    (globalEstimates : SelectedGlobalExponentEstimates B S
      (selectedProfileV2 eta stage targetExponent) stage
      (firstNonLargeStep S gapEpsilon not_all_large))
    (V : VerifiedRelevantStepNodeLowerBounds
      (epsilon := gapEpsilon)
      (profile := selectedProfileV2 eta stage targetExponent)
      (stage := stage) (C.toActualIntervalCovers S) R
      (firstNonLargeStep S gapEpsilon not_all_large))
    (gap_pos : 0 < gapEpsilon)
    (delta_pos : 0 < delta)
    (delta_le : delta <= selectedGlobalAdjacentRecoveredThresholdV2
      eta stage gapEpsilon targetExponent iota) :
    Nonempty (KatzTaoDividingWitness delta N gapEpsilon
      (recoveredProfileV2 eta stage targetExponent)) := by
  have two_le_eta_stage : (2 : Real) <= eta stage :=
    two_le_zero.trans (eta_monotone (Nat.zero_le stage))
  have profile_pred_pos :
      0 < selectedProfileV2 eta stage targetExponent (stage - 1) :=
    selectedProfileV2_pred_pos_of_stoppingData
      stage_pos eta_monotone two_le_zero
  have global_budget :
      actualGlobalProductAt B
          (firstNonLargeStep S gapEpsilon not_all_large) <=
        requiredGlobalPowerAt S
          (selectedProfileV2 eta stage targetExponent) stage
          (firstNonLargeStep S gapEpsilon not_all_large) :=
    firstNonLarge_actualGlobalProductAt_le_requiredGlobalPowerAt
      B not_all_large delta_pos globalEstimates
  have budgets : SelectedNumericalBudgets B
      (C.toActualIntervalCovers S)
      (selectedProfileV2 eta stage targetExponent) stage
      (firstNonLargeStep S gapEpsilon not_all_large) :=
    firstNonLarge_selectedNumericalBudgets_of_global_and_card
      C S B (selectedProfileV2 eta stage targetExponent) stage
      not_all_large gap_pos profile_pred_pos delta_pos
      (delta_le_adjacentThresholdV2_of_le_combined delta_le)
      global_budget
  exact exists_recoveredLiteralWitnessV2_of_selectedNumericalBudgets
    C R B stage stage_pos stage_le two_le_eta_stage strict_room
    not_all_large budgets V gap_pos delta_pos
    (delta_le_actualRecoveredThresholdV2_of_le_combined delta_le)

#print axioms actualRecoveredThresholdV2_le_one
#print axioms exists_recoveredLiteralWitnessV2_of_selectedNumericalBudgets
#print axioms exists_recoveredLiteralWitnessV2_of_selectedGlobalEstimates

end
end FamilyStickyScaleChainTwoParameterRecoveredEndpointV2
