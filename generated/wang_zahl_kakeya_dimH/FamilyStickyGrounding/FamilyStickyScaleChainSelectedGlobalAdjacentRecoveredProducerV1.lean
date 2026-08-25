import FamilyStickyGrounding.FamilyStickyScaleChainSelectedGlobalExponentProducerV1
import FamilyStickyGrounding.FamilyStickyScaleChainFirstNonLargeAdjacentCardBudgetProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000

open Set
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainSelectedGlobalAdjacentRecoveredProducerV1

open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainRootedRefinementTreeV1
open FamilyStickyScaleChainReservedExponentProfileV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
open FamilyStickyScaleChainActualSmallDeltaRecoveredEndpointV1
open FamilyStickyScaleChainActualStoppingUpstreamClosureV1
open FamilyStickyScaleChainDividingFiniteNodeProducerV1
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1
open FamilyStickyScaleChainFirstNonLargeRelevantNodeProducerV1
open FamilyStickyScaleChainTotalStoppingDiagnosticProducerV1
open FamilyStickyScaleChainFirstNonLargeAdjacentCardBudgetProducerV1
open FamilyStickyScaleChainSelectedGlobalExponentProducerV1

noncomputable section

/-!
# Selected global estimates plus automatic adjacent-card recovery

At the computed first non-large interval, the preceding modules leave two
quantitatively different jobs.  Pointwise global exponent estimates close the
literal buffered product comparison.  Finite cardinality and longness close
the adjacent comparison below an explicit small-delta threshold.

This module combines those jobs with the relevant-node endpoint.  The caller
supplies only one selected global exponent-estimate certificate and the
relevant-node lower bounds.  Positivity of `epsilon` and of the selected
predecessor exponent follows from the standard monotonicity, baseline, and
strict-room assumptions.  One `min` threshold pays both the adjacent-card
budget and the already existing constant-recovery budget.
-/

universe u

variable {delta : NNReal} {epsilon : Real}
  {outerDepth chainDepth N : Nat}
  {S : FiniteScaleSequence delta outerDepth}
  {eta : Nat -> Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-! ## Automatic positivity from the standard stopping data -/

/-- The strict room lies above a profile value which is at least the baseline
`eta 0 >= 2`, so the ambient stopping exponent is positive. -/
theorem epsilon_pos_of_stoppingData
    (slot : Fin N) (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta (oneBasedStage slot) < epsilon) :
    0 < epsilon := by
  have eta_zero_le_stage : eta 0 <= eta (oneBasedStage slot) :=
    eta_monotone (Nat.zero_le _)
  linarith

/-- At the predecessor of the one-based selected stage, tail reservation has
not started.  Monotonicity and `eta 0 >= 2` therefore make the selected
predecessor exponent strictly positive. -/
theorem diagnosticSelectedProfile_pred_pos_of_stoppingData
    (slot : Fin N) (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0) :
    0 < diagnosticSelectedProfile eta slot epsilon
      (oneBasedStage slot - 1) := by
  rw [diagnosticSelectedProfile,
    reserveTailLoss_pred eta (oneBasedStage_pos slot)]
  have eta_zero_le_pred : eta 0 <= eta (oneBasedStage slot - 1) :=
    eta_monotone (Nat.zero_le _)
  linarith

/-! ## One threshold for both numerical absorptions -/

/-- The exact common threshold: the left term pays the finite adjacent-family
cardinality, and the right term pays the strict-localization constant in the
recovered endpoint. -/
def selectedGlobalAdjacentRecoveredThreshold
    (eta : Nat -> Real) (slot : Fin N) (epsilon : Real)
    (iota : Type*) [Fintype iota] : NNReal :=
  min
    (firstNonLargeAdjacentCardThreshold iota epsilon
      (diagnosticSelectedProfile eta slot epsilon
        (oneBasedStage slot - 1)))
    (actualStrictLossRecoveredSmallDeltaThreshold eta
      (oneBasedStage slot) epsilon iota)

theorem selectedGlobalAdjacentRecoveredThreshold_pos
    (eta : Nat -> Real) (slot : Fin N) (epsilon : Real)
    (iota : Type*) [Fintype iota] :
    0 < selectedGlobalAdjacentRecoveredThreshold eta slot epsilon iota := by
  exact lt_min
    (firstNonLargeAdjacentCardThreshold_pos iota epsilon
      (diagnosticSelectedProfile eta slot epsilon
        (oneBasedStage slot - 1)))
    (actualStrictLossRecoveredSmallDeltaThreshold_pos eta
      (oneBasedStage slot) epsilon iota)

theorem delta_le_adjacentThreshold_of_le_combined
    (slot : Fin N)
    (delta_le : delta <=
      selectedGlobalAdjacentRecoveredThreshold eta slot epsilon iota) :
    delta <= firstNonLargeAdjacentCardThreshold iota epsilon
      (diagnosticSelectedProfile eta slot epsilon
        (oneBasedStage slot - 1)) :=
  delta_le.trans (min_le_left _ _)

theorem delta_le_recoveredThreshold_of_le_combined
    (slot : Fin N)
    (delta_le : delta <=
      selectedGlobalAdjacentRecoveredThreshold eta slot epsilon iota) :
    delta <= actualStrictLossRecoveredSmallDeltaThreshold eta
      (oneBasedStage slot) epsilon iota :=
  delta_le.trans (min_le_right _ _)

/-! ## End-to-end producer -/

/-- Selected pointwise global exponent estimates and relevant-node checks are
the only analytic inputs.  The adjacent numerical comparison and both needed
positivity facts are generated internally. -/
theorem exists_recoveredLiteralWitness_of_selectedGlobalEstimates_and_relevantNodes
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (slot : Fin N)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta (oneBasedStage slot) < epsilon)
    (not_all_large : Not (S.AllStepsLarge epsilon))
    (globalEstimates : SelectedGlobalExponentEstimates B S
      (diagnosticSelectedProfile eta slot epsilon)
      (oneBasedStage slot)
      (firstNonLargeStep S epsilon not_all_large))
    (V : VerifiedRelevantStepNodeLowerBounds
      (epsilon := epsilon)
      (profile := diagnosticSelectedProfile eta slot epsilon)
      (stage := oneBasedStage slot)
      (C.toActualIntervalCovers S) R
      (firstNonLargeStep S epsilon not_all_large))
    (delta_pos : 0 < delta)
    (delta_le : delta <=
      selectedGlobalAdjacentRecoveredThreshold eta slot epsilon iota) :
    Nonempty (KatzTaoDividingWitness delta N epsilon
      (diagnosticRecoveredProfile eta slot epsilon)) := by
  have epsilon_pos : 0 < epsilon :=
    epsilon_pos_of_stoppingData slot eta_monotone two_le_zero strict_room
  have profile_pred_pos :
      0 < diagnosticSelectedProfile eta slot epsilon
        (oneBasedStage slot - 1) :=
    diagnosticSelectedProfile_pred_pos_of_stoppingData
      slot eta_monotone two_le_zero
  have global_budget :
      actualGlobalProductAt B
          (firstNonLargeStep S epsilon not_all_large) <=
        requiredGlobalPowerAt S
          (diagnosticSelectedProfile eta slot epsilon)
          (oneBasedStage slot)
          (firstNonLargeStep S epsilon not_all_large) :=
    firstNonLarge_actualGlobalProductAt_le_requiredGlobalPowerAt
      B not_all_large delta_pos globalEstimates
  have budgets : SelectedNumericalBudgets B
      (C.toActualIntervalCovers S)
      (diagnosticSelectedProfile eta slot epsilon)
      (oneBasedStage slot)
      (firstNonLargeStep S epsilon not_all_large) :=
    firstNonLarge_selectedNumericalBudgets_of_global_and_card
      C S B (diagnosticSelectedProfile eta slot epsilon)
      (oneBasedStage slot) not_all_large epsilon_pos profile_pred_pos
      delta_pos
      (delta_le_adjacentThreshold_of_le_combined slot delta_le)
      global_budget
  have endpoint :=
    exists_recoveredLiteralWitness_of_relevantSelectedNumericalBudgets
      C R B slot eta_monotone two_le_zero strict_room not_all_large
      (by simpa [diagnosticSelectedProfile] using budgets)
      (by simpa [diagnosticSelectedProfile] using V)
      delta_pos
      (delta_le_recoveredThreshold_of_le_combined slot delta_le)
  simpa [diagnosticRecoveredProfile] using endpoint

/-! ## Source-shaped relevant mass variant -/

/-- The same producer with literal relevant-node mass selections in place of
the verified inequalities.  The proof argument indexing the selections is
the automatically derived nonnegativity of `epsilon`. -/
theorem exists_recoveredLiteralWitness_of_selectedGlobalEstimates_and_relevantMass
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (slot : Fin N)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta (oneBasedStage slot) < epsilon)
    (not_all_large : Not (S.AllStepsLarge epsilon))
    (globalEstimates : SelectedGlobalExponentEstimates B S
      (diagnosticSelectedProfile eta slot epsilon)
      (oneBasedStage slot)
      (firstNonLargeStep S epsilon not_all_large))
    (M : RelevantNodeMassSelections
      (epsilon := epsilon)
      (profile := diagnosticSelectedProfile eta slot epsilon)
      (stage := oneBasedStage slot)
      (C.toActualIntervalCovers S) R
      (epsilon_pos_of_stoppingData slot eta_monotone
        two_le_zero strict_room).le
      (firstNonLargeStep S epsilon not_all_large))
    (delta_pos : 0 < delta)
    (delta_le : delta <=
      selectedGlobalAdjacentRecoveredThreshold eta slot epsilon iota) :
    Nonempty (KatzTaoDividingWitness delta N epsilon
      (diagnosticRecoveredProfile eta slot epsilon)) := by
  exact
    exists_recoveredLiteralWitness_of_selectedGlobalEstimates_and_relevantNodes
      C R B slot eta_monotone two_le_zero strict_room not_all_large
      globalEstimates
      (M.toVerifiedRelevantStepNodeLowerBounds
        (epsilon_pos_of_stoppingData slot eta_monotone
          two_le_zero strict_room).le)
      delta_pos delta_le

/-! ## Numerical-failure-free two-branch diagnostic -/

/-- Once selected global exponent estimates and the common small-delta bound
are present, the numerical-failure branch disappears.  The remaining search
returns a recovered literal witness or the first relevant-node analytic
alternative. -/
noncomputable def recoveredLiteralWitnessOrFirstRelevantNodeAlternative_of_selectedGlobalEstimates
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (slot : Fin N)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta (oneBasedStage slot) < epsilon)
    (not_all_large : Not (S.AllStepsLarge epsilon))
    (globalEstimates : SelectedGlobalExponentEstimates B S
      (diagnosticSelectedProfile eta slot epsilon)
      (oneBasedStage slot)
      (firstNonLargeStep S epsilon not_all_large))
    (delta_pos : 0 < delta)
    (delta_le : delta <=
      selectedGlobalAdjacentRecoveredThreshold eta slot epsilon iota) :
    PLift (Nonempty (KatzTaoDividingWitness delta N epsilon
      (diagnosticRecoveredProfile eta slot epsilon))) ⊕
      FirstRelevantNodeAnalyticAlternative
        (epsilon := epsilon)
        (profile := diagnosticSelectedProfile eta slot epsilon)
        (stage := oneBasedStage slot)
        (C.toActualIntervalCovers S) R
        (firstNonLargeStep S epsilon not_all_large) := by
  let selected := relevantNodeSearch
    (epsilon := epsilon)
    (profile := diagnosticSelectedProfile eta slot epsilon)
    (stage := oneBasedStage slot)
    (C.toActualIntervalCovers S) R
    (firstNonLargeStep S epsilon not_all_large)
  cases selected with
  | inl verified =>
      exact Sum.inl ⟨
        exists_recoveredLiteralWitness_of_selectedGlobalEstimates_and_relevantNodes
          C R B slot eta_monotone two_le_zero strict_room not_all_large
          globalEstimates verified.down delta_pos delta_le⟩
  | inr failure =>
      exact Sum.inr failure.toAnalyticAlternative

#print axioms epsilon_pos_of_stoppingData
#print axioms diagnosticSelectedProfile_pred_pos_of_stoppingData
#print axioms selectedGlobalAdjacentRecoveredThreshold_pos
#print axioms delta_le_adjacentThreshold_of_le_combined
#print axioms delta_le_recoveredThreshold_of_le_combined
#print axioms exists_recoveredLiteralWitness_of_selectedGlobalEstimates_and_relevantNodes
#print axioms exists_recoveredLiteralWitness_of_selectedGlobalEstimates_and_relevantMass
#print axioms recoveredLiteralWitnessOrFirstRelevantNodeAlternative_of_selectedGlobalEstimates

end
end FamilyStickyScaleChainSelectedGlobalAdjacentRecoveredProducerV1
