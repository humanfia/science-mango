import FamilyStickyGrounding.FamilyStickyScaleChainRelevantNodeCutoffPhaseProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000

open Set
open scoped ENNReal NNReal

namespace FamilyStickyScaleChainFirstNonLargeVacuousRelevantNodeProducerV1

open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainRootedRefinementTreeV1
open FamilyStickyScaleChainReservedExponentProfileV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
open FamilyStickyScaleChainActualStrictLossWithConstantV1
open FamilyStickyScaleChainActualSmallDeltaRecoveredEndpointV1
open FamilyStickyScaleChainActualStoppingUpstreamClosureV1
open FamilyStickyScaleChainDividingFiniteNodeProducerV1
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1
open FamilyStickyScaleChainFirstNonLargeRelevantNodeProducerV1
open FamilyStickyScaleChainRelevantNodeCutoffPhaseProducerV1

noncomputable section

/-!
# Vacuous relevant-node certificate at the actual first non-large step

The recovered small-delta threshold is strictly below one because the actual
localization constant is at least one and the absorbed exponent is positive.
At the first non-large interval, `delta < 1` and longness force
`tau < theta`.  Meanwhile the recovered exponent room gives `1 < epsilon`,
so the upper buffered cutoff lies strictly below `tau`.  Since every rooted
tree node lies at or above `tau`, there are no relevant nodes at all.

Thus the relevant-node lower-bound certificate is automatic and vacuous in
the actual recovered endpoint.  No contained-mass selection, active-family
nonemptiness, John data, WZ data, or hierarchy coordinate is required.
-/

/-! ## The actual recovered threshold is strictly below one -/

theorem actualStrictLossRecoveredSmallDeltaThreshold_lt_one
    {eta : Nat -> Real} {stage : Nat} {epsilon : Real}
    (iota : Type*) [Fintype iota]
    (epsilon_pos : 0 < epsilon)
    (strict_room : eta stage < epsilon) :
    actualStrictLossRecoveredSmallDeltaThreshold
      eta stage epsilon iota < 1 := by
  let K := actualStrictLocalizationConstant iota
  have K_ne_top : K ≠ ∞ := actualStrictLocalizationConstant_ne_top iota
  have one_le_K : (1 : ENNReal) <= K :=
    one_le_actualStrictLocalizationConstant iota
  have one_le_toNNReal : (1 : NNReal) <= K.toNNReal := by
    rw [<- ENNReal.coe_le_coe, ENNReal.coe_toNNReal K_ne_top]
    exact one_le_K
  have base_gt_one : (1 : NNReal) < K.toNNReal + 1 := by
    linarith
  have loss_pos : 0 < halfReservedExponentRoom eta stage epsilon :=
    halfReservedExponentRoom_pos strict_room
  have exponent_pos :
      0 < epsilon ^ 2 * halfReservedExponentRoom eta stage epsilon := by
    positivity
  have power_neg :
      -(1 / (epsilon ^ 2 *
        halfReservedExponentRoom eta stage epsilon)) < 0 := by
    have inverse_pos : 0 < 1 / (epsilon ^ 2 *
        halfReservedExponentRoom eta stage epsilon) :=
      one_div_pos.mpr exponent_pos
    linarith
  change (K.toNNReal + 1) ^
      (-(1 / (epsilon ^ 2 *
        halfReservedExponentRoom eta stage epsilon))) < 1
  exact NNReal.rpow_lt_one_of_one_lt_of_neg base_gt_one power_neg

/-! ## Longness plus strict smallness makes the first interval strict -/

variable {delta : NNReal} {outerDepth chainDepth N : Nat}
  {epsilon : Real} {eta : Nat -> Real}
  {S : FiniteScaleSequence delta outerDepth}

theorem firstNonLarge_tau_lt_theta_of_delta_lt_one
    (S : FiniteScaleSequence delta outerDepth)
    (not_all_large : Not (S.AllStepsLarge epsilon))
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (epsilon_pos : 0 < epsilon) :
    S.tau (firstNonLargeStep S epsilon not_all_large) <
      S.theta (firstNonLargeStep S epsilon not_all_large) := by
  let m := firstNonLargeStep S epsilon not_all_large
  have long : S.IsLong epsilon m := by
    simpa [m] using firstNonLargeStep_isLong S epsilon not_all_large
  have delta_lt_one_E : (delta : ENNReal) < 1 := by
    exact_mod_cast delta_lt_one
  have delta_power_lt_one : (delta : ENNReal) ^ epsilon < 1 :=
    ENNReal.rpow_lt_one delta_lt_one_E epsilon_pos
  have theta_pos : 0 < S.theta m :=
    (delta_pos.trans_le (S.delta_le_tau m)).trans_le
      (S.tau_le_theta m)
  have scaled_lt_theta :
      (delta : ENNReal) ^ epsilon * (S.theta m : ENNReal) <
        (S.theta m : ENNReal) := by
    simpa using ENNReal.mul_lt_mul_left
      (ENNReal.coe_ne_zero.mpr theta_pos.ne') ENNReal.coe_ne_top
        delta_power_lt_one
  change (S.tau m : ENNReal) <=
      (delta : ENNReal) ^ epsilon * (S.theta m : ENNReal) at long
  have tau_lt_theta_E :
      (S.tau m : ENNReal) < (S.theta m : ENNReal) :=
    long.trans_lt scaled_lt_theta
  exact_mod_cast tau_lt_theta_E

/-! ## The actual relevant-node certificate has no nodes to check -/

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

theorem firstNonLarge_verifiedRelevantStepNodeLowerBounds_vacuous
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (slot : Fin N)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta (oneBasedStage slot) < epsilon)
    (not_all_large : Not (S.AllStepsLarge epsilon))
    (delta_pos : 0 < delta)
    (delta_le : delta <=
      actualStrictLossRecoveredSmallDeltaThreshold
        eta (oneBasedStage slot) epsilon iota) :
    VerifiedRelevantStepNodeLowerBounds
      (epsilon := epsilon)
      (profile := reserveTailLoss eta (oneBasedStage slot)
        (halfReservedExponentRoom eta (oneBasedStage slot) epsilon))
      (stage := oneBasedStage slot)
      (C.toActualIntervalCovers S) R
        (firstNonLargeStep S epsilon not_all_large) where
  checked := by
    intro i relevant
    have eta_zero_le_stage : eta 0 <= eta (oneBasedStage slot) :=
      eta_monotone (Nat.zero_le _)
    have epsilon_pos : 0 < epsilon := by linarith
    have one_lt_epsilon : (1 : Real) < epsilon := by linarith
    have threshold_lt_one :=
      actualStrictLossRecoveredSmallDeltaThreshold_lt_one
        iota epsilon_pos strict_room
    have delta_lt_one : delta < 1 := delta_le.trans_lt threshold_lt_one
    have tau_lt_theta := firstNonLarge_tau_lt_theta_of_delta_lt_one
      S not_all_large delta_pos delta_lt_one epsilon_pos
    let m := firstNonLargeStep S epsilon not_all_large
    have upper_lt_tau := bufferedUpperCutoff_lt_tau_of_tau_lt_theta
      S m (R.tau_pos m) (by simpa [m] using tau_lt_theta)
        one_lt_epsilon
    have tau_le_scale :
        (S.tau m : ENNReal) <= (R.tree.scale m i : ENNReal) := by
      exact_mod_cast R.tau_le_scale m i
    have scale_lt_tau :
        (R.tree.scale m i : ENNReal) < (S.tau m : ENNReal) :=
      relevant.trans_lt upper_lt_tau
    exact False.elim ((not_lt_of_ge tau_le_scale) scale_lt_tau)

/-! ## Direct recovered endpoint without a node certificate input -/

theorem exists_recoveredLiteralWitness_of_selectedNumericalBudgets_without_nodes
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : BufferedChainFamily outerDepth chainDepth)
    (slot : Fin N)
    (eta_monotone : Monotone eta)
    (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta (oneBasedStage slot) < epsilon)
    (not_all_large : Not (S.AllStepsLarge epsilon))
    (budgets : SelectedNumericalBudgets B
      (C.toActualIntervalCovers S)
      (reserveTailLoss eta (oneBasedStage slot)
        (halfReservedExponentRoom eta (oneBasedStage slot) epsilon))
      (oneBasedStage slot)
      (firstNonLargeStep S epsilon not_all_large))
    (delta_pos : 0 < delta)
    (delta_le : delta <=
      actualStrictLossRecoveredSmallDeltaThreshold
        eta (oneBasedStage slot) epsilon iota) :
    Nonempty (KatzTaoDividingWitness delta N epsilon
      (recoveredReservedProfile eta (oneBasedStage slot)
        (halfReservedExponentRoom eta (oneBasedStage slot) epsilon))) := by
  exact exists_recoveredLiteralWitness_of_relevantSelectedNumericalBudgets
    C R B slot eta_monotone two_le_zero strict_room not_all_large budgets
      (firstNonLarge_verifiedRelevantStepNodeLowerBounds_vacuous
        C R slot eta_monotone two_le_zero strict_room not_all_large
          delta_pos delta_le)
      delta_pos delta_le

#print axioms actualStrictLossRecoveredSmallDeltaThreshold_lt_one
#print axioms firstNonLarge_tau_lt_theta_of_delta_lt_one
#print axioms firstNonLarge_verifiedRelevantStepNodeLowerBounds_vacuous
#print axioms exists_recoveredLiteralWitness_of_selectedNumericalBudgets_without_nodes

end
end FamilyStickyScaleChainFirstNonLargeVacuousRelevantNodeProducerV1
