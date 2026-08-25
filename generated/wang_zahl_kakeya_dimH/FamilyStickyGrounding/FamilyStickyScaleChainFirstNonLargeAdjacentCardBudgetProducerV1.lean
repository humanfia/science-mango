import FamilyStickyGrounding.FamilyStickyScaleChainTotalStoppingDiagnosticProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000

open Set
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainFirstNonLargeAdjacentCardBudgetProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open FamilyStickyAtEveryScaleCoreV1
open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyDeltaMaxFiniteChainV2
open FamilyStickyFiniteFamilyMaximalConcentrationV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainActualStrictLossWithConstantV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
open FamilyStickyScaleChainActualStoppingUpstreamClosureV1
open FamilyStickyScaleChainDividingFiniteNodeProducerV1
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1
open FamilyStickyScaleChainTotalStoppingDiagnosticProducerV1

noncomputable section

/-!
# Cardinal adjacent budget at the first non-large interval

The literal adjacent coarse family is finite.  Its maximal concentration is
therefore bounded by the cardinality of its active index set, which in turn
is bounded by the cardinality of the original fine family.  At the first
non-large interval, longness converts a sufficiently small `delta` into the
exact endpoint-ratio power required by `SelectedNumericalBudgets`.

This construction makes no cardinal-one or parent-collapse assumption.  It
automates only the adjacent half of the selected numerical budget; the
global product comparison remains a separate, quantitatively exact input.
-/

universe u

variable {delta : NNReal} {epsilon : Real}
  {outerDepth chainDepth N : Nat}
  {S : FiniteScaleSequence delta outerDepth}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-! ## Finite cardinality of the literal adjacent coarse family -/

/-- A coarse `Delta_max` is bounded by the cardinality of the active coarse
index set.  Repeated tubes are retained because the subtype is the actual
finite index type of `activeCoarseFamily`. -/
theorem StickyScaleCover.coarseDeltaMax_le_activeCoarse_card
    {rho : NNReal} {index : Type*} [Fintype index] [DecidableEq index]
    {F : UniformTubeFamily delta index}
    (Q : StickyScaleCover F rho) :
    StickyScaleCover.coarseDeltaMax Q <=
      (Q.activeCoarse.card : ENNReal) := by
  unfold StickyScaleCover.coarseDeltaMax
  calc
    maximalConcentration Q.activeCoarseFamily <=
        (Fintype.card {k // k ∈ Q.activeCoarse} : ENNReal) :=
      maximalConcentration_le_card Q.activeCoarseFamily
    _ = (Q.activeCoarse.card : ENNReal) := by
      rw [Fintype.card_coe]

/-- Every literal interval coarse maximum of a coherent cover is bounded by
the cardinality of the original fine index type. -/
theorem interval_coarseDeltaMax_le_original_card
    (C : CoherentStickyMultiscaleCover fine)
    {sigma rho : NNReal}
    (hdeltaSigma : delta <= sigma)
    (hSigmaRho : sigma <= rho)
    (hRhoOne : rho <= 1) :
    StickyScaleCover.coarseDeltaMax
        (C.intervalScaleCover sigma rho
          hdeltaSigma hSigmaRho hRhoOne) <=
      (Fintype.card iota : ENNReal) := by
  let U := C.base.cover rho
    (hdeltaSigma.trans hSigmaRho) hRhoOne
  let I := C.intervalScaleCover sigma rho
    hdeltaSigma hSigmaRho hRhoOne
  calc
    StickyScaleCover.coarseDeltaMax I <=
        (I.activeCoarse.card : ENNReal) :=
      StickyScaleCover.coarseDeltaMax_le_activeCoarse_card I
    _ = (U.activeCoarse.card : ENNReal) := by rfl
    _ <= (U.activeFine.card : ENNReal) := by
      exact_mod_cast StickyScaleCover.activeCoarse_card_le_activeFine_card U
    _ <= (Fintype.card iota : ENNReal) := by
      exact_mod_cast Finset.card_le_univ U.activeFine

/-- The actual adjacent value generated from a coherent cover inherits the
uniform original-cardinality bound at every interval. -/
theorem actualAdjacentCoarseValue_le_original_card
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta outerDepth)
    (m : Fin outerDepth) :
    (C.toActualIntervalCovers S).adjacentCoarseValue m <=
      (Fintype.card iota : ENNReal) := by
  rw [C.toActualIntervalCovers_adjacentCoarseValue_eq S m]
  exact interval_coarseDeltaMax_le_original_card C
    (S.delta_le_tau m) (S.tau_le_theta m) (S.theta_le_one m)

/-! ## Longness converts a small-delta power to an endpoint-ratio power -/

/-- A long interval turns `delta ^ (-epsilon)` into the reciprocal scale
gap.  Raising this comparison to a nonnegative exponent gives the precise
power later consumed by the adjacent numerical budget. -/
theorem delta_negative_mul_exponent_le_endpointRatio_power
    (S : FiniteScaleSequence delta outerDepth)
    (m : Fin outerDepth)
    {epsilon exponent : Real}
    (delta_pos : 0 < delta)
    (long : S.IsLong epsilon m)
    (exponent_nonneg : 0 <= exponent) :
    (delta : ENNReal) ^ (-(epsilon * exponent)) <=
      (((S.theta m / S.tau m : NNReal) : ENNReal) ^ exponent) := by
  let d : ENNReal := (delta : ENNReal)
  let a : ENNReal := ((S.theta m / S.tau m : NNReal) : ENNReal)
  have tau_pos : 0 < S.tau m :=
    delta_pos.trans_le (S.delta_le_tau m)
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr delta_pos.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hlong :
      (S.tau m : ENNReal) <=
        d ^ epsilon * (S.theta m : ENNReal) := by
    change (S.tau m : ENNReal) <=
      (delta : ENNReal) ^ epsilon * (S.theta m : ENNReal) at long
    simpa [d] using long
  have hscaled :
      d ^ (-epsilon) * (S.tau m : ENNReal) <=
        (S.theta m : ENNReal) := by
    calc
      d ^ (-epsilon) * (S.tau m : ENNReal) <=
          d ^ (-epsilon) *
            (d ^ epsilon * (S.theta m : ENNReal)) :=
        mul_le_mul' le_rfl hlong
      _ = (d ^ (-epsilon) * d ^ epsilon) *
          (S.theta m : ENNReal) := by ac_rfl
      _ = d ^ ((-epsilon) + epsilon) *
          (S.theta m : ENNReal) := by
        rw [ENNReal.rpow_add (-epsilon) epsilon hd0 hdTop]
      _ = (S.theta m : ENNReal) := by simp
  have hdeltaGap : d ^ (-epsilon) <= a := by
    change d ^ (-epsilon) <=
      ((S.theta m / S.tau m : NNReal) : ENNReal)
    rw [ENNReal.coe_div tau_pos.ne']
    exact (ENNReal.le_div_iff_mul_le
      (Or.inl (ENNReal.coe_ne_zero.mpr tau_pos.ne'))
      (Or.inl ENNReal.coe_ne_top)).2 hscaled
  calc
    (delta : ENNReal) ^ (-(epsilon * exponent)) =
        d ^ ((-epsilon) * exponent) := by
      congr 1
      ring
    _ = (d ^ (-epsilon)) ^ exponent :=
      ENNReal.rpow_mul d (-epsilon) exponent
    _ <= a ^ exponent :=
      ENNReal.rpow_le_rpow hdeltaGap exponent_nonneg
    _ = (((S.theta m / S.tau m : NNReal) : ENNReal) ^ exponent) := by
      rfl

/-! ## Explicit threshold and adjacent budget producer -/

/-- The exact small-delta threshold which absorbs the original cardinality
into the adjacent endpoint gap. -/
def firstNonLargeAdjacentCardThreshold
    (iota : Type*) [Fintype iota]
    (epsilon exponent : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold
    (Fintype.card iota : ENNReal) (epsilon * exponent)

theorem firstNonLargeAdjacentCardThreshold_pos
    (iota : Type*) [Fintype iota]
    (epsilon exponent : Real) :
    0 < firstNonLargeAdjacentCardThreshold iota epsilon exponent :=
  finiteConstantSmallDeltaThreshold_pos
    (Fintype.card iota : ENNReal) (epsilon * exponent)

/-- At any long interval, the explicit cardinal threshold produces exactly
the adjacent comparison used by `SelectedNumericalBudgets`. -/
theorem adjacentBudget_of_card_long_and_smallDelta
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta outerDepth)
    (m : Fin outerDepth)
    (profile : Nat -> Real) (stage : Nat)
    (epsilon_pos : 0 < epsilon)
    (profile_pred_pos : 0 < profile (stage - 1))
    (delta_pos : 0 < delta)
    (long : S.IsLong epsilon m)
    (delta_le : delta <= firstNonLargeAdjacentCardThreshold
      iota epsilon (profile (stage - 1))) :
    (C.toActualIntervalCovers S).adjacentCoarseValue m <=
      requiredAdjacentPowerAt S profile stage m := by
  have card_ne_top :
      (Fintype.card iota : ENNReal) ≠ ∞ :=
    ENNReal.natCast_ne_top (Fintype.card iota)
  have card_le_power :
      (Fintype.card iota : ENNReal) <=
        (delta : ENNReal) ^
          (-(epsilon * profile (stage - 1))) := by
    exact finiteConstant_le_delta_negativePower card_ne_top
      (mul_pos epsilon_pos profile_pred_pos) delta_pos delta_le
  calc
    (C.toActualIntervalCovers S).adjacentCoarseValue m <=
        (Fintype.card iota : ENNReal) :=
      actualAdjacentCoarseValue_le_original_card C S m
    _ <= (delta : ENNReal) ^
        (-(epsilon * profile (stage - 1))) := card_le_power
    _ <= (((S.theta m / S.tau m : NNReal) : ENNReal) ^
        profile (stage - 1)) :=
      delta_negative_mul_exponent_le_endpointRatio_power S m
        delta_pos long profile_pred_pos.le
    _ = requiredAdjacentPowerAt S profile stage m := by
      rfl

/-- First-non-large specialization: no longness certificate is supplied by
the caller. -/
theorem firstNonLarge_adjacentBudget_of_card_and_smallDelta
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta outerDepth)
    (profile : Nat -> Real) (stage : Nat)
    (not_all_large : Not (S.AllStepsLarge epsilon))
    (epsilon_pos : 0 < epsilon)
    (profile_pred_pos : 0 < profile (stage - 1))
    (delta_pos : 0 < delta)
    (delta_le : delta <= firstNonLargeAdjacentCardThreshold
      iota epsilon (profile (stage - 1))) :
    (C.toActualIntervalCovers S).adjacentCoarseValue
        (firstNonLargeStep S epsilon not_all_large) <=
      requiredAdjacentPowerAt S profile stage
        (firstNonLargeStep S epsilon not_all_large) := by
  exact adjacentBudget_of_card_long_and_smallDelta C S
    (firstNonLargeStep S epsilon not_all_large) profile stage
    epsilon_pos profile_pred_pos delta_pos
    (firstNonLargeStep_isLong S epsilon not_all_large) delta_le

/-! ## Direct bridge to the selected numerical and recovered endpoints -/

/-- The cardinal argument supplies the complete selected numerical budget
once the logically independent global product comparison is available.  The
global comparison is deliberately stated at its exact required power rather
than strengthened to a unit cap. -/
theorem firstNonLarge_selectedNumericalBudgets_of_global_and_card
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta outerDepth)
    (B : BufferedChainFamily outerDepth chainDepth)
    (profile : Nat -> Real) (stage : Nat)
    (not_all_large : Not (S.AllStepsLarge epsilon))
    (epsilon_pos : 0 < epsilon)
    (profile_pred_pos : 0 < profile (stage - 1))
    (delta_pos : 0 < delta)
    (delta_le : delta <= firstNonLargeAdjacentCardThreshold
      iota epsilon (profile (stage - 1)))
    (global_budget : actualGlobalProductAt B
        (firstNonLargeStep S epsilon not_all_large) <=
      requiredGlobalPowerAt S profile stage
        (firstNonLargeStep S epsilon not_all_large)) :
    SelectedNumericalBudgets B (C.toActualIntervalCovers S)
      profile stage (firstNonLargeStep S epsilon not_all_large) := by
  exact ⟨global_budget,
    firstNonLarge_adjacentBudget_of_card_and_smallDelta
      C S profile stage not_all_large epsilon_pos profile_pred_pos
        delta_pos delta_le⟩

#print axioms StickyScaleCover.coarseDeltaMax_le_activeCoarse_card
#print axioms interval_coarseDeltaMax_le_original_card
#print axioms actualAdjacentCoarseValue_le_original_card
#print axioms delta_negative_mul_exponent_le_endpointRatio_power
#print axioms adjacentBudget_of_card_long_and_smallDelta
#print axioms firstNonLarge_adjacentBudget_of_card_and_smallDelta
#print axioms firstNonLarge_selectedNumericalBudgets_of_global_and_card

end
end FamilyStickyScaleChainFirstNonLargeAdjacentCardBudgetProducerV1
