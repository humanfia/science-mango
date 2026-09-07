import Family8Grounding.Family8CanonicalExactWeightedDef212ExactScaleInputsRHSV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8CanonicalExactWeightedDef212EpsilonDependentStepV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV14
open Family8FrostmanWeightedSelectedDirectBaseBudgetV3
open Family8CanonicalExactWeightedDef212ExactScaleInputsRHSV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Quantifier-correct epsilon-dependent exact-incidence step

The exact weighted RHS connector has an unavoidable `2 * nu` term when the
Frostman exponent drops from `beta` to `beta - nu`.  Consequently its direct
property-level consequence is an epsilon-dependent right-limit step, not a
fixed positive decrement.  This file chooses every numerical parameter and
the terminal scale explicitly and records that exact quantifier order.
-/

/-- One common small exponent pays source density, the exact conflict degree,
the selected base volume, and the requested epsilon gap. -/
def exactWeightedEpsilonStep (oldEta targetEpsilon : Real) : Real :=
  min (oldEta / 12) (min (targetEpsilon / 64) 1)

theorem exactWeightedEpsilonStep_pos
    {oldEta targetEpsilon : Real}
    (holdEta : 0 < oldEta) (htarget : 0 < targetEpsilon) :
    0 < exactWeightedEpsilonStep oldEta targetEpsilon := by
  unfold exactWeightedEpsilonStep
  exact lt_min (by linarith) (lt_min (by linarith) (by norm_num))

theorem exactWeightedEpsilonStep_le_oldEta_div_twelve
    (oldEta targetEpsilon : Real) :
    exactWeightedEpsilonStep oldEta targetEpsilon <= oldEta / 12 := by
  exact min_le_left _ _

theorem exactWeightedEpsilonStep_le_targetEpsilon_div_sixtyFour
    (oldEta targetEpsilon : Real) :
    exactWeightedEpsilonStep oldEta targetEpsilon <= targetEpsilon / 64 := by
  exact (min_le_right _ _).trans (min_le_left _ _)

theorem exactWeightedEpsilonStep_le_one
    (oldEta targetEpsilon : Real) :
    exactWeightedEpsilonStep oldEta targetEpsilon <= 1 := by
  exact (min_le_right _ _).trans (min_le_right _ _)

/-- All three exponent inequalities consumed by the exact weighted endpoint,
under the explicit common choice `q`. -/
theorem exactWeightedEpsilonStep_budgets
    {oldEta targetEpsilon : Real}
    (holdEta : 0 < oldEta) (htarget : 0 < targetEpsilon) :
    let q := exactWeightedEpsilonStep oldEta targetEpsilon
    q <= oldEta - activeOwnerExactDegreePowerEnvelope q q q ∧
    2 * q + directSelectedBasePowerLoss q q q q <= oldEta ∧
    activeOwnerExactDegreePowerEnvelope q q q + 2 * q +
          (2 * q + activeOwnerExactDegreePowerEnvelope q q q) * q / 2 <=
      targetEpsilon - targetEpsilon / 4 := by
  let q := exactWeightedEpsilonStep oldEta targetEpsilon
  have hqPos : 0 < q := exactWeightedEpsilonStep_pos holdEta htarget
  have hq0 : 0 <= q := hqPos.le
  have hqEta : q <= oldEta / 12 :=
    exactWeightedEpsilonStep_le_oldEta_div_twelve _ _
  have hqTarget : q <= targetEpsilon / 64 :=
    exactWeightedEpsilonStep_le_targetEpsilon_div_sixtyFour _ _
  have hqOne : q <= 1 := exactWeightedEpsilonStep_le_one _ _
  have hqSq : q * q <= q := by
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hqOne)]
  dsimp only
  rw [directSelectedBasePowerLoss_eq]
  unfold activeOwnerExactDegreePowerEnvelope
  constructor
  · linarith
  constructor
  · linarith
  · nlinarith

/-- Terminal scale simultaneously satisfying the old property scale, both
finite-constant absorption thresholds, and the exact-incidence `rho <= 1/16`
side condition. -/
def exactWeightedEpsilonStepDeltaThreshold
    (oldDelta0 : NNReal) (q : Real) : NNReal :=
  min oldDelta0
    (min (activeOwnerExactDegreeSmallDeltaThreshold q)
      (min (directSelectedBaseVolumeSmallDeltaThreshold q) (1 / 16)))

theorem exactWeightedEpsilonStepDeltaThreshold_pos
    {oldDelta0 : NNReal} (holdDelta0 : 0 < oldDelta0) (q : Real) :
    0 < exactWeightedEpsilonStepDeltaThreshold oldDelta0 q := by
  unfold exactWeightedEpsilonStepDeltaThreshold
  exact lt_min holdDelta0
    (lt_min (activeOwnerExactDegreeSmallDeltaThreshold_pos q)
      (lt_min (directSelectedBaseVolumeSmallDeltaThreshold_pos q)
        (by norm_num)))

/-- Quantifier-correct fixed-epsilon consequence.  For every requested
`targetEpsilon`, the source Frostman property first chooses uniform old
parameters; only then is the positive decrement `q` fixed, uniformly for all
later data at that target epsilon.  The actual scale cover is obtained by
`M.cover` inside `averageMultiplicity_le_improvedRHS_of_exactScaleInputs`.

The two remaining datum-level geometric inputs are explicit and substantive:
an existing `ExactScaleDef212Inputs M Cnn` package and a sharp source
Katz--Tao concentration bound at constant `delta^(-q)`. -/
theorem exists_epsilonDependent_exactWeighted_improved_parameters
    {beta targetEpsilon : Real}
    (hF : FrostmanProperty beta)
    (htarget : 0 < targetEpsilon) (hbeta : beta <= 2) :
    ∃ q : Real, ∃ delta1 : NNReal,
      0 < q ∧ q <= targetEpsilon / 64 ∧
      0 < delta1 ∧ delta1 <= (2 : NNReal)⁻¹ ∧
      ∀ {delta : NNReal} {index : Type}
          [Fintype index] [DecidableEq index]
          (D : ActualTubeDatum delta index) (_hD : D.IsAdmissible),
        delta <= delta1 ->
        FrostmanHypotheses D q ->
        ∀ (M : StickyMultiscaleCover D.family) (Cnn : NNReal),
          ExactScaleDef212Inputs M Cnn ->
          IsKatzTao ((delta : ENNReal) ^ (-q)) D.family.bodyFamily ->
          D.shading.averageMultiplicity <=
            frostmanMultiplicityRHS delta D.actualFamilyVolume
              targetEpsilon (beta - q) := by
  obtain ⟨oldEta, oldDelta0, holdEta, holdDelta0, _holdDelta0Half, hAt⟩ :=
    hF.exists_parameters (show 0 < targetEpsilon / 4 by linarith)
  let q := exactWeightedEpsilonStep oldEta targetEpsilon
  let delta1 := exactWeightedEpsilonStepDeltaThreshold oldDelta0 q
  have hqPos : 0 < q := exactWeightedEpsilonStep_pos holdEta htarget
  have hqTarget : q <= targetEpsilon / 64 :=
    exactWeightedEpsilonStep_le_targetEpsilon_div_sixtyFour _ _
  have hdelta1Pos : 0 < delta1 :=
    exactWeightedEpsilonStepDeltaThreshold_pos holdDelta0 q
  have hdelta1Old : delta1 <= oldDelta0 := by
    exact min_le_left _ _
  have hdelta1Degree :
      delta1 <= activeOwnerExactDegreeSmallDeltaThreshold q := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hdelta1Volume :
      delta1 <= directSelectedBaseVolumeSmallDeltaThreshold q := by
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hdelta1Sixteen : delta1 <= (1 / 16 : NNReal) := by
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))
  have hdelta1Half : delta1 <= (2 : NNReal)⁻¹ :=
    hdelta1Sixteen.trans (by
      exact_mod_cast (by norm_num : (1 / 16 : Real) <= (2 : Real)⁻¹))
  obtain ⟨hdensityBudget, hbaseBudget, hRHSBudget⟩ :=
    exactWeightedEpsilonStep_budgets holdEta htarget
  refine ⟨q, delta1, hqPos, hqTarget, hdelta1Pos, hdelta1Half, ?_⟩
  intro delta index _ _ D hD hdelta hSource M Cnn H hKT
  have hdeltaOld : delta <= oldDelta0 := hdelta.trans hdelta1Old
  have hdeltaDegree :
      delta <= activeOwnerExactDegreeSmallDeltaThreshold q :=
    hdelta.trans hdelta1Degree
  have hdeltaVolume :
      delta <= directSelectedBaseVolumeSmallDeltaThreshold q :=
    hdelta.trans hdelta1Volume
  have hdeltaSixteen : delta <= (1 / 16 : NNReal) :=
    hdelta.trans hdelta1Sixteen
  have hdeltaOneENN : (delta : ENNReal) <= 1 := by
    exact_mod_cast (hD.delta_le_half.trans (by norm_num))
  have hAone : 1 <= (delta : ENNReal) ^ (-q) := by
    exact ENNReal.one_le_rpow_of_pos_of_le_one_of_neg
      (ENNReal.coe_pos.mpr hD.delta_pos) hdeltaOneENN (by linarith)
  exact averageMultiplicity_le_improvedRHS_of_exactScaleInputs
    (frostmanEpsilon := targetEpsilon / 4) (frostmanEta := oldEta)
    (sourceExponent := q) (targetEpsilon := targetEpsilon) (nu := q)
    (scaleEpsilon := q) (katzTaoExponent := q)
    (degreeAbsorbExponent := q) (volumeAbsorbExponent := q)
    (A := (delta : ENNReal) ^ (-q))
    hAt D hD hSource M H hqPos.le hqPos hqPos hdeltaDegree
    hdeltaVolume hAone le_rfl hKT hdeltaSixteen hdeltaOld
    hdensityBudget hbaseBudget hqPos.le (by linarith) hRHSBudget

/-- A fixed positive decrement cannot satisfy even the unavoidable
`2 * nu` part of the epsilon budget for every positive target epsilon.
Thus the theorem above cannot honestly be repackaged as
`FrostmanProperty (beta - nu)` with one fixed `nu > 0`. -/
theorem no_fixed_positive_nu_from_direct_epsilon_gap
    {nu : Real} (hnu : 0 < nu) :
    ¬ ∀ targetEpsilon : Real, 0 < targetEpsilon ->
      ∃ sourceEpsilon : Real, 0 < sourceEpsilon ∧
        2 * nu <= targetEpsilon - sourceEpsilon := by
  intro h
  obtain ⟨sourceEpsilon, hsource, hgap⟩ := h nu hnu
  linarith

#print axioms exactWeightedEpsilonStep_pos
#print axioms exactWeightedEpsilonStep_budgets
#print axioms exactWeightedEpsilonStepDeltaThreshold_pos
#print axioms exists_epsilonDependent_exactWeighted_improved_parameters
#print axioms no_fixed_positive_nu_from_direct_epsilon_gap

end
end Family8CanonicalExactWeightedDef212EpsilonDependentStepV1
