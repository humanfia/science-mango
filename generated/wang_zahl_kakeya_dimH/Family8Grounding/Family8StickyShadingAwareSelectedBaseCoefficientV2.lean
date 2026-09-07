import Family8Grounding.Family8StickyShadingAwareSelectedMassPopularFiberV2
import Family8Grounding.Family8StickyMassPopularRelativeScaleCoefficientV1
import Mathlib.Tactic

/-!
# Relative-scale envelope for the shading-aware selected base coefficient

The selected parent set is a literal subset of the active parents. Hence its
cardinality-times-fine-area coefficient is controlled by the existing active
coarse card-scale mass and the exact relative square.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8StickyShadingAwareSelectedBaseCoefficientV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8StickyMassPopularRelativeScaleCoefficientV1
open Family8StickyShadingAwareLogBucketSelectionV1
open Family8StickyShadingAwareCanonicalLogBucketSelectedV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The exact coefficient from the shading-aware mass-popular whole-fibre
bound lies below the scalar envelope already consumed by
`baseEnvelope_of_powerCaps`. -/
theorem shadingAwareSelected_cardCoefficient_le_relativeScaleEnvelope
    (S : StickyScaleCover fine rho) (Y : Shading fine.bodyFamily)
    (A : ENNReal) (hA0 : A ≠ 0) (hAtop : A ≠ ∞)
    (hrho : 0 < rho) (hactive : S.activeFine.Nonempty)
    (hmass : shadingMassOn Y S.activeFine ≠ 0) :
    let selected := shadingAwareSelectedParents
      S Y A hA0 hAtop hrho hactive hmass
    let retention : Nat := 2 * (Nat.log 2 (Fintype.card index) + 1)
    (((retention : ENNReal) * (selected.card : ENNReal)) *
        (8 * (delta : ENNReal) ^ 2)) ≤
      (retention : ENNReal) *
        (8 * ((activeCoarseCardScaleMass S : ENNReal) *
          (((delta : ENNReal) / (rho : ENNReal)) ^ 2))) := by
  dsimp only
  let selected := shadingAwareSelectedParents
    S Y A hA0 hAtop hrho hactive hmass
  let retention : Nat := 2 * (Nat.log 2 (Fintype.card index) + 1)
  have hsubset : selected ⊆ S.activeCoarse := by
    simpa only [selected] using shadingAwareSelectedParents_subset_activeCoarse
      S Y A hA0 hAtop hrho hactive hmass
  have hcardNat : selected.card ≤ S.activeCoarse.card :=
    Finset.card_le_card hsubset
  have hcard : (selected.card : ENNReal) ≤
      (S.activeCoarse.card : ENNReal) := by
    exact_mod_cast hcardNat
  have hidentity :=
    activeCoarse_card_mul_delta_sq_eq_cardScaleMass_mul_ratio_sq S hrho
  calc
    (((retention : ENNReal) * (selected.card : ENNReal)) *
        (8 * (delta : ENNReal) ^ 2)) =
      (retention : ENNReal) * 8 *
        ((selected.card : ENNReal) * (delta : ENNReal) ^ 2) := by
      ring
    _ ≤ (retention : ENNReal) * 8 *
        ((S.activeCoarse.card : ENNReal) * (delta : ENNReal) ^ 2) := by
      gcongr
    _ = (retention : ENNReal) *
        (8 * ((activeCoarseCardScaleMass S : ENNReal) *
          (((delta : ENNReal) / (rho : ENNReal)) ^ 2))) := by
      rw [hidentity]
      ring

#print axioms
  shadingAwareSelected_cardCoefficient_le_relativeScaleEnvelope

end
end Family8StickyShadingAwareSelectedBaseCoefficientV2
