import Family8Grounding.Family8PaperEq45MaxOwnerRefinedInputProducerV1
import Mathlib.Tactic

/-!
# Canonical numerical Delta for the genuine max-owner Eq. (45) input, V2

The refined input producer exposes the honest inequality
`frostmanConstant * ambientDensity <= Delta`.  Both factors are finite for
the actual finite family and positive ambient body, so their product itself
has a canonical `NNReal` representative.  This successor chooses that value
and thereby removes `Delta` and its domination proof as upstream data.

V1 omitted the namespace exporting the witness-cover loss and is not
imported.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxOwnerCanonicalDeltaV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8AmbientFamilyVolumeDensityV2
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8PaperEq45MaxOwnerRefinedBundleV2
open Family8PaperEq45MaxOwnerRefinedInputProducerV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerHullAggregateV2
open Family8SelectedOccurrenceMaxOwnerHullFrostmanProducerV3
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u

/-- The literal finite Eq. (45) concentration coefficient, represented as an
`NNReal`. -/
def canonicalMaxOwnerDelta
    {iota : Type u} [Fintype iota]
    (CF : ENNReal) (M : Nat) (delta a b : NNReal)
    (F : ConvexFamily iota) (ambient : ConvexBody Space) : NNReal :=
  (maxOwnerRefinedFrostmanConstant CF M delta a b *
    ambientFamilyVolumeDensity F ambient).toNNReal

theorem maxOwnerRefinedFrostmanConstant_ne_top
    (CF : ENNReal) (M : Nat) (delta a b : NNReal)
    (hCF : CF ≠ ∞) (hdelta : 0 < delta) :
    maxOwnerRefinedFrostmanConstant CF M delta a b ≠ ∞ := by
  have hden0 : ((delta : ENNReal) ^ 2 / 2) ≠ 0 := by
    simp [ENNReal.coe_ne_zero.mpr hdelta.ne']
  have hcover : maxOwnerHullWitnessCoverLoss delta a b ≠ ∞ := by
    unfold maxOwnerHullWitnessCoverLoss
    exact ENNReal.div_ne_top (by finiteness) hden0
  unfold maxOwnerRefinedFrostmanConstant
  exact ENNReal.mul_ne_top hcover
    (ENNReal.mul_ne_top hCF (by finiteness))

/-- The canonical `NNReal` value is exactly the required product, hence in
particular dominates it without any supplied numerical callback. -/
theorem canonicalMaxOwnerDelta_coe
    {iota : Type u} [Fintype iota]
    (CF : ENNReal) (M : Nat) (delta a b : NNReal)
    (F : ConvexFamily iota) (ambient : ConvexBody Space)
    (hCF : CF ≠ ∞) (hdelta : 0 < delta)
    (hambientVolume : volume (ambient : Set Space) ≠ 0) :
    (canonicalMaxOwnerDelta CF M delta a b F ambient : ENNReal) =
      maxOwnerRefinedFrostmanConstant CF M delta a b *
        ambientFamilyVolumeDensity F ambient := by
  unfold canonicalMaxOwnerDelta
  rw [ENNReal.coe_toNNReal]
  exact ENNReal.mul_ne_top
    (maxOwnerRefinedFrostmanConstant_ne_top CF M delta a b hCF hdelta)
    (ambientFamilyVolumeDensity_ne_top F ambient hambientVolume)

variable {delta rho a b : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  (C : StickyScaleCover fine rho)
  {P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates C.activeFine) (hullContainer fine.bodyFamily)
    C.activeFine}

/-- Construct the complete refined input using the canonical numerical
`Delta`; callers no longer choose either `Delta` or its domination proof. -/
noncomputable def paperEq45MaxOwnerRefinedInput_of_sourceFine_canonicalDelta
    (Y : Shading fine.bodyFamily)
    (R0 : Finset (Fin (blocks fine.bodyFamily P).length))
    (loss : ENNReal)
    (W : DoubledParentConflictWeightedSelection C
      (occurrenceMaxOwnerMass C P Y R0) loss)
    (M : Nat)
    (hcard : ∀ k ∈ R0, (blockAt fine.bodyFamily P k).fiber.card ≤ M)
    (hrho : 0 < rho) (hb : b ≤ rho)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (comparisonConstant : NNReal)
    (all_isPlank : ∀ q, IsPlank comparisonConstant a b
      (selectedOccurrenceMaxOwnerHullFamily C P Y
        (occurrencesMaxOwnedBy C P Y R0 W.selected) q))
    (ambient : ConvexBody Space) (ambientComparisonConstant : NNReal)
    (ambient_is_unit_scale : IsPlank ambientComparisonConstant 1 1 ambient)
    (contained_in_ambient : ∀ q,
      (selectedOccurrenceMaxOwnerHullFamily C P Y
        (occurrencesMaxOwnedBy C P Y R0 W.selected) q : Set Space) ⊆
        (ambient : Set Space))
    (CF : ENNReal) (hCF : CF ≠ ∞)
    (source_frostman : IsFrostmanOn CF fine.bodyFamily
      (selectedOccurrenceFineIndices P
        (occurrencesMaxOwnedBy C P Y R0 W.selected)) ambient) :
    PaperEq45MaxOwnerRefinedInput C Y R0 loss W a b := by
  let R := occurrencesMaxOwnedBy C P Y R0 W.selected
  let F := selectedOccurrenceMaxOwnerHullFamily C P Y R
  let Delta := canonicalMaxOwnerDelta CF M delta a b F ambient
  have hambientVolume : volume (ambient : Set Space) ≠ 0 :=
    ne_of_gt ambient_is_unit_scale.volume_pos
  apply paperEq45MaxOwnerRefinedInput_of_sourceFine C Y R0 loss W M hcard
    hrho hb hdelta hdeltaHalf comparisonConstant all_isPlank ambient
    ambientComparisonConstant ambient_is_unit_scale contained_in_ambient CF
    source_frostman Delta
  rw [canonicalMaxOwnerDelta_coe CF M delta a b F ambient hCF hdelta
    hambientVolume]

#print axioms canonicalMaxOwnerDelta
#print axioms maxOwnerRefinedFrostmanConstant_ne_top
#print axioms canonicalMaxOwnerDelta_coe
#print axioms paperEq45MaxOwnerRefinedInput_of_sourceFine_canonicalDelta

end
end Family8PaperEq45MaxOwnerCanonicalDeltaV2
