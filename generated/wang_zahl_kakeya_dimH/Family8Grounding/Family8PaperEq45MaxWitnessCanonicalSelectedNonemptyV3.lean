import Family8Grounding.Family8PaperEq45MaxWitnessCanonicalSelectedFieldsV1
import Family8Grounding.Family8SelectedOccurrenceMaxOwnerHullAggregateV2
import Mathlib.Tactic

/-!
# Nonemptiness of the exact-degree canonical occurrence selection

Positive full outer occurrence mass passes first to the finite-argmax
max-owner refinement and then through the exact-degree weighted conflict
selection.  The resulting literal selected occurrence set, and hence its
selected fine-index union, is nonempty.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxWitnessCanonicalSelectedNonemptyV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8PaperEq45MaxWitnessCanonicalSelectedFieldsV1
open Family8PaperEq45MaxWitnessCanonicalSelectedFiniteV2
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerHullAggregateV2
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho sigma : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  (S : StickyScaleCover fine rho)
  (U : StickyScaleCover (S.coarse.restrictTo S.activeCoarse) sigma)
  (P : GreedyDensityPartition S.activeCoarseFamily
    (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
    (hullContainer S.activeCoarseFamily) Finset.univ)
  (Y : Shading S.activeCoarseFamily)

theorem canonicalSelectedFine_nonempty_of_outerShadingMass_ne_zero
    (houter : (selectedOccurrenceOuterShading
      (actualUpperPartition S U P) Y Finset.univ).shadingMass ≠ 0) :
    (selectedOccurrenceFineIndices (actualUpperPartition S U P)
      (canonicalSelectedOccurrences S U P Y)).Nonempty := by
  let Q := actualUpperPartition S U P
  let W := canonicalEq45ConflictSelection S U P Y
  let R := canonicalSelectedOccurrences S U P Y
  let N := Fintype.card (ActiveParentIndex S)
  have hmaxBound :
      (selectedOccurrenceOuterShading Q Y Finset.univ).shadingMass ≤
        (N : ENNReal) *
          (selectedOccurrenceMaxOwnerHullShading U Q Y Finset.univ).shadingMass := by
    exact selectedOccurrenceOuterShading_mass_le_maxOwnerHull
      U Q Y Finset.univ N (fun k _hk =>
        actualUpperPartition_block_fibre_card_le_activeParentCard S U P k)
  have hmax :
      (selectedOccurrenceMaxOwnerHullShading U Q Y Finset.univ).shadingMass ≠
        0 := by
    intro hzero
    apply houter
    apply le_antisymm
    · simpa only [hzero, mul_zero] using hmaxBound
    · exact bot_le
  have hretained :
      (selectedOccurrenceMaxOwnerHullShading U Q Y Finset.univ).shadingMass ≤
        canonicalEq45ConflictLoss S U *
          (selectedOccurrenceMaxOwnerHullShading U Q Y R).shadingMass := by
    simpa only [Q, W, R, canonicalSelectedOccurrences] using
      (selectedMaxOwner_refinedShadedMass_retention
        U Q Y Finset.univ (canonicalEq45ConflictLoss S U) W)
  have hselectedMass :
      (selectedOccurrenceMaxOwnerHullShading U Q Y R).shadingMass ≠ 0 := by
    intro hzero
    apply hmax
    apply le_antisymm
    · simpa only [hzero, mul_zero] using hretained
    · exact bot_le
  have hR : R.Nonempty := by
    by_contra hnot
    apply hselectedMass
    unfold Shading.shadingMass
    apply Finset.sum_eq_zero
    intro q _hq
    obtain ⟨k, hk, _⟩ :=
      (mem_selectedOccurrenceIndices Q R q.1).mp q.2
    exact (hnot ⟨k, hk⟩).elim
  obtain ⟨k, hk⟩ := hR
  obtain ⟨i, hi⟩ := (blockAt S.activeCoarseFamily Q k).fiber_nonempty
  refine ⟨i, ?_⟩
  exact Finset.mem_biUnion.mpr ⟨k, hk, hi⟩

#print axioms canonicalSelectedFine_nonempty_of_outerShadingMass_ne_zero

end
end Family8PaperEq45MaxWitnessCanonicalSelectedNonemptyV3
