import Family8Grounding.Family8PaperEq45MaxWitnessBufferedCanonicalSelectedFieldsV1
import Mathlib.Tactic

/-!
# Finite structural bounds for the actual buffered selected family

These small lemmas isolate every non-algebraic input to the canonical
outer/thick estimate, so the final scalar consumer need not elaborate a large
dependent selected-input expression.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxWitnessBufferedCanonicalSelectedFiniteBoundsV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8ClosedBallFourBufferedCommonScaleUnitPlankV1
open Family8PaperEq45MaxWitnessBufferedCanonicalV1
open Family8PaperEq45MaxWitnessBufferedCanonicalSelectedFieldsV1
open Family8PaperEq45MaxWitnessCanonicalSelectedFiniteV2
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerHullFrostmanProducerV3
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8SelectedOccurrenceMaxWitnessBufferedCommonScaleDatumV1
open Family8StickyParentHullVolumeBoundV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

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

theorem canonicalBufferedSelectedRefinedCF_ne_top
    (CF : ENNReal) (hCF : CF ≠ ∞) :
    canonicalBufferedSelectedRefinedCF S CF ≠ ∞ := by
  exact bufferedRefinedFrostmanConstant_ne_top CF
    (Fintype.card (ActiveParentIndex S)) hCF

theorem canonicalBufferedSelectedFamily_contained
    (CF : ENNReal)
    (source_frostman : IsFrostmanOn CF S.activeCoarseFamily
      (selectedOccurrenceFineIndices (actualUpperPartition S U P)
        (canonicalBufferedSelectedOccurrences S U P Y))
      closedBallFourBody) :
    ∀ q, (canonicalBufferedSelectedFamily S U P Y q : Set Space) ⊆
      (canonicalBufferedSelectedAmbient (rho := rho) : Set Space) := by
  intro q
  exact Set.image_mono
    (selectedOccurrenceMaxWitness_subset_ambient U Y
      (canonicalBufferedSelectedOccurrences S U P Y)
      closedBallFourBody source_frostman q)

theorem canonicalBufferedSelectedAmbient_volume_ne_zero
    (hrhoHalf : rho ≤ (2 : NNReal)⁻¹) :
    volume (canonicalBufferedSelectedAmbient (rho := rho) : Set Space) ≠ 0 := by
  exact ne_of_gt
    (bufferedCommonScale_closedBallFour_isPlank hrhoHalf).volume_pos

theorem canonicalBufferedSelected_card_le_activeParentCard_ennreal :
    (Fintype.card {q // q ∈ selectedOccurrenceIndices
      (actualUpperPartition S U P)
      (canonicalBufferedSelectedOccurrences S U P Y)} : ENNReal) ≤
      (Fintype.card (ActiveParentIndex S) : ENNReal) := by
  exact_mod_cast canonicalEq45SelectedWitness_card_le_activeParentCard S U P Y

#print axioms canonicalBufferedSelectedRefinedCF_ne_top
#print axioms canonicalBufferedSelectedFamily_contained
#print axioms canonicalBufferedSelectedAmbient_volume_ne_zero
#print axioms canonicalBufferedSelected_card_le_activeParentCard_ennreal

end
end Family8PaperEq45MaxWitnessBufferedCanonicalSelectedFiniteBoundsV1
