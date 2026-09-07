import Family8Grounding.Family8PaperEq45MaxWitnessBufferedCanonicalV1
import Family8Grounding.Family8PaperEq45MaxWitnessCanonicalSelectedInputV3
import Mathlib.Tactic

/-!
# Actual exact-degree selected input for buffered Equation (45)

This thin adapter reuses the already constructed exact doubled-parent
selection and its active-parent fibre cap.  It changes only the geometric
normalization: the literal selected witnesses are sent through the certified
buffered common-scale map, whose ambient body is now a genuine unit plank.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxWitnessBufferedCanonicalSelectedInputV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family6AffineConvexVolumeCoreV1
open Family8PaperEq45MaxWitnessBufferedCanonicalV1
open Family8PaperEq45MaxWitnessCanonicalSelectedFiniteV2
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8StickyParentHullVolumeBoundV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

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

/-- The exact-degree selected family, now normalized by the buffered map. -/
noncomputable def canonicalEq45BufferedInput
    (hrho : 0 < rho) (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (h2rho : 2 * rho ≤ sigma)
    (CF : ENNReal) (hCF : CF ≠ ∞)
    (source_frostman : IsFrostmanOn CF S.activeCoarseFamily
      (selectedOccurrenceFineIndices (actualUpperPartition S U P)
        (occurrencesMaxOwnedBy U (actualUpperPartition S U P) Y
          Finset.univ (canonicalEq45ConflictSelection S U P Y).selected))
      closedBallFourBody) :
    PaperEq45MaxWitnessBufferedInput U Y Finset.univ
      (canonicalEq45ConflictLoss S U)
      (canonicalEq45ConflictSelection S U P Y) :=
  paperEq45MaxWitnessBufferedInput_closedBallFour
    U Y Finset.univ (canonicalEq45ConflictLoss S U)
    (canonicalEq45ConflictSelection S U P Y)
    (Fintype.card (ActiveParentIndex S))
    (fun k _hk =>
      actualUpperPartition_block_fibre_card_le_activeParentCard S U P k)
    hrho hrhoHalf h2rho CF hCF source_frostman

@[simp] theorem canonicalEq45BufferedInput_fibreCardCap
    (hrho : 0 < rho) (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (h2rho : 2 * rho ≤ sigma)
    (CF : ENNReal) (hCF : CF ≠ ∞)
    (source_frostman : IsFrostmanOn CF S.activeCoarseFamily
      (selectedOccurrenceFineIndices (actualUpperPartition S U P)
        (occurrencesMaxOwnedBy U (actualUpperPartition S U P) Y
          Finset.univ (canonicalEq45ConflictSelection S U P Y).selected))
      closedBallFourBody) :
    (canonicalEq45BufferedInput S U P Y hrho hrhoHalf h2rho
      CF hCF source_frostman).fibreCardCap =
        Fintype.card (ActiveParentIndex S) := by
  rfl

#print axioms canonicalEq45BufferedInput
#print axioms canonicalEq45BufferedInput_fibreCardCap

end
end Family8PaperEq45MaxWitnessBufferedCanonicalSelectedInputV1
