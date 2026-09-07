import Family8Grounding.Family8ExactAssemblyMassPopularActualAverageV2
import Family8Grounding.Family8SelectedParentFineLevelBucketRetentionV5

/-!
# One mass-popular exact-assembly fibre and its actual plank bucket, V2

This is the occurrence-indexed specialization of the finite mass-popularity
theorem.  It selects one genuine greedy block which simultaneously retains
source active mass with the explicit loss `loss * P.length`, is the fine
actual-average factor in the exact outer/fine product, and admits the existing
V9 affine plank bucket with its actual `IsPlank 576` certificate.

Multiplying the two honest retention estimates gives a source-to-bucket mass
comparison on that same block.  No surviving-fibre popularity premise is
left to the caller.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentMassPopularFineLevelBucketV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8ExactAssemblyMassPopularActualAverageV2.ExactAssembly
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentFineLevelBucketRetentionV5
open Family8SelectedParentFineLevelLiftV2
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- One actual greedy occurrence is quantitatively mass-popular, realizes the
fine actual-average factor, and has an automatically produced affine plank
bucket retaining that same mass. -/
theorem exists_massPopularGreedyBlock_actualAverage_and_affinePlankBucket
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss)
    (hsource :
      (IndexedShadingRefinement.restrictTo
        (parentAggregatedShading S D.shading)
        (greedyParentFactorization S P).index.fine).shading.shadingMass ≠ 0) :
    ∃ k : Fin (blocks S.activeCoarseFamily P).length,
      (IndexedShadingRefinement.restrictTo
          (parentAggregatedShading S D.shading)
          (greedyParentFactorization S P).index.fine).shading.shadingMass ≤
        (loss : ENNReal) * (P.length : ENNReal) *
          (sourceFineLevelShading A (some k)).shadingMass ∧
      0 < volume (sourceFineLevelShading A (some k)).shadedUnion ∧
      A.refinement.shading.averageMultiplicity ≤
        ((greedyParentFactorization S P).inducedShading
          A.refinement.shading).averageMultiplicity *
          (sourceFineLevelShading A (some k)).averageMultiplicity ∧
      let B := (blockAt S.activeCoarseFamily P k).fiber
      let Ylevel :=
        fineShadingAtGreedyBlockLevel S D.shading P k A.fineLevel
      let e := contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
      let parent := {p // p ∈ B}
      let side : parent → Fin 3 → NNReal := fun p =>
        selectedParentLongRelabeledSide e S B hrho p
      ∃ label : Fin 3 → Int,
        label ∈ occupiedWeightBuckets (Finset.univ : Finset parent)
          (fun p => sideShapeLabel (side p)) ∧
        affineJacobian (bucketNormalizedAffineEquiv e label) *
            (IndexedShadingRefinement.restrictTo
              (parentAggregatedShading S D.shading)
              (greedyParentFactorization S P).index.fine).shading.shadingMass ≤
          ((loss : ENNReal) * (P.length : ENNReal)) *
            (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
              (selectedParentPlankBucketShading
                e S Ylevel B hrho label).shadingMass ∧
        0 < bucketShortA label ∧
        bucketShortA label ≤ bucketShortB label ∧
        bucketShortB label ≤ 1 ∧
        ∀ p, p ∈ sideShapeBucket Finset.univ side label →
          IsPlank 576 (bucketShortA label) (bucketShortB label)
            (selectedParentAffineFamily
              (bucketNormalizedAffineEquiv e label) S B p) := by
  obtain ⟨q, hq, hmass, hvolume, hproduct⟩ :=
    exists_massPopular_sourceFineLevelShading_actualAverage A hsource
  change q ∈ (indexFactorization S.activeCoarseFamily P).coarse at hq
  rw [indexFactorization_coarse, occurrenceIndices] at hq
  obtain ⟨k, _hk, hq⟩ := Finset.mem_image.mp hq
  subst q
  have hmass' :
      (IndexedShadingRefinement.restrictTo
          (parentAggregatedShading S D.shading)
          (greedyParentFactorization S P).index.fine).shading.shadingMass ≤
        (loss : ENNReal) * (P.length : ENNReal) *
          (sourceFineLevelShading A (some k)).shadingMass := by
    change _ ≤ (loss : ENNReal) *
      ((indexFactorization S.activeCoarseFamily P).coarse.card : ENNReal) * _
      at hmass
    rw [coarse_card_eq_length S.activeCoarseFamily P] at hmass
    exact hmass
  obtain ⟨label, hoccupied, hbucket, ha, hab, hb, hplank⟩ :=
    exists_selectedParentFineLevelPlankBucket_affineShadingMassRetention
      D hD S hrho hrhoOne P k r hr A
  dsimp only
  refine ⟨k, hmass', hvolume, hproduct, label, hoccupied, ?_,
    ha, hab, hb, hplank⟩
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let Ylevel := fineShadingAtGreedyBlockLevel
    S D.shading P k A.fineLevel
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  calc
    affineJacobian (bucketNormalizedAffineEquiv e label) *
        (IndexedShadingRefinement.restrictTo
          (parentAggregatedShading S D.shading)
          (greedyParentFactorization S P).index.fine).shading.shadingMass ≤
      affineJacobian (bucketNormalizedAffineEquiv e label) *
        (((loss : ENNReal) * (P.length : ENNReal)) *
          (sourceFineLevelShading A (some k)).shadingMass) := by
      exact mul_le_mul' le_rfl hmass'
    _ = ((loss : ENNReal) * (P.length : ENNReal)) *
        (affineJacobian (bucketNormalizedAffineEquiv e label) *
          (sourceFineLevelShading A (some k)).shadingMass) := by
      ac_rfl
    _ ≤ ((loss : ENNReal) * (P.length : ENNReal)) *
        ((selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
          (selectedParentPlankBucketShading
            e S Ylevel B hrho label).shadingMass) := by
      exact mul_le_mul' le_rfl hbucket
    _ = ((loss : ENNReal) * (P.length : ENNReal)) *
        (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
          (selectedParentPlankBucketShading
            e S Ylevel B hrho label).shadingMass := by
      ac_rfl

#print axioms
  exists_massPopularGreedyBlock_actualAverage_and_affinePlankBucket

end

end Family8SelectedParentMassPopularFineLevelBucketV2
