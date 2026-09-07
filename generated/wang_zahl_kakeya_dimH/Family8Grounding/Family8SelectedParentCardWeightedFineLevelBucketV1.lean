import Family8Grounding.Family8ExactAssemblyCardWeightedMassPopularActualAverageV2
import Family8Grounding.Family8SelectedParentFineLevelBucketRetentionV5
import Mathlib.Tactic

/-!
# A card-weighted selected-parent fibre and its actual plank bucket

The selected greedy occurrence maximizes fine-level mass per member.  Its
block cardinality remains on the source side of the retention inequality,
where it can cancel the literal selected-bucket cardinality in the Cordoba
mean.  The total loss is the cardinality of the active parent family, not the
product of the number of blocks and the selected bucket cardinality.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentCardWeightedFineLevelBucketV1

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
open Family8ExactAssemblyCardWeightedMassPopularActualAverageV2.ExactAssembly
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
set_option maxHeartbeats 7000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- One genuine greedy occurrence carries the card-weighted retained source
mass, realizes the actual-average product, and supplies an actual affine
plank bucket on that same occurrence. -/
theorem exists_cardWeightedGreedyBlock_actualAverage_and_affinePlankBucket
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
          (greedyParentFactorization S P).index.fine).shading.shadingMass *
            ((blockAt S.activeCoarseFamily P k).fiber.card : ENNReal) ≤
        (loss : ENNReal) *
          (Fintype.card (ActiveParentIndex S) : ENNReal) *
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
        (affineJacobian (bucketNormalizedAffineEquiv e label) *
            (IndexedShadingRefinement.restrictTo
              (parentAggregatedShading S D.shading)
              (greedyParentFactorization S P).index.fine).shading.shadingMass) *
              (B.card : ENNReal) ≤
          ((loss : ENNReal) *
              (Fintype.card (ActiveParentIndex S) : ENNReal)) *
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
  have hfiber : ∀ q ∈ (greedyParentFactorization S P).index.coarse,
      ((greedyParentFactorization S P).index.fiber q).Nonempty := by
    intro q hq
    change q ∈ (indexFactorization S.activeCoarseFamily P).coarse at hq
    rw [indexFactorization_coarse, occurrenceIndices] at hq
    obtain ⟨k, _hk, rfl⟩ := Finset.mem_image.mp hq
    rw [greedyParentFactorization_fiber_eq_block S P k]
    exact (blockAt S.activeCoarseFamily P k).fiber_nonempty
  obtain ⟨q, hq, hmass, hvolume, hproduct⟩ :=
    exists_cardWeighted_sourceFineLevelShading_actualAverage
      A hsource hfiber
  change q ∈ (indexFactorization S.activeCoarseFamily P).coarse at hq
  rw [indexFactorization_coarse, occurrenceIndices] at hq
  obtain ⟨k, _hk, hq⟩ := Finset.mem_image.mp hq
  subst q
  have hmass' :
      (IndexedShadingRefinement.restrictTo
          (parentAggregatedShading S D.shading)
          (greedyParentFactorization S P).index.fine).shading.shadingMass *
            ((blockAt S.activeCoarseFamily P k).fiber.card : ENNReal) ≤
        (loss : ENNReal) *
          (Fintype.card (ActiveParentIndex S) : ENNReal) *
            (sourceFineLevelShading A (some k)).shadingMass := by
    change _ *
        (((indexFactorization S.activeCoarseFamily P).fiber
          (some k)).card : ENNReal) ≤
      (loss : ENNReal) *
        (((indexFactorization S.activeCoarseFamily P).fine).card : ENNReal) * _
      at hmass
    rw [indexFactorization_fiber_eq_blockAt S.activeCoarseFamily P,
      indexFactorization_fine, Finset.card_univ] at hmass
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
    (affineJacobian (bucketNormalizedAffineEquiv e label) *
        (IndexedShadingRefinement.restrictTo
          (parentAggregatedShading S D.shading)
          (greedyParentFactorization S P).index.fine).shading.shadingMass) *
          (B.card : ENNReal) =
      affineJacobian (bucketNormalizedAffineEquiv e label) *
        ((IndexedShadingRefinement.restrictTo
          (parentAggregatedShading S D.shading)
          (greedyParentFactorization S P).index.fine).shading.shadingMass *
            (B.card : ENNReal)) := by ac_rfl
    _ ≤ affineJacobian (bucketNormalizedAffineEquiv e label) *
        (((loss : ENNReal) *
            (Fintype.card (ActiveParentIndex S) : ENNReal)) *
              (sourceFineLevelShading A (some k)).shadingMass) := by
      exact mul_le_mul' le_rfl hmass'
    _ = ((loss : ENNReal) *
          (Fintype.card (ActiveParentIndex S) : ENNReal)) *
        (affineJacobian (bucketNormalizedAffineEquiv e label) *
          (sourceFineLevelShading A (some k)).shadingMass) := by
      ac_rfl
    _ ≤ ((loss : ENNReal) *
          (Fintype.card (ActiveParentIndex S) : ENNReal)) *
        ((selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
          (selectedParentPlankBucketShading
            e S Ylevel B hrho label).shadingMass) := by
      exact mul_le_mul' le_rfl hbucket
    _ = ((loss : ENNReal) *
          (Fintype.card (ActiveParentIndex S) : ENNReal)) *
        (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
          (selectedParentPlankBucketShading
            e S Ylevel B hrho label).shadingMass := by ac_rfl

#print axioms
  exists_cardWeightedGreedyBlock_actualAverage_and_affinePlankBucket

end

end Family8SelectedParentCardWeightedFineLevelBucketV1
