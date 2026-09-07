import Family8Grounding.Family8SelectedParentExactAssemblyCordobaProductV2
import Family8Grounding.Family8SelectedParentExactAssemblyCordobaExpandedV5

/-!
# Actual selected-parent expanded Cordoba right-hand side, V6

This canonical successor applies V5's small monotonicity lemma to the literal
selected-parent bucket.  The resulting expression exposes the thresholded
angle-cardinality loss and preserves the actual popularity denominator
`bucketMass / (2 * bucketCard)` exactly.  Failed drafts V1--V4 are not
imported.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentExactAssemblyCordobaExpandedV6

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8CertifiedPlankDyadicCordobaV2
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentExactAssemblyCordobaExpandedV5
open Family8SelectedParentExactAssemblyCordobaProductV2
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
set_option maxHeartbeats 8000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The fully explicit inner Cordoba scalar attached to one actual selected
parent side bucket. -/
noncomputable def selectedParentFineLevelExpandedCordobaRHS
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss)
    (label : Fin 3 -> Int) (KT : ENNReal) : ENNReal :=
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let Ylevel := fineShadingAtGreedyBlockLevel
    S D.shading P k A.fineLevel
  let Ybucket := selectedParentPlankBucketShading e S Ylevel B hrho label
  (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
    (2 *
      (((certifiedPlankThresholdedAngleBucketLoss
        (bucketShortA label) (bucketShortB label) : Nat) : ENNReal) * KT *
        (certifiedPlankThresholdedAngleScaleCap 576 *
          (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
            (Ybucket.shadingMass /
              (((selectedParentPlankBucketIndices e S B hrho label).card :
                ENNReal) * 2))))))

/-- The finite angle-level factor in the actual endpoint is bounded by the
expanded scalar with the literal mass/cardinality denominator. -/
theorem selectedParentFineLevelExplicitCordobaRHS_le_expanded
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss)
    (label : Fin 3 -> Int)
    (hplank : forall p : {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber},
      p ∈ selectedParentPlankBucketIndices
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho label ->
        IsPlank 576 (bucketShortA label) (bucketShortB label)
          (selectedParentAffineFamily
            (bucketNormalizedAffineEquiv
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
              label)
            S (blockAt S.activeCoarseFamily P k).fiber p))
    (KT : ENNReal) :
    selectedParentFineLevelExplicitCordobaRHS
        D S hrho P k r hr A label hplank KT <=
      selectedParentFineLevelExpandedCordobaRHS
        D S hrho P k r hr A label KT := by
  dsimp only [selectedParentFineLevelExplicitCordobaRHS,
    selectedParentFineLevelExpandedCordobaRHS]
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let Ylevel := fineShadingAtGreedyBlockLevel
    S D.shading P k A.fineLevel
  let Ybucket := selectedParentPlankBucketShading e S Ylevel B hrho label
  let hplankPos : forall q,
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (quantitativePositiveCarrierFamily Ybucket q) := fun q =>
    selectedParentPlankBucket_isPlank e S B hrho label hplank q.1
  let cert := chosenPlankCertificate hplankPos
  exact loss_mul_two_mul_certifiedPlankDyadicFactor_le_explicit cert
    (selectedParentLogarithmicSideBucketLoss rho : ENNReal) KT
    (certifiedPlankThresholdedAngleScaleCap 576 *
      (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
        (Ybucket.shadingMass /
          (((selectedParentPlankBucketIndices e S B hrho label).card :
            ENNReal) * 2))))

#print axioms selectedParentFineLevelExplicitCordobaRHS_le_expanded

end

end Family8SelectedParentExactAssemblyCordobaExpandedV6
