import Family8Grounding.Family8SelectedParentFineLevelExplicitCordobaTransportV3

/-!
# Exact-assembly product with the actual selected-parent Cordoba fibre, V2

V1 reached only a final commutative multiplication mismatch.  This canonical
successor identifies the actual surviving occurrence and inserts its proved
selected-parent Cordoba bound into the literal actual-average product.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentExactAssemblyCordobaProductV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8CertifiedPlankDyadicCordobaV2
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentFineLevelExplicitCordobaTransportV3
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

/-- The literal selected-parent inner factor after side-bucket retention and
half-average carrier popularity. -/
noncomputable def selectedParentFineLevelExplicitCordobaRHS
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
    (hplank : ∀ p : {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber},
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
    (KT : ENNReal) : ENNReal :=
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let Ylevel := fineShadingAtGreedyBlockLevel
    S D.shading P k A.fineLevel
  let Ybucket := selectedParentPlankBucketShading e S Ylevel B hrho label
  let hplankPos : ∀ q,
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (quantitativePositiveCarrierFamily Ybucket q) := fun q =>
    selectedParentPlankBucket_isPlank e S B hrho label hplank q.1
  let cert := chosenPlankCertificate hplankPos
  (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
    (2 * certifiedPlankDyadicFactor
      (certifiedPlankThresholdedLevels cert) KT
        (certifiedPlankThresholdedAngleScaleCap 576 *
          (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
            (Ybucket.shadingMass /
              (((selectedParentPlankBucketIndices e S B hrho label).card :
                ENNReal) * 2)))))

/-- The actual-average product selects the same surviving greedy occurrence
to which the explicit selected-parent Cordoba endpoint applies. -/
theorem exists_survivingGreedyBlock_refinementAverage_le_outer_mul_explicitCordoba
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
        (greedyParentFactorization S P).index.fine).shading.shadingMass ≠ 0)
    (KT : ENNReal) (hKT : IsKatzTao KT S.activeCoarseFamily) :
    ∃ k : Fin (blocks S.activeCoarseFamily P).length,
      0 < volume (sourceFineLevelShading A (some k)).shadedUnion ∧
      ∃ label : Fin 3 -> Int,
        ∃ hplank : ∀ p : {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber},
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
                S (blockAt S.activeCoarseFamily P k).fiber p),
          label ∈ occupiedWeightBuckets
            (Finset.univ : Finset
              {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
            (fun p => sideShapeLabel
              (selectedParentLongRelabeledSide
                (contractedJohnAffineEquiv
                  (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
                S (blockAt S.activeCoarseFamily P k).fiber hrho p)) ∧
          0 < bucketShortA label ∧
          bucketShortA label ≤ bucketShortB label ∧
          bucketShortB label ≤ 1 ∧
          (sourceFineLevelShading A (some k)).averageMultiplicity ≤
            selectedParentFineLevelExplicitCordobaRHS
              D S hrho P k r hr A label hplank KT ∧
          A.refinement.shading.averageMultiplicity ≤
            ((greedyParentFactorization S P).inducedShading
              A.refinement.shading).averageMultiplicity *
              selectedParentFineLevelExplicitCordobaRHS
                D S hrho P k r hr A label hplank KT := by
  obtain ⟨q, hq, hvolume, hproduct⟩ :=
    refinement_averageMultiplicity_le_product_actualAverages A hsource
  change q ∈ (indexFactorization S.activeCoarseFamily P).coarse at hq
  rw [indexFactorization_coarse, occurrenceIndices] at hq
  obtain ⟨k, _hk, hq⟩ := Finset.mem_image.mp hq
  subst q
  obtain ⟨label, hplank, hoccupied, ha, hab, hb, hinner⟩ :=
    exists_selectedParentFineLevel_sourceAverage_le_explicitCordoba
      D hD S hrho hrhoOne P k r hr A KT hKT
  have hinner' :
      (sourceFineLevelShading A (some k)).averageMultiplicity ≤
        selectedParentFineLevelExplicitCordobaRHS
          D S hrho P k r hr A label hplank KT := by
    simpa only [selectedParentFineLevelExplicitCordobaRHS] using hinner
  refine ⟨k, hvolume, label, hplank, hoccupied, ha, hab, hb, hinner', ?_⟩
  apply hproduct.trans
  simpa only [mul_comm] using
    (mul_le_mul_left hinner'
      ((greedyParentFactorization S P).inducedShading
        A.refinement.shading).averageMultiplicity)

#print axioms
  exists_survivingGreedyBlock_refinementAverage_le_outer_mul_explicitCordoba

end

end Family8SelectedParentExactAssemblyCordobaProductV2
