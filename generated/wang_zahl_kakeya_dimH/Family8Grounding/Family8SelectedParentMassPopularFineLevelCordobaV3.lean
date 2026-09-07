import Family8Grounding.Family8SelectedParentExactAssemblyCordobaProductV2
import Family8Grounding.Family8SelectedParentMassPopularFineLevelBucketV2
import Family8Grounding.Family8SelectedParentExactAssemblyProp66AConnectorV3

/-!
# The same mass-popular fibre supplies the actual Córdoba factor

First select the quantitative mass-popular greedy occurrence.  On that fixed
occurrence, run the actual side-bucket producer once and retain all of its
outputs: fine-level mass retention, the actual plank certificate, and the
thresholded Córdoba estimate.  Thus the bucket used to bound the fine actual
average is literally the bucket whose mass is controlled by the source.

This removes the possible mismatch between a popularity-selected occurrence,
an arbitrary positive occurrence in the actual-average product, and a second
existentially selected side bucket.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentMassPopularFineLevelCordobaV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8CertifiedPlankDyadicCordobaV2
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentExactAssemblyCordobaProductV2
open Family8SelectedParentExactAssemblyProp66AConnectorV3
open Family8SelectedParentFineLevelAverageTransportV3
open Family8SelectedParentFineLevelBucketRetentionV5
open Family8SelectedParentFineLevelLiftV2
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentMassPopularFineLevelBucketV2
open Family8SelectedParentQuantitativePopularityCordobaExplicitV5
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- One mass-popular occurrence and one literal bucket simultaneously give
source-to-bucket mass retention, the actual-average product, and the named
logarithmic Córdoba bound for the fine factor. -/
theorem exists_massPopularGreedyBlock_sourceAverage_le_logarithmicCordoba
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
      ∃ label : Fin 3 → Int,
        ∃ _hplank : ∀ p :
            {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber},
          p ∈ selectedParentPlankBucketIndices
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
              S (blockAt S.activeCoarseFamily P k).fiber hrho label →
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
          affineJacobian
              (bucketNormalizedAffineEquiv
                (contractedJohnAffineEquiv
                  (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
                label) *
              (sourceFineLevelShading A (some k)).shadingMass ≤
            (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
              (selectedParentPlankBucketShading
                (contractedJohnAffineEquiv
                  (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
                S (fineShadingAtGreedyBlockLevel
                  S D.shading P k A.fineLevel)
                (blockAt S.activeCoarseFamily P k).fiber hrho label).shadingMass ∧
          affineJacobian
              (bucketNormalizedAffineEquiv
                (contractedJohnAffineEquiv
                  (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
                label) *
              (IndexedShadingRefinement.restrictTo
                (parentAggregatedShading S D.shading)
                (greedyParentFactorization S P).index.fine).shading.shadingMass ≤
            ((loss : ENNReal) * (P.length : ENNReal)) *
              (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
                (selectedParentPlankBucketShading
                  (contractedJohnAffineEquiv
                    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
                  S (fineShadingAtGreedyBlockLevel
                    S D.shading P k A.fineLevel)
                  (blockAt S.activeCoarseFamily P k).fiber hrho label).shadingMass ∧
          0 < bucketShortA label ∧
          bucketShortA label ≤ bucketShortB label ∧
          bucketShortB label ≤ 1 ∧
          (sourceFineLevelShading A (some k)).averageMultiplicity ≤
            selectedParentFineLevelLogarithmicCordobaRHS
              D S hrho P k r hr A label KT := by
  obtain ⟨k, hmass, hvolume, hproduct, _label0, _hoccupied0,
      _hglobal0, _ha0, _hab0, _hb0, _hplank0⟩ :=
    exists_massPopularGreedyBlock_actualAverage_and_affinePlankBucket
      D hD S hrho hrhoOne P r hr A hsource
  obtain ⟨label, hoccupied, hretained, ha, hab, hb, hplank⟩ :=
    exists_selectedParentFineLevelPlankBucket_affineShadingMassRetention
      D hD S hrho hrhoOne P k r hr A
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let Ylevel := fineShadingAtGreedyBlockLevel
    S D.shading P k A.fineLevel
  let Ybucket := selectedParentPlankBucketShading e S Ylevel B hrho label
  have hglobal :
      affineJacobian (bucketNormalizedAffineEquiv e label) *
          (IndexedShadingRefinement.restrictTo
            (parentAggregatedShading S D.shading)
            (greedyParentFactorization S P).index.fine).shading.shadingMass ≤
        ((loss : ENNReal) * (P.length : ENNReal)) *
          (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
            Ybucket.shadingMass := by
    calc
      affineJacobian (bucketNormalizedAffineEquiv e label) *
          (IndexedShadingRefinement.restrictTo
            (parentAggregatedShading S D.shading)
            (greedyParentFactorization S P).index.fine).shading.shadingMass ≤
        affineJacobian (bucketNormalizedAffineEquiv e label) *
          (((loss : ENNReal) * (P.length : ENNReal)) *
            (sourceFineLevelShading A (some k)).shadingMass) :=
        mul_le_mul' le_rfl hmass
      _ = ((loss : ENNReal) * (P.length : ENNReal)) *
          (affineJacobian (bucketNormalizedAffineEquiv e label) *
            (sourceFineLevelShading A (some k)).shadingMass) := by
        ac_rfl
      _ ≤ ((loss : ENNReal) * (P.length : ENNReal)) *
          ((selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
            Ybucket.shadingMass) :=
        mul_le_mul' le_rfl hretained
      _ = ((loss : ENNReal) * (P.length : ENNReal)) *
          (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
            Ybucket.shadingMass := by ac_rfl
  have htransport :
      (sourceFineLevelShading A (some k)).averageMultiplicity ≤
        (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
          Ybucket.averageMultiplicity :=
    sourceFineLevelShading_averageMultiplicity_le_bucketLoss_mul
      D S P k A e hrho label
        (selectedParentLogarithmicSideBucketLoss rho : ENNReal) hretained
  let hplankPos : ∀ q,
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (quantitativePositiveCarrierFamily Ybucket q) := fun q =>
    selectedParentPlankBucket_isPlank e S B hrho label hplank q.1
  let cert := chosenPlankCertificate hplankPos
  have hcases :=
    selectedParentPlankBucket_averageMultiplicity_eq_zero_or_le_explicit
      S hrho Ylevel P k r hr label hplank KT hKT
  dsimp only at hcases
  have hbucket : Ybucket.averageMultiplicity ≤
      2 * certifiedPlankDyadicFactor
        (certifiedPlankThresholdedLevels cert) KT
          (certifiedPlankThresholdedAngleScaleCap 576 *
            (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
              (Ybucket.shadingMass /
                (((selectedParentPlankBucketIndices e S B hrho label).card :
                  ENNReal) * 2)))) := by
    rcases hcases with hzero | hle
    · rw [hzero]
      exact bot_le
    · exact hle
  have hfineExplicit :
      (sourceFineLevelShading A (some k)).averageMultiplicity ≤
        selectedParentFineLevelExplicitCordobaRHS
          D S hrho P k r hr A label hplank KT := by
    apply htransport.trans
    simpa only [selectedParentFineLevelExplicitCordobaRHS, mul_comm] using
      (mul_le_mul_left hbucket
        (selectedParentLogarithmicSideBucketLoss rho : ENNReal))
  have hfineLog := hfineExplicit.trans
    (selectedParentFineLevelExplicitCordobaRHS_le_namedLogarithmic
      D hD S hrho hrhoOne P k r hr A label hplank hoccupied KT)
  refine ⟨k, hmass, hvolume, hproduct, label, hplank, hoccupied,
    hretained, ?_, ha, hab, hb, hfineLog⟩
  simpa only [e, B, Ylevel, Ybucket] using hglobal

#print axioms
  exists_massPopularGreedyBlock_sourceAverage_le_logarithmicCordoba

end

end Family8SelectedParentMassPopularFineLevelCordobaV3
