import Family8Grounding.Family8SelectedParentFineLevelAverageTransportV3
import Family8Grounding.Family8SelectedParentQuantitativePopularityCordobaExplicitV5

/-!
# Actual fine-level average bounded by the explicit selected-parent Cordoba factor, V3

V1 had a namespace parsing error and V2 ended with the opposite commutative
multiplication orientation.  This canonical successor supplies the literal
source-fine average bound needed by the Proposition 6.6(A) product.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentFineLevelExplicitCordobaTransportV3

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
open Family8SelectedParentQuantitativePopularityCordobaExplicitV5
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

/-- One retained selected-parent plank bucket controls the actual source
fine-level average, with the popularity floor expanded into its literal
mass/cardinality formula. -/
theorem exists_selectedParentFineLevel_sourceAverage_le_explicitCordoba
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss)
    (KT : ENNReal) (hKT : IsKatzTao KT S.activeCoarseFamily) :
    let B := (blockAt S.activeCoarseFamily P k).fiber
    let Ylevel :=
      fineShadingAtGreedyBlockLevel S D.shading P k A.fineLevel
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let parent := {p // p ∈ B}
    let side : parent -> Fin 3 -> NNReal := fun p =>
      selectedParentLongRelabeledSide e S B hrho p
    ∃ label : Fin 3 -> Int,
      ∃ hplank : ∀ p : parent,
        p ∈ selectedParentPlankBucketIndices e S B hrho label ->
          IsPlank 576 (bucketShortA label) (bucketShortB label)
            (selectedParentAffineFamily
              (bucketNormalizedAffineEquiv e label) S B p),
        label ∈ occupiedWeightBuckets (Finset.univ : Finset parent)
          (fun p => sideShapeLabel (side p)) ∧
        0 < bucketShortA label ∧
        bucketShortA label ≤ bucketShortB label ∧
        bucketShortB label ≤ 1 ∧
        let Ybucket := selectedParentPlankBucketShading e S Ylevel B hrho label
        let hplankPos : ∀ q,
            IsPlank 576 (bucketShortA label) (bucketShortB label)
              (quantitativePositiveCarrierFamily Ybucket q) := fun q =>
          selectedParentPlankBucket_isPlank e S B hrho label hplank q.1
        let cert := chosenPlankCertificate hplankPos
        (sourceFineLevelShading A (some k)).averageMultiplicity ≤
          (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
            (2 * certifiedPlankDyadicFactor
              (certifiedPlankThresholdedLevels cert) KT
                (certifiedPlankThresholdedAngleScaleCap 576 *
                  (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
                    (Ybucket.shadingMass /
                      (((selectedParentPlankBucketIndices e S B hrho label).card :
                        ENNReal) * 2))))) := by
  dsimp only
  obtain ⟨label, hoccupied, hretained, ha, hab, hb, hplank⟩ :=
    exists_selectedParentFineLevelPlankBucket_affineShadingMassRetention
      D hD S hrho hrhoOne P k r hr A
  refine ⟨label, hplank, hoccupied, ha, hab, hb, ?_⟩
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
  have htransport :
      (sourceFineLevelShading A (some k)).averageMultiplicity ≤
        (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
          Ybucket.averageMultiplicity :=
    sourceFineLevelShading_averageMultiplicity_le_bucketLoss_mul
      D S P k A e hrho label
        (selectedParentLogarithmicSideBucketLoss rho : ENNReal) hretained
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
  apply htransport.trans
  simpa only [mul_comm] using
    (mul_le_mul_left hbucket
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal))

#print axioms
  exists_selectedParentFineLevel_sourceAverage_le_explicitCordoba

end

end Family8SelectedParentFineLevelExplicitCordobaTransportV3
