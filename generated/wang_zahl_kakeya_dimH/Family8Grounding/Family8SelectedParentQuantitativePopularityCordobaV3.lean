import Family8Grounding.Family8QuantitativeCarrierPopularityRestrictionV3
import Family8Grounding.Family8SelectedParentCertifiedPlankCordobaActualJohnContainerV7

/-!
# Actual selected-parent Córdoba with quantitative popularity, V3

The carrier floor is produced by a literal half-average popularity
restriction.  Low-mass pieces cost a factor two, zero carriers are deleted,
and every remaining carrier obeys the explicit floor.  In the nonzero branch
that floor is exactly the bucket mass divided by twice its cardinality.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentQuantitativePopularityCordobaV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8CertifiedPlankDyadicCordobaV2
open Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
open Family8PositiveCarrierShadingRestrictionV4
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCertifiedPlankCordobaActualJohnContainerV7
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The actual thresholded Córdoba estimate after the automatic half-average
carrier popularity restriction. -/
theorem selectedParentPlankBucket_averageMultiplicity_le_quantitativePopularityJohn
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (Y : Shading fine.bodyFamily)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
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
    (KT : ENNReal) (hKT : IsKatzTao KT S.activeCoarseFamily) :
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let B := (blockAt S.activeCoarseFamily P k).fiber
    let Ybucket := selectedParentPlankBucketShading e S Y B hrho label
    let hplankPos : forall q,
        IsPlank 576 (bucketShortA label) (bucketShortB label)
          (quantitativePositiveCarrierFamily Ybucket q) := fun q =>
      selectedParentPlankBucket_isPlank e S B hrho label hplank q.1
    let cert := chosenPlankCertificate hplankPos
    Ybucket.averageMultiplicity <=
      2 * certifiedPlankDyadicFactor
        (certifiedPlankThresholdedLevels cert) KT
          (certifiedPlankThresholdedAngleScaleCap 576 *
            (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
              quantitativeCarrierFloor Ybucket)) := by
  dsimp only
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let Ybucket := selectedParentPlankBucketShading e S Y B hrho label
  let R := quantitativeCarrierRefinement Ybucket
  let Ypop := quantitativePositiveCarrierShading Ybucket
  let hplankBucket : forall q,
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label q) :=
    selectedParentPlankBucket_isPlank e S B hrho label hplank
  let hplankPos : forall q,
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (quantitativePositiveCarrierFamily Ybucket q) := fun q =>
    hplankBucket q.1
  let cert := chosenPlankCertificate hplankPos
  let K := selectedParentBucketNormalizedJohnContainer S hrho P k r label
  have hcontains : forall q,
      (quantitativePositiveCarrierFamily Ybucket q : Set Space) ⊆
        (K : Set Space) := by
    intro q
    change (selectedParentPlankBucketFamily e S B hrho label q.1 : Set Space) ⊆
      (selectedParentBucketNormalizedJohnContainer S hrho P k r label : Set Space)
    exact selectedParentPlankBucketFamily_subset_normalizedJohnContainer
      S hrho P k r hr label q.1
  have hKTbucket :
      IsKatzTao KT (selectedParentPlankBucketFamily e S B hrho label) :=
    selectedParentPlankBucket_isKatzTao e S B hrho label KT hKT
  have hKTpop : IsKatzTao KT (quantitativePositiveCarrierFamily Ybucket) := by
    exact isKatzTao_selectedCoarseFamily_of_isKatzTaoOn
      (hKTbucket.on (positiveCarrierIndices R.shading))
  have hresult := certifiedPlankThresholded_averageMultiplicity_le_globalContainer
    cert Ypop K hcontains (quantitativeCarrierFloor Ybucket)
      (quantitativeCarrierFloor_ne_zero Ybucket)
      (quantitativeCarrierFloor_ne_top Ybucket)
      (quantitativeCarrierFloor_le Ybucket) KT hKTpop
  rw [volume_selectedParentBucketNormalizedJohnContainer] at hresult
  have htransport :=
    averageMultiplicity_le_two_mul_quantitativePositiveCarrier Ybucket
  calc
    Ybucket.averageMultiplicity ≤ 2 * Ypop.averageMultiplicity := htransport
    _ ≤ 2 * certifiedPlankDyadicFactor
        (certifiedPlankThresholdedLevels cert) KT
          (certifiedPlankThresholdedAngleScaleCap 576 *
            (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
              quantitativeCarrierFloor Ybucket)) := by
      exact mul_le_mul le_rfl hresult bot_le bot_le

#print axioms
  selectedParentPlankBucket_averageMultiplicity_le_quantitativePopularityJohn

end

end Family8SelectedParentQuantitativePopularityCordobaV3
