import Family8Grounding.Family8PositiveCarrierShadingRestrictionV5
import Family8Grounding.Family8SelectedParentCertifiedPlankCordobaActualJohnContainerV7

/-!
# Actual selected-parent Córdoba after positive-carrier restriction, V2

Delete precisely the zero-volume shaded pieces from an actual V9 plank
bucket.  This changes neither mass, union volume, nor average multiplicity.
The remaining finite subtype has an automatic positive finite carrier floor,
while plank geometry, common John-container containment, and Katz--Tao
control pass by restriction.  No carrier-floor callback remains.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentPositiveCarrierCordobaV2

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
open Family8PositiveCarrierShadingRestrictionV5
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

/-- The actual John-container Córdoba estimate with the former `hfloor`
premise replaced by the canonical positive-carrier subtype and its computed
finite minimum. -/
theorem selectedParentPlankBucket_averageMultiplicity_le_thresholdedJohn_positiveCarrier
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
          (positiveCarrierFamily Ybucket q) := fun q =>
      selectedParentPlankBucket_isPlank e S B hrho label hplank q.1
    let cert := chosenPlankCertificate hplankPos
    Ybucket.averageMultiplicity <=
      certifiedPlankDyadicFactor (certifiedPlankThresholdedLevels cert) KT
        (certifiedPlankThresholdedAngleScaleCap 576 *
          (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
            automaticPositiveCarrierVolumeFloor Ybucket)) := by
  dsimp only
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let Ybucket := selectedParentPlankBucketShading e S Y B hrho label
  let Ypos := positiveCarrierShading Ybucket
  let hplankBucket : forall q,
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label q) :=
    selectedParentPlankBucket_isPlank e S B hrho label hplank
  let hplankPos : forall q,
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (positiveCarrierFamily Ybucket q) := fun q => hplankBucket q.1
  let cert := chosenPlankCertificate hplankPos
  let K := selectedParentBucketNormalizedJohnContainer S hrho P k r label
  let lower := automaticPositiveCarrierVolumeFloor Ybucket
  have hcontains : forall q,
      (positiveCarrierFamily Ybucket q : Set Space) ⊆ (K : Set Space) := by
    intro q
    change (selectedParentPlankBucketFamily e S B hrho label q.1 : Set Space) ⊆
      (selectedParentBucketNormalizedJohnContainer S hrho P k r label : Set Space)
    exact selectedParentPlankBucketFamily_subset_normalizedJohnContainer
      S hrho P k r hr label q.1
  have hKTbucket :
      IsKatzTao KT (selectedParentPlankBucketFamily e S B hrho label) :=
    selectedParentPlankBucket_isKatzTao e S B hrho label KT hKT
  have hKTpos : IsKatzTao KT (positiveCarrierFamily Ybucket) := by
    exact isKatzTao_selectedCoarseFamily_of_isKatzTaoOn
      (hKTbucket.on (positiveCarrierIndices Ybucket))
  have hresult := certifiedPlankThresholded_averageMultiplicity_le_globalContainer
    cert Ypos K hcontains lower
      (automaticPositiveCarrierVolumeFloor_ne_zero Ybucket)
      (automaticPositiveCarrierVolumeFloor_ne_top Ybucket)
      (automaticPositiveCarrierVolumeFloor_le Ybucket) KT hKTpos
  rw [volume_selectedParentBucketNormalizedJohnContainer] at hresult
  rw [positiveCarrierShading_averageMultiplicity Ybucket] at hresult
  simpa [e, B, Ybucket, Ypos, hplankBucket, hplankPos, cert, K, lower]
    using hresult

#print axioms
  selectedParentPlankBucket_averageMultiplicity_le_thresholdedJohn_positiveCarrier

end

end Family8SelectedParentPositiveCarrierCordobaV2
