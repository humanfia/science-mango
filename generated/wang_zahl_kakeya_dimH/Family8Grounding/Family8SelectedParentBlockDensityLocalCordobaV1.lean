import Family8Grounding.Family8AmbientFamilyVolumeDensityV2
import Family8Grounding.Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
import Family8Grounding.Family8SelectedParentArbitraryBlockQuantitativeCordobaV2

/-!
# Local block-density Katz--Tao input for the selected-parent Cordoba endpoint

For one literal greedy occurrence block, the canonical ambient family-volume
density is exactly its existing `blockDensity`.  Thus the constant-one
Frostman certificate already carried by a high occurrence gives Katz--Tao on
that same block, with no global common-point estimate.

The Cordoba successors below transport only this local block certificate
through the already fixed affine map and side bucket.  They neither select a
new greedy block nor ask for Katz--Tao control of the full active-coarse
family.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentBlockDensityLocalCordobaV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family6AffineKatzTaoTransportV3
open Family8AmbientFamilyVolumeDensityV2
open Family8CertifiedPlankDyadicCordobaV2
open Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8PositiveCarrierShadingRestrictionV4
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentArbitraryBlockPlankBucketV4
open Family8SelectedParentArbitraryBlockQuantitativeCordobaV2
open Family8SelectedParentCertifiedPlankCordobaActualJohnContainerV7
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
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

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The family-volume density of the literal selected block is definitionally
the greedy block density after rewriting the selected-subtype sum. -/
theorem ambientFamilyVolumeDensity_selectedParentBlock_eq_blockDensity
    (S : StickyScaleCover fine rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length) :
    ambientFamilyVolumeDensity
        (selectedCoarseFamily S.activeCoarseFamily
          (blockAt S.activeCoarseFamily P k).fiber)
        (blockAt S.activeCoarseFamily P k).body =
      blockDensity S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P k) := by
  unfold ambientFamilyVolumeDensity blockDensity blockMass
  rw [selectedCoarseFamily_volume]

/-- Constant-one Frostman control on one actual occurrence block upgrades to
Katz--Tao with exactly that block's existing density.  Positivity of the
winning hull follows from one coarse tube in its nonempty greedy fibre. -/
theorem selectedParentBlock_isKatzTao_blockDensity_of_isFrostmanIn_one
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (hF : IsFrostmanIn 1
      (selectedCoarseFamily S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P k).fiber)
      (blockAt S.activeCoarseFamily P k).body) :
    IsKatzTao
      (blockDensity S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P k))
      (selectedCoarseFamily S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P k).fiber) := by
  have hvolume0 :
      volume ((blockAt S.activeCoarseFamily P k).body : Set Space) ≠ 0 := by
    obtain ⟨p, hp⟩ := (blockAt S.activeCoarseFamily P k).fiber_nonempty
    have hcontained := (blockAt S.activeCoarseFamily P k).contained p hp
    have hpVolume :
        0 < volume (S.activeCoarseFamily p : Set Space) := by
      change 0 < volume (S.coarse.tubes p.1).carrier
      exact (S.coarse.tubes p.1).volume_pos hrho
    exact (hpVolume.trans_le (measure_mono hcontained)).ne'
  have hvolumeTop :
      volume ((blockAt S.activeCoarseFamily P k).body : Set Space) ≠ ∞ :=
    (blockAt S.activeCoarseFamily P k).body.isCompact.measure_lt_top.ne
  have hKT := isKatzTao_of_isFrostmanIn_familyVolumeDensity
    hF hvolume0 hvolumeTop
  simpa only [one_mul,
    ambientFamilyVolumeDensity_selectedParentBlock_eq_blockDensity]
    using hKT

/-- Katz--Tao on the literal selected block survives the fixed bucket affine
normalization and the restriction to its literal side-shape bucket. -/
theorem selectedParentPlankBucket_isKatzTao_of_block
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 -> Int) (KT : ENNReal)
    (hKT : IsKatzTao KT
      (selectedCoarseFamily S.activeCoarseFamily B)) :
    IsKatzTao KT
      (selectedParentPlankBucketFamily e S B hrho label) := by
  have haffine : IsKatzTao KT
      (selectedParentAffineFamily
        (bucketNormalizedAffineEquiv e label) S B) := by
    exact isKatzTao_affineImageFamily
      (bucketNormalizedAffineEquiv e label)
      (selectedCoarseFamily S.activeCoarseFamily B) hKT
  exact isKatzTao_selectedCoarseFamily_of_isKatzTaoOn
    (haffine.on (selectedParentPlankBucketIndices e S B hrho label))

/-- Thresholded-angle Cordoba on the fixed bucket, requiring Katz--Tao only
on its originating greedy block. -/
theorem selectedParentArbitraryPlankBucket_averageMultiplicity_le_quantitativePopularityJohn_of_blockKT
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (Z : Shading (selectedCoarseFamily S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P k).fiber))
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
    (KT : ENNReal)
    (hKT : IsKatzTao KT
      (selectedCoarseFamily S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P k).fiber)) :
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let B := (blockAt S.activeCoarseFamily P k).fiber
    let Ybucket := selectedParentArbitraryPlankBucketShading
      e S B hrho label Z
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
  let Ybucket := selectedParentArbitraryPlankBucketShading
    e S B hrho label Z
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
      (selectedParentBucketNormalizedJohnContainer S hrho P k r label :
        Set Space)
    exact selectedParentPlankBucketFamily_subset_normalizedJohnContainer
      S hrho P k r hr label q.1
  have hKTbucket :
      IsKatzTao KT (selectedParentPlankBucketFamily e S B hrho label) :=
    selectedParentPlankBucket_isKatzTao_of_block
      e S B hrho label KT hKT
  have hKTpop : IsKatzTao KT
      (quantitativePositiveCarrierFamily Ybucket) := by
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
    Ybucket.averageMultiplicity <= 2 * Ypop.averageMultiplicity := htransport
    _ <= 2 * certifiedPlankDyadicFactor
        (certifiedPlankThresholdedLevels cert) KT
          (certifiedPlankThresholdedAngleScaleCap 576 *
            (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
              quantitativeCarrierFloor Ybucket)) :=
      mul_le_mul le_rfl hresult bot_le bot_le

/-- Fully automatic side-bucket successor using only Katz--Tao on the same
literal greedy block.  The block, its shading, and the chosen side bucket are
unchanged from the ordinary arbitrary-block endpoint. -/
theorem exists_selectedParentArbitraryPlankBucket_averageMultiplicity_le_of_blockKT
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r)
    (Z : Shading (selectedCoarseFamily S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P k).fiber))
    (KT : ENNReal)
    (hKT : IsKatzTao KT
      (selectedCoarseFamily S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P k).fiber)) :
    let B := (blockAt S.activeCoarseFamily P k).fiber
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let parent := {p // p ∈ B}
    let side : parent -> Fin 3 -> NNReal := fun p =>
      selectedParentLongRelabeledSide e S B hrho p
    exists label : Fin 3 -> Int,
      label ∈ occupiedWeightBuckets (Finset.univ : Finset parent)
        (fun p => sideShapeLabel (side p)) /\
      0 < bucketShortA label /\
      bucketShortA label <= bucketShortB label /\
      bucketShortB label <= 1 /\
      exists hplank : forall p,
          p ∈ sideShapeBucket Finset.univ side label ->
            IsPlank 576 (bucketShortA label) (bucketShortB label)
              (selectedParentAffineFamily
                (bucketNormalizedAffineEquiv e label) S B p),
        let Ybucket := selectedParentArbitraryPlankBucketShading
          e S B hrho label Z
        let hplankPos : forall q,
            IsPlank 576 (bucketShortA label) (bucketShortB label)
              (quantitativePositiveCarrierFamily Ybucket q) := fun q =>
          selectedParentPlankBucket_isPlank e S B hrho label hplank q.1
        let cert := chosenPlankCertificate hplankPos
        Z.averageMultiplicity <=
          (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
            (2 * certifiedPlankDyadicFactor
              (certifiedPlankThresholdedLevels cert) KT
                (certifiedPlankThresholdedAngleScaleCap 576 *
                  (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
                    quantitativeCarrierFloor Ybucket))) := by
  dsimp only
  have hbucket :=
    exists_selectedParentArbitraryPlankBucket_affineShadingMassRetention
      D hD S hrho hrhoOne P k r hr Z
  dsimp only at hbucket
  obtain ⟨label, hoccupied, hretained, ha, hab, hb, hplank⟩ := hbucket
  refine ⟨label, hoccupied, ha, hab, hb, hplank, ?_⟩
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let Ybucket := selectedParentArbitraryPlankBucketShading
    e S B hrho label Z
  have hsourceToBucket : Z.averageMultiplicity <=
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
        Ybucket.averageMultiplicity :=
    arbitraryBlockShading_averageMultiplicity_le_bucketLoss_mul
      e S B hrho label Z
        (selectedParentLogarithmicSideBucketLoss rho : ENNReal) hretained
  have hcordoba :=
    selectedParentArbitraryPlankBucket_averageMultiplicity_le_quantitativePopularityJohn_of_blockKT
      S hrho P k r hr label Z hplank KT hKT
  dsimp only at hcordoba
  exact hsourceToBucket.trans (mul_le_mul' le_rfl hcordoba)

#print axioms
  ambientFamilyVolumeDensity_selectedParentBlock_eq_blockDensity
#print axioms
  selectedParentBlock_isKatzTao_blockDensity_of_isFrostmanIn_one
#print axioms selectedParentPlankBucket_isKatzTao_of_block
#print axioms
  selectedParentArbitraryPlankBucket_averageMultiplicity_le_quantitativePopularityJohn_of_blockKT
#print axioms
  exists_selectedParentArbitraryPlankBucket_averageMultiplicity_le_of_blockKT

end
end Family8SelectedParentBlockDensityLocalCordobaV1
