import Family8Grounding.Family8SelectedParentArbitraryBlockPlankBucketV4
import Family8Grounding.Family8SelectedParentQuantitativePopularityCordobaV3

/-!
# Automatic quantitative Cordoba for an arbitrary selected-parent shading

This is the canonical successor to the failed V1 draft.  The plank
certificate in the final output is existentially bound, so the certified
factor depends honestly on the very geometry proof returned by the bucket
construction.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentArbitraryBlockQuantitativeCordobaV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8CertifiedPlankDyadicCordobaV2
open Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8PositiveCarrierShadingRestrictionV4
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentArbitraryBlockPlankBucketV4
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

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Every carrier of the arbitrary bucket is the literal affine image of the
corresponding source block carrier. -/
theorem selectedParentArbitraryPlankBucketShading_carrier
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 -> Int)
    (Z : Shading (selectedCoarseFamily S.activeCoarseFamily B))
    (q : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label}) :
    (selectedParentArbitraryPlankBucketShading
      e S B hrho label Z).carrier q =
      bucketNormalizedAffineEquiv e label '' Z.carrier q.1 := rfl

/-- A Jacobian-weighted mass-retention estimate transports to the actual
average multiplicity of the arbitrary source block. -/
theorem arbitraryBlockShading_averageMultiplicity_le_bucketLoss_mul
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 -> Int)
    (Z : Shading (selectedCoarseFamily S.activeCoarseFamily B))
    (bucketLoss : ENNReal)
    (hretained :
      affineJacobian (bucketNormalizedAffineEquiv e label) * Z.shadingMass <=
        bucketLoss *
          (selectedParentArbitraryPlankBucketShading
            e S B hrho label Z).shadingMass) :
    Z.averageMultiplicity <= bucketLoss *
      (selectedParentArbitraryPlankBucketShading
        e S B hrho label Z).averageMultiplicity := by
  let f := bucketNormalizedAffineEquiv e label
  let Ybucket := selectedParentArbitraryPlankBucketShading
    e S B hrho label Z
  have hunion : Ybucket.shadedUnion ⊆ f '' Z.shadedUnion := by
    intro x hx
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
    rw [selectedParentArbitraryPlankBucketShading_carrier] at hxq
    obtain ⟨y, hy, rfl⟩ := hxq
    exact ⟨y, Set.mem_iUnion.mpr ⟨q.1, hy⟩, rfl⟩
  have hvolume : volume Ybucket.shadedUnion <=
      affineJacobian f * volume Z.shadedUnion := by
    calc
      volume Ybucket.shadedUnion <= volume (f '' Z.shadedUnion) :=
        measure_mono hunion
      _ = affineJacobian f * volume Z.shadedUnion :=
        volume_image_affineEquiv f Z.shadedUnion
  have hJ0 : affineJacobian f ≠ 0 := (affineJacobian_pos f).ne'
  have hJtop : affineJacobian f ≠ ∞ := affineJacobian_ne_top f
  unfold Shading.averageMultiplicity
  change Z.shadingMass / volume Z.shadedUnion <=
    bucketLoss * (Ybucket.shadingMass / volume Ybucket.shadedUnion)
  calc
    Z.shadingMass / volume Z.shadedUnion =
        (affineJacobian f * Z.shadingMass) /
          (affineJacobian f * volume Z.shadedUnion) := by
      exact (ENNReal.mul_div_mul_left Z.shadingMass
        (volume Z.shadedUnion) hJ0 hJtop).symm
    _ <= (bucketLoss * Ybucket.shadingMass) /
          (affineJacobian f * volume Z.shadedUnion) :=
      ENNReal.div_le_div_right hretained _
    _ <= (bucketLoss * Ybucket.shadingMass) /
          volume Ybucket.shadedUnion :=
      ENNReal.div_le_div_left hvolume _
    _ = bucketLoss *
          (Ybucket.shadingMass / volume Ybucket.shadedUnion) := by
      simp only [div_eq_mul_inv]
      ac_rfl

/-- The thresholded-angle certified Córdoba theorem applies verbatim to the
arbitrary actual bucket, with automatic half-average carrier popularity and
the actual normalized John container. -/
theorem selectedParentArbitraryPlankBucket_averageMultiplicity_le_quantitativePopularityJohn
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
    (KT : ENNReal) (hKT : IsKatzTao KT S.activeCoarseFamily) :
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
    Ybucket.averageMultiplicity <= 2 * Ypop.averageMultiplicity := htransport
    _ <= 2 * certifiedPlankDyadicFactor
        (certifiedPlankThresholdedLevels cert) KT
          (certifiedPlankThresholdedAngleScaleCap 576 *
            (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
              quantitativeCarrierFloor Ybucket)) :=
      mul_le_mul le_rfl hresult bot_le bot_le

/-- Fully automatic selected-parent output for an arbitrary actual block
shading.  The certificate is existentially bound, rather than being recovered
from a preceding conjunction by proof search. -/
theorem exists_selectedParentArbitraryPlankBucket_averageMultiplicity_le
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
    (KT : ENNReal) (hKT : IsKatzTao KT S.activeCoarseFamily) :
    let B := (blockAt S.activeCoarseFamily P k).fiber
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let parent := {p // p ∈ B}
    let side : parent -> Fin 3 -> NNReal := fun p =>
      selectedParentLongRelabeledSide e S B hrho p
    exists label : Fin 3 -> Int,
      label ∈ occupiedWeightBuckets (Finset.univ : Finset parent)
        (fun p => sideShapeLabel (side p)) ∧
      0 < bucketShortA label ∧
      bucketShortA label <= bucketShortB label ∧
      bucketShortB label <= 1 ∧
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
    selectedParentArbitraryPlankBucket_averageMultiplicity_le_quantitativePopularityJohn
      S hrho P k r hr label Z hplank KT hKT
  dsimp only at hcordoba
  exact hsourceToBucket.trans (mul_le_mul' le_rfl hcordoba)

#print axioms selectedParentArbitraryPlankBucketShading_carrier
#print axioms arbitraryBlockShading_averageMultiplicity_le_bucketLoss_mul
#print axioms
  selectedParentArbitraryPlankBucket_averageMultiplicity_le_quantitativePopularityJohn
#print axioms exists_selectedParentArbitraryPlankBucket_averageMultiplicity_le

end

end Family8SelectedParentArbitraryBlockQuantitativeCordobaV2
