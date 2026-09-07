import Family8Grounding.Family8SelectedParentArbitraryBlockQuantitativeCordobaV2

/-!
# Compact positive-carrier quantitative Cordoba for an arbitrary block

The arbitrary plank bucket may contain indices whose shaded carriers have
zero volume.  This wrapper first replaces that bucket by its literal
positive-carrier subtype.  Mass and actual average multiplicity are unchanged,
while the subsequent quantitative-popularity denominator counts only those
positive carriers.

The occurrence, side label, plank certificate, and normalized John container
are fixed throughout.  No additional density or side-label selection is made.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentArbitraryBlockPositiveCarrierQuantitativeCordobaV1

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
open Family8SelectedParentArbitraryBlockQuantitativeCordobaV2
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
set_option maxHeartbeats 4000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u

/-- On the compact positive-carrier subtype, the quantitative popularity
floor divides by the number of positive carriers, not by the ambient index
cardinality. -/
theorem quantitativeCarrierFloor_positiveCarrierShading_eq_mass_div_card_mul_two
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota} (Y : Shading F)
    (hmass : Y.shadingMass ≠ 0) :
    quantitativeCarrierFloor (positiveCarrierShading Y) =
      Y.shadingMass /
        ((Fintype.card {i // i ∈ positiveCarrierIndices Y} : ENNReal) * 2) := by
  let Yclean := positiveCarrierShading Y
  have hcleanMass : Yclean.shadingMass ≠ 0 := by
    rw [show Yclean.shadingMass = Y.shadingMass by
      exact positiveCarrierShading_shadingMass Y]
    exact hmass
  simpa only [Yclean, positiveCarrierShading_shadingMass] using
    (quantitativeCarrierFloor_eq_mass_div_card_mul_two Yclean hcleanMass)

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The compact side bucket injects into any declared local surviving set
that contains every positive carrier of the source block shading.  Thus its
cardinality is paid by the local surviving count, never by the ambient block
or occurrence count. -/
theorem selectedParentArbitraryPlankBucket_positiveCarrier_card_le_surviving
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 -> Int)
    (Z : Shading (selectedCoarseFamily S.activeCoarseFamily B))
    (surviving : Finset (ActiveParentIndex S))
    (hsupport : forall p : {p // p ∈ B},
      volume (Z.carrier p) ≠ 0 -> p.1 ∈ surviving) :
    Fintype.card
        {q // q ∈ positiveCarrierIndices
          (selectedParentArbitraryPlankBucketShading
            e S B hrho label Z)} ≤
      surviving.card := by
  let Yraw := selectedParentArbitraryPlankBucketShading
    e S B hrho label Z
  let toSurviving :
      {q // q ∈ positiveCarrierIndices Yraw} →
        {p // p ∈ surviving} := fun q => ⟨q.1.1.1, by
    apply hsupport q.1.1
    have hraw : volume (Yraw.carrier q.1) ≠ 0 :=
      (mem_positiveCarrierIndices Yraw q.1).1 q.2
    intro hzero
    apply hraw
    rw [selectedParentArbitraryPlankBucketShading_carrier,
      volume_image_affineEquiv, hzero, mul_zero]⟩
  have hinjective : Function.Injective toSurviving := by
    intro q₁ q₂ hq
    have hval : q₁.1.1.1 = q₂.1.1.1 := by
      simpa only [toSurviving] using
        congrArg (fun p : {p // p ∈ surviving} => p.1) hq
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact hval
  simpa only [Yraw, Fintype.card_coe] using
    (Fintype.card_le_of_injective toSurviving hinjective)

/-- Fixed-occurrence, fixed-label quantitative Cordoba after first deleting
all zero-volume carriers from the arbitrary normalized plank bucket.  The
first two conjuncts expose the exact mass and average identities used to
transport the final estimate back to the raw bucket. -/
theorem selectedParentArbitraryPlankBucket_positiveCarrier_averageMultiplicity_le
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
    let Yraw := selectedParentArbitraryPlankBucketShading
      e S B hrho label Z
    let Yclean := positiveCarrierShading Yraw
    let hplankPos : forall q,
        IsPlank 576 (bucketShortA label) (bucketShortB label)
          (quantitativePositiveCarrierFamily Yclean q) := fun q =>
      selectedParentPlankBucket_isPlank e S B hrho label hplank q.1.1
    let cert := chosenPlankCertificate hplankPos
    Yclean.shadingMass = Yraw.shadingMass /\
    Yclean.averageMultiplicity = Yraw.averageMultiplicity /\
    Yraw.averageMultiplicity <=
      2 * certifiedPlankDyadicFactor
        (certifiedPlankThresholdedLevels cert) KT
          (certifiedPlankThresholdedAngleScaleCap 576 *
            (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
              quantitativeCarrierFloor Yclean)) := by
  dsimp only
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let Yraw := selectedParentArbitraryPlankBucketShading
    e S B hrho label Z
  let Yclean := positiveCarrierShading Yraw
  let R := quantitativeCarrierRefinement Yclean
  let Ypop := quantitativePositiveCarrierShading Yclean
  let hplankBucket : forall q,
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label q) :=
    selectedParentPlankBucket_isPlank e S B hrho label hplank
  let hplankPos : forall q,
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (quantitativePositiveCarrierFamily Yclean q) := fun q =>
    hplankBucket q.1.1
  let cert := chosenPlankCertificate hplankPos
  let K := selectedParentBucketNormalizedJohnContainer S hrho P k r label
  have hcontains : forall q,
      (quantitativePositiveCarrierFamily Yclean q : Set Space) ⊆
        (K : Set Space) := by
    intro q
    change (selectedParentPlankBucketFamily e S B hrho label q.1.1 : Set Space) ⊆
      (selectedParentBucketNormalizedJohnContainer S hrho P k r label : Set Space)
    exact selectedParentPlankBucketFamily_subset_normalizedJohnContainer
      S hrho P k r hr label q.1.1
  have hKTbucket :
      IsKatzTao KT (selectedParentPlankBucketFamily e S B hrho label) :=
    selectedParentPlankBucket_isKatzTao e S B hrho label KT hKT
  have hKTclean : IsKatzTao KT (positiveCarrierFamily Yraw) := by
    exact isKatzTao_selectedCoarseFamily_of_isKatzTaoOn
      (hKTbucket.on (positiveCarrierIndices Yraw))
  have hKTpop : IsKatzTao KT (quantitativePositiveCarrierFamily Yclean) := by
    exact isKatzTao_selectedCoarseFamily_of_isKatzTaoOn
      (hKTclean.on (positiveCarrierIndices R.shading))
  have hresult :=
    certifiedPlankThresholded_averageMultiplicity_le_globalContainer
      cert Ypop K hcontains (quantitativeCarrierFloor Yclean)
        (quantitativeCarrierFloor_ne_zero Yclean)
        (quantitativeCarrierFloor_ne_top Yclean)
        (quantitativeCarrierFloor_le Yclean) KT hKTpop
  rw [volume_selectedParentBucketNormalizedJohnContainer] at hresult
  have htransport :=
    averageMultiplicity_le_two_mul_quantitativePositiveCarrier Yclean
  refine ⟨positiveCarrierShading_shadingMass Yraw,
    positiveCarrierShading_averageMultiplicity Yraw, ?_⟩
  calc
    Yraw.averageMultiplicity = Yclean.averageMultiplicity :=
      (positiveCarrierShading_averageMultiplicity Yraw).symm
    _ <= 2 * Ypop.averageMultiplicity := htransport
    _ <= 2 * certifiedPlankDyadicFactor
        (certifiedPlankThresholdedLevels cert) KT
          (certifiedPlankThresholdedAngleScaleCap 576 *
            (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
              quantitativeCarrierFloor Yclean)) := by
      exact mul_le_mul le_rfl hresult bot_le bot_le

/-- The weighted side selector followed by the compact fixed-label theorem.
The returned label is the selector's actual occupied label.  Its compact
bucket is nonzero, has at most the declared local surviving cardinality, and
uses its own positive-carrier quantitative floor in the Cordoba denominator.
-/
theorem exists_selectedParentArbitraryPlankBucket_positiveCarrier_quantitativeCordoba
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
    (hZmass : Z.shadingMass ≠ 0)
    (surviving : Finset (ActiveParentIndex S))
    (hsupport : forall p :
        {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber},
      volume (Z.carrier p) ≠ 0 -> p.1 ∈ surviving)
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
        let Yraw := selectedParentArbitraryPlankBucketShading
          e S B hrho label Z
        let Yclean := positiveCarrierShading Yraw
        let hplankPos : forall q,
            IsPlank 576 (bucketShortA label) (bucketShortB label)
              (quantitativePositiveCarrierFamily Yclean q) := fun q =>
          selectedParentPlankBucket_isPlank
            e S B hrho label hplank q.1.1
        let cert := chosenPlankCertificate hplankPos
        affineJacobian (bucketNormalizedAffineEquiv e label) * Z.shadingMass <=
            (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
              Yclean.shadingMass ∧
        Yclean.shadingMass = Yraw.shadingMass ∧
        Yclean.averageMultiplicity = Yraw.averageMultiplicity ∧
        Yclean.shadingMass ≠ 0 ∧
        (Fintype.card {q // q ∈ positiveCarrierIndices Yraw} : ENNReal) <=
          (surviving.card : ENNReal) ∧
        quantitativeCarrierFloor Yclean =
          Yraw.shadingMass /
            ((Fintype.card {q // q ∈ positiveCarrierIndices Yraw} : ENNReal) * 2) ∧
        Z.averageMultiplicity <=
          (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
            (2 * certifiedPlankDyadicFactor
              (certifiedPlankThresholdedLevels cert) KT
                (certifiedPlankThresholdedAngleScaleCap 576 *
                  (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
                    quantitativeCarrierFloor Yclean))) := by
  dsimp only
  obtain ⟨label, hoccupied, hretained, ha, hab, hb, hplank⟩ :=
    exists_selectedParentArbitraryPlankBucket_affineShadingMassRetention
      D hD S hrho hrhoOne P k r hr Z
  refine ⟨label, hoccupied, ha, hab, hb, hplank, ?_⟩
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let Yraw := selectedParentArbitraryPlankBucketShading
    e S B hrho label Z
  let Yclean := positiveCarrierShading Yraw
  let hplankPos : forall q,
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (quantitativePositiveCarrierFamily Yclean q) := fun q =>
    selectedParentPlankBucket_isPlank e S B hrho label hplank q.1.1
  let cert := chosenPlankCertificate hplankPos
  have hretainedRaw :
      affineJacobian (bucketNormalizedAffineEquiv e label) * Z.shadingMass <=
        (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
          Yraw.shadingMass := by
    simpa only [e, B, Yraw] using hretained
  have hrawMass : Yraw.shadingMass ≠ 0 := by
    intro hzero
    have hleft :
        affineJacobian (bucketNormalizedAffineEquiv e label) *
            Z.shadingMass ≠ 0 :=
      mul_ne_zero
        (affineJacobian_pos (bucketNormalizedAffineEquiv e label)).ne'
        hZmass
    apply hleft
    apply le_antisymm
    · exact hretainedRaw.trans_eq (by rw [hzero, mul_zero])
    · exact bot_le
  have hcleanMassEq : Yclean.shadingMass = Yraw.shadingMass :=
    positiveCarrierShading_shadingMass Yraw
  have hcleanAverageEq :
      Yclean.averageMultiplicity = Yraw.averageMultiplicity :=
    positiveCarrierShading_averageMultiplicity Yraw
  have hcleanMass : Yclean.shadingMass ≠ 0 := by
    rw [hcleanMassEq]
    exact hrawMass
  have hretainedClean :
      affineJacobian (bucketNormalizedAffineEquiv e label) * Z.shadingMass <=
        (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
          Yclean.shadingMass := by
    rw [hcleanMassEq]
    exact hretainedRaw
  have hcardNat :
      Fintype.card {q // q ∈ positiveCarrierIndices Yraw} <= surviving.card := by
    simpa only [e, B, Yraw] using
      selectedParentArbitraryPlankBucket_positiveCarrier_card_le_surviving
        e S B hrho label Z surviving hsupport
  have hcard :
      (Fintype.card {q // q ∈ positiveCarrierIndices Yraw} : ENNReal) <=
        (surviving.card : ENNReal) := by
    exact_mod_cast hcardNat
  have hfloor : quantitativeCarrierFloor Yclean =
      Yraw.shadingMass /
        ((Fintype.card {q // q ∈ positiveCarrierIndices Yraw} : ENNReal) * 2) := by
    simpa only [Yclean] using
      quantitativeCarrierFloor_positiveCarrierShading_eq_mass_div_card_mul_two
        Yraw hrawMass
  have hsourceToRaw : Z.averageMultiplicity <=
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
        Yraw.averageMultiplicity :=
    arbitraryBlockShading_averageMultiplicity_le_bucketLoss_mul
      e S B hrho label Z
        (selectedParentLogarithmicSideBucketLoss rho : ENNReal)
        hretainedRaw
  have hcompact :=
    selectedParentArbitraryPlankBucket_positiveCarrier_averageMultiplicity_le
      S hrho P k r hr label Z hplank KT hKT
  dsimp only at hcompact
  obtain ⟨_hcompactMass, _hcompactAverage, hrawCordoba⟩ := hcompact
  have hcordoba : Z.averageMultiplicity <=
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
        (2 * certifiedPlankDyadicFactor
          (certifiedPlankThresholdedLevels cert) KT
            (certifiedPlankThresholdedAngleScaleCap 576 *
              (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
                quantitativeCarrierFloor Yclean))) :=
    hsourceToRaw.trans (mul_le_mul' le_rfl hrawCordoba)
  exact ⟨hretainedClean, hcleanMassEq, hcleanAverageEq, hcleanMass,
    hcard, hfloor, hcordoba⟩

#print axioms
  quantitativeCarrierFloor_positiveCarrierShading_eq_mass_div_card_mul_two
#print axioms
  selectedParentArbitraryPlankBucket_positiveCarrier_averageMultiplicity_le
#print axioms
  selectedParentArbitraryPlankBucket_positiveCarrier_card_le_surviving
#print axioms
  exists_selectedParentArbitraryPlankBucket_positiveCarrier_quantitativeCordoba

end

end Family8SelectedParentArbitraryBlockPositiveCarrierQuantitativeCordobaV1
