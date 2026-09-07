import Family8Grounding.Family8SelectedParentAngleBucketLogarithmicLossV2
import Family8Grounding.Family8SelectedParentCombinedLogLossPowerAbsorptionV3
import Family8Grounding.Family8GreedyHighPrefixSameOccurrenceOccupiedCardV1
import Family8Grounding.Family8TauActiveParentGreedyLowFreshOrSameOccurrenceWeightedCordobaSourceAverageV1
import Mathlib.Tactic

/-!
# Same-occurrence Cordoba scalar envelope at the tau parent scale

This module changes no selected object.  It expands the proof-dependent
certified Córdoba factor for the already selected block shading, then bounds
its actual thresholded angle count by the existing logarithmic ratio loss.
The only geometric adaptation is that tau-active coarse support replaces the
older, stronger support hypothesis on every fine tube.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8TauActiveParentSameOccurrenceWeightedCordobaScalarEnvelopeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8CertifiedPlankDyadicCordobaV2
open Family8FullRefinementActualDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8GreedyHighPrefixActualOccurrenceV1
open Family8GreedyHighPrefixSameOccurrenceOccupiedCardV1
open Family8GreedyHighPrefixSameOccurrenceWeightedMassV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCrossingSourceTauShadingV2
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8PositiveCarrierShadingRestrictionV4
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentAngleBucketLogarithmicLossV2
open Family8SelectedParentArbitraryBlockPlankBucketV4
open Family8SelectedParentArbitraryBlockQuantitativeCordobaV2
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentCombinedLogLossPowerAbsorptionV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankQuantitativeLossV10
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8ScaleContainedB2NativeFreshKatzTaoEndpointV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8TauActiveParentGreedyLowFreshOrSameOccurrenceWeightedCordobaV1
open Family8TauActiveParentGreedyLowFreshOrSameOccurrenceWeightedCordobaSourceAverageV1
open Family8TauActiveParentGreedyLowFreshOrActualHighOccurrenceV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The actual short-side aspect ratio is controlled from active-coarse
support alone. -/
theorem bucketShortB_div_bucketShortA_le_selectedParentRatio_of_activeCoarse_contained
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hcoarseContained : forall p : ActiveParentIndex S,
      (S.activeCoarseFamily p : Set Space) ⊆
        Metric.closedBall (0 : Space) 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (hoccupied : label ∈ occupiedWeightBuckets
      (Finset.univ : Finset
        {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
      (fun p => sideShapeLabel
        (selectedParentLongRelabeledSide
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho p))) :
    (((bucketShortB label / bucketShortA label : NNReal) : Real)) <=
      11943936 / (rho : Real) := by
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let side : {p // p ∈ B} -> Fin 3 -> NNReal := fun p =>
    selectedParentLongRelabeledSide e S B hrho p
  rcases mem_occupiedWeightBuckets_iff.mp hoccupied with
    ⟨p, _hp, hpLabel⟩
  have hpos : forall i, 0 < side p i := by
    intro i
    exact selectedParentLongRelabeledSide_pos e S B hrho p i
  have hband0 := sideShapeUpper_half_lt_and_le hpos (0 : Fin 3)
  have hband1 := sideShapeUpper_half_lt_and_le hpos (1 : Fin 3)
  change sideShapeLabel (side p) = label at hpLabel
  rw [hpLabel] at hband0 hband1
  have hfloor0 : selectedParentSideFloor rho r <= side p 0 := by
    exact selectedParentContractedLongRelabeledSide_floor_of_activeCoarse_contained
      S hrho hcoarseContained P k r hr p 0
  have hfloor1 : selectedParentSideFloor rho r <= side p 1 := by
    exact selectedParentContractedLongRelabeledSide_floor_of_activeCoarse_contained
      S hrho hcoarseContained P k r hr p 1
  have hside0Upper : side p 0 <= 1728 * r := by
    exact selectedParentContractedLongRelabeledSide_le
      S hrho P k r hr p 0
  have hside1Upper : side p 1 <= 1728 * r := by
    exact selectedParentContractedLongRelabeledSide_le
      S hrho P k r hr p 1
  have hU0Lower : selectedParentSideFloor rho r <=
      sideShapeUpper label 0 := hfloor0.trans hband0.2
  have hU1Lower : selectedParentSideFloor rho r <=
      sideShapeUpper label 1 := hfloor1.trans hband1.2
  have hU0Upper : sideShapeUpper label 0 <= 3456 * r := by
    apply le_of_lt
    nlinarith [hband0.1, hside0Upper]
  have hU1Upper : sideShapeUpper label 1 <= 3456 * r := by
    apply le_of_lt
    nlinarith [hband1.1, hside1Upper]
  have hU0Pos : (0 : Real) < (sideShapeUpper label 0 : Real) := by
    exact_mod_cast sideShapeUpper_pos label 0
  have hU1Pos : (0 : Real) < (sideShapeUpper label 1 : Real) := by
    exact_mod_cast sideShapeUpper_pos label 1
  have hU2Pos : (0 : Real) < (sideShapeUpper label 2 : Real) := by
    exact_mod_cast sideShapeUpper_pos label 2
  have hfloorPos : (0 : Real) <
      (selectedParentSideFloor rho r : Real) := by
    exact_mod_cast selectedParentSideFloor_pos hrho hr
  have hU0LowerReal : (selectedParentSideFloor rho r : Real) <=
      (sideShapeUpper label 0 : Real) := by exact_mod_cast hU0Lower
  have hU1LowerReal : (selectedParentSideFloor rho r : Real) <=
      (sideShapeUpper label 1 : Real) := by exact_mod_cast hU1Lower
  have hU0UpperReal : (sideShapeUpper label 0 : Real) <=
      ((3456 * r : NNReal) : Real) := by exact_mod_cast hU0Upper
  have hU1UpperReal : (sideShapeUpper label 1 : Real) <=
      ((3456 * r : NNReal) : Real) := by exact_mod_cast hU1Upper
  have hscale :
      (((3456 * r : NNReal) : Real) /
          (selectedParentSideFloor rho r : Real)) =
        11943936 / (rho : Real) := by
    unfold selectedParentSideFloor
    norm_num [NNReal.coe_div, NNReal.coe_mul]
    field_simp [show (r : Real) ≠ 0 by exact_mod_cast hr.ne',
      show (rho : Real) ≠ 0 by exact_mod_cast hrho.ne']
    ring
  by_cases h01 : sideShapeUpper label 0 <= sideShapeUpper label 1
  · simp only [bucketShortA, bucketShortB, if_pos h01, NNReal.coe_div]
    have hcancel :
        (((sideShapeUpper label 1 : Real) /
            (sideShapeUpper label 2 : Real)) /
          ((sideShapeUpper label 0 : Real) /
            (sideShapeUpper label 2 : Real))) =
          (sideShapeUpper label 1 : Real) /
            (sideShapeUpper label 0 : Real) := by
      field_simp [hU0Pos.ne', hU2Pos.ne']
    rw [hcancel, ← hscale]
    exact div_le_div₀ (by positivity) hU1UpperReal hfloorPos hU0LowerReal
  · simp only [bucketShortA, bucketShortB, if_neg h01, NNReal.coe_div]
    have hcancel :
        (((sideShapeUpper label 0 : Real) /
            (sideShapeUpper label 2 : Real)) /
          ((sideShapeUpper label 1 : Real) /
            (sideShapeUpper label 2 : Real))) =
          (sideShapeUpper label 0 : Real) /
            (sideShapeUpper label 1 : Real) := by
      field_simp [hU1Pos.ne', hU2Pos.ne']
    rw [hcancel, ← hscale]
    exact div_le_div₀ (by positivity) hU0UpperReal hfloorPos hU1LowerReal

/-- The actual angle-label loss is logarithmic under the same exact
active-coarse geometry used by the tau connector. -/
theorem selectedParent_angleBucketLoss_le_logarithmic_of_activeCoarse_contained
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hcoarseContained : forall p : ActiveParentIndex S,
      (S.activeCoarseFamily p : Set Space) ⊆
        Metric.closedBall (0 : Space) 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (hoccupied : label ∈ occupiedWeightBuckets
      (Finset.univ : Finset
        {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
      (fun p => sideShapeLabel
        (selectedParentLongRelabeledSide
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho p))) :
    certifiedPlankThresholdedAngleBucketLoss
        (bucketShortA label) (bucketShortB label) <=
      2 * threeSideDyadicRatioLoss (11943936 / (rho : Real)) := by
  apply certifiedPlankThresholdedAngleBucketLoss_le_two_mul_ratioLoss
    (bucketShortA_pos label) (bucketShortA_le_bucketShortB label)
  exact
    bucketShortB_div_bucketShortA_le_selectedParentRatio_of_activeCoarse_contained
      S hrho hcoarseContained P k r hr label hoccupied

/-- Pure monotone scalar expansion for an already selected literal block and
shading.  It preserves the caller's exact first-hit and occupied-q factors. -/
theorem sourceAverage_le_logarithmicSameBlockCordobaEnvelope
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hcoarseContained : forall p : ActiveParentIndex S,
      (S.activeCoarseFamily p : Set Space) ⊆
        Metric.closedBall (0 : Space) 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r)
    (Z : Shading (selectedCoarseFamily S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P k).fiber))
    (label : Fin 3 -> Int)
    (hoccupied : label ∈ occupiedWeightBuckets
      (Finset.univ : Finset
        {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
      (fun p => sideShapeLabel
        (selectedParentLongRelabeledSide
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho p)))
    (hplank : forall p,
      p ∈ sideShapeBucket Finset.univ
        (fun p => selectedParentLongRelabeledSide
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho p) label ->
        IsPlank 576 (bucketShortA label) (bucketShortB label)
          (selectedParentAffineFamily
            (bucketNormalizedAffineEquiv
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
              label)
            S (blockAt S.activeCoarseFamily P k).fiber p))
    (sourceAverage firstFactor qFactor KT : ENNReal) :
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let B := (blockAt S.activeCoarseFamily P k).fiber
    let Ybucket := selectedParentArbitraryPlankBucketShading
      e S B hrho label Z
    let hplankPos : forall t,
        IsPlank 576 (bucketShortA label) (bucketShortB label)
          (quantitativePositiveCarrierFamily Ybucket t) := fun t =>
      selectedParentPlankBucket_isPlank e S B hrho label hplank t.1
    let cert := chosenPlankCertificate hplankPos
    sourceAverage <=
      firstFactor *
        (qFactor *
          ((selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
            (2 * certifiedPlankDyadicFactor
              (certifiedPlankThresholdedLevels cert) KT
                (certifiedPlankThresholdedAngleScaleCap 576 *
                  (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
                    quantitativeCarrierFloor Ybucket))))) ->
    sourceAverage <=
      firstFactor *
        (qFactor *
          ((selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
            (2 *
              ((((2 * threeSideDyadicRatioLoss
                (11943936 / (rho : Real)) : Nat) : ENNReal) * KT) *
                (certifiedPlankThresholdedAngleScaleCap 576 *
                  (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
                    quantitativeCarrierFloor Ybucket)))))) := by
  dsimp only
  intro hsource
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let Ybucket := selectedParentArbitraryPlankBucketShading
    e S B hrho label Z
  let hplankPos : forall t,
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (quantitativePositiveCarrierFamily Ybucket t) := fun t =>
    selectedParentPlankBucket_isPlank e S B hrho label hplank t.1
  let cert := chosenPlankCertificate hplankPos
  let scale := certifiedPlankThresholdedAngleScaleCap 576 *
    (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
      quantitativeCarrierFloor Ybucket)
  have hcert : certifiedPlankDyadicFactor
      (certifiedPlankThresholdedLevels cert) KT scale <=
        (certifiedPlankThresholdedAngleBucketLoss
          (bucketShortA label) (bucketShortB label) : ENNReal) * KT * scale :=
    certifiedPlankDyadicFactor_thresholded_le_explicit cert KT scale
  have hangleNat :=
    selectedParent_angleBucketLoss_le_logarithmic_of_activeCoarse_contained
      S hrho hcoarseContained P k r hr label hoccupied
  have hangle :
      (certifiedPlankThresholdedAngleBucketLoss
        (bucketShortA label) (bucketShortB label) : ENNReal) <=
        ((2 * threeSideDyadicRatioLoss
          (11943936 / (rho : Real)) : Nat) : ENNReal) := by
    exact_mod_cast hangleNat
  have hfactor : certifiedPlankDyadicFactor
      (certifiedPlankThresholdedLevels cert) KT scale <=
        (((2 * threeSideDyadicRatioLoss
          (11943936 / (rho : Real)) : Nat) : ENNReal) * KT) * scale := by
    exact hcert.trans (mul_le_mul' (mul_le_mul' hangle le_rfl) le_rfl)
  exact hsource.trans
    (mul_le_mul' le_rfl
      (mul_le_mul' le_rfl
        (mul_le_mul' le_rfl (mul_le_mul' le_rfl hfactor))))

/-- The two literal selected-parent logarithms are absorbed without changing
the already chosen block, shading, or side label.  The first-hit and
occupied-occurrence-label factors remain completely explicit. -/
theorem sourceAverage_le_sameBlockCordoba_logAbsorbed
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (hcoarseContained : forall p : ActiveParentIndex S,
      (S.activeCoarseFamily p : Set Space) ⊆
        Metric.closedBall (0 : Space) 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r)
    (Z : Shading (selectedCoarseFamily S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P k).fiber))
    (label : Fin 3 -> Int)
    (hoccupied : label ∈ occupiedWeightBuckets
      (Finset.univ : Finset
        {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
      (fun p => sideShapeLabel
        (selectedParentLongRelabeledSide
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho p)))
    (hplank : forall p,
      p ∈ sideShapeBucket Finset.univ
        (fun p => selectedParentLongRelabeledSide
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho p) label ->
        IsPlank 576 (bucketShortA label) (bucketShortB label)
          (selectedParentAffineFamily
            (bucketNormalizedAffineEquiv
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
              label)
            S (blockAt S.activeCoarseFamily P k).fiber p))
    (sourceAverage firstFactor qFactor KT : ENNReal)
    {lossEta : Real} (hlossEta : 0 < lossEta)
    (hsideThreshold :
      rho <= selectedParentLogarithmicSideBucketAbsorptionThreshold
        1 (lossEta / 2))
    (hangleThreshold :
      rho / 2 <= selectedParentLogarithmicSideBucketAbsorptionThreshold
        4 (lossEta / 4)) :
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let B := (blockAt S.activeCoarseFamily P k).fiber
    let Ybucket := selectedParentArbitraryPlankBucketShading
      e S B hrho label Z
    let hplankPos : forall t,
        IsPlank 576 (bucketShortA label) (bucketShortB label)
          (quantitativePositiveCarrierFamily Ybucket t) := fun t =>
      selectedParentPlankBucket_isPlank e S B hrho label hplank t.1
    let cert := chosenPlankCertificate hplankPos
    sourceAverage <=
      firstFactor *
        (qFactor *
          ((selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
            (2 * certifiedPlankDyadicFactor
              (certifiedPlankThresholdedLevels cert) KT
                (certifiedPlankThresholdedAngleScaleCap 576 *
                  (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
                    quantitativeCarrierFloor Ybucket))))) ->
    sourceAverage <=
      firstFactor *
        (qFactor *
          ((rho : ENNReal) ^ (-lossEta) *
            (KT *
              (certifiedPlankThresholdedAngleScaleCap 576 *
                (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
                  quantitativeCarrierFloor Ybucket))))) := by
  dsimp only
  intro hsource
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let Ybucket := selectedParentArbitraryPlankBucketShading
    e S B hrho label Z
  let hplankPos : forall t,
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (quantitativePositiveCarrierFamily Ybucket t) := fun t =>
    selectedParentPlankBucket_isPlank e S B hrho label hplank t.1
  let cert := chosenPlankCertificate hplankPos
  let scale : ENNReal := certifiedPlankThresholdedAngleScaleCap 576 *
    (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
      quantitativeCarrierFloor Ybucket)
  have henv := sourceAverage_le_logarithmicSameBlockCordobaEnvelope
    S hrho hcoarseContained P k r hr Z label hoccupied hplank
      sourceAverage firstFactor qFactor KT hsource
  let angleLoss : ENNReal :=
    (threeSideDyadicRatioLoss (11943936 / (rho : Real)) : Nat)
  have hlogs :
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
          (4 * angleLoss) <= (rho : ENNReal) ^ (-lossEta) := by
    exact fixedConstant_mul_combinedSelectedParentLogLoss_le_rpow
      (rho := rho) (fixedConstant := 4) (lossEta := lossEta)
        (by norm_num) hlossEta hrho hrhoHalf hsideThreshold hangleThreshold
  have hscalar :
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
          (2 * ((((2 * threeSideDyadicRatioLoss
            (11943936 / (rho : Real)) : Nat) : ENNReal) * KT) * scale)) <=
        (rho : ENNReal) ^ (-lossEta) * (KT * scale) := by
    have hrewrite :
        (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
            (2 * ((((2 * threeSideDyadicRatioLoss
              (11943936 / (rho : Real)) : Nat) : ENNReal) * KT) * scale)) =
          ((selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
            (4 * angleLoss)) * (KT * scale) := by
      dsimp only [angleLoss]
      norm_num [Nat.cast_mul]
      ring
    rw [hrewrite]
    exact mul_le_mul' hlogs le_rfl
  exact henv.trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl hscalar))

/-- A division-free nonvanishing consequence of any literal mass-retention
inequality. -/
theorem bucket_ne_zero_of_nonzero_source_and_retention
    {jacobian source loss bucket : ENNReal}
    (hjacobian : jacobian ≠ 0) (hsource : source ≠ 0)
    (hretained : jacobian * source <= loss * bucket) :
    bucket ≠ 0 := by
  intro hzero
  rw [hzero, mul_zero] at hretained
  exact (mul_ne_zero hjacobian hsource) (bot_unique hretained)

/-- Active-coarse arbitrary-block endpoint retaining both the literal affine
mass payment and the Córdoba average bound for the same chosen side bucket.
This is the information needed to cancel `quantitativeCarrierFloor` later. -/
theorem exists_selectedParentArbitraryPlankBucket_massRetention_and_averageMultiplicity_le_of_activeCoarse_contained
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hcoarseContained : forall p : ActiveParentIndex S,
      (S.activeCoarseFamily p : Set Space) ⊆
        Metric.closedBall (0 : Space) 1)
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
        affineJacobian (bucketNormalizedAffineEquiv e label) * Z.shadingMass <=
            (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
              Ybucket.shadingMass /\
          Z.averageMultiplicity <=
            (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
              (2 * certifiedPlankDyadicFactor
                (certifiedPlankThresholdedLevels cert) KT
                  (certifiedPlankThresholdedAngleScaleCap 576 *
                    (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
                      quantitativeCarrierFloor Ybucket))) := by
  dsimp only
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let weight : {p // p ∈ B} -> Real := fun p => shadingPieceRealWeight Z p
  have hweightNonneg : forall p, 0 <= weight p := by
    intro p
    dsimp only [weight, shadingPieceRealWeight]
    positivity
  have hbucket :=
    exists_selectedParentActualIsPlankBucket_logarithmicLoss_of_activeCoarse_contained
      S hrho hcoarseContained P k r hr weight hweightNonneg
  dsimp only at hbucket
  obtain ⟨label, hoccupied, hretainedReal, ha, hab, hb, hplank⟩ := hbucket
  have hreal : Z.shadingMass.toReal <=
      selectedParentLogarithmicSideBucketLoss rho *
        (selectedParentArbitraryPreAffinePlankBucketShading
          e S B hrho label Z).shadingMass.toReal := by
    calc
      Z.shadingMass.toReal = ∑ p, weight p := by
        exact shadingMass_toReal_eq_sum_shadingPieceRealWeight Z
      _ <= selectedParentLogarithmicSideBucketLoss rho *
          (∑ p ∈ sideShapeBucket Finset.univ
            (fun p => selectedParentLongRelabeledSide e S B hrho p) label,
            weight p) := hretainedReal
      _ = selectedParentLogarithmicSideBucketLoss rho *
          (selectedParentArbitraryPreAffinePlankBucketShading
            e S B hrho label Z).shadingMass.toReal := by
        rw [selectedParentArbitraryPreAffinePlankBucketShading_mass_toReal]
        rfl
  have hpre : Z.shadingMass <=
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
        (selectedParentArbitraryPreAffinePlankBucketShading
          e S B hrho label Z).shadingMass := by
    apply (ENNReal.toReal_le_toReal Z.shadingMass_lt_top.ne
      (ENNReal.mul_ne_top (by simp)
        (selectedParentArbitraryPreAffinePlankBucketShading
          e S B hrho label Z).shadingMass_lt_top.ne)).mp
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using hreal
  have hretained :
      affineJacobian (bucketNormalizedAffineEquiv e label) * Z.shadingMass <=
        (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
          (selectedParentArbitraryPlankBucketShading
            e S B hrho label Z).shadingMass := by
    calc
      affineJacobian (bucketNormalizedAffineEquiv e label) * Z.shadingMass <=
          affineJacobian (bucketNormalizedAffineEquiv e label) *
            ((selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
              (selectedParentArbitraryPreAffinePlankBucketShading
                e S B hrho label Z).shadingMass) :=
        mul_le_mul' le_rfl hpre
      _ = (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
          (selectedParentArbitraryPlankBucketShading
            e S B hrho label Z).shadingMass := by
        rw [selectedParentArbitraryPlankBucketShading_shadingMass]
        ac_rfl
  refine ⟨label, hoccupied, ha, hab, hb, hplank, hretained, ?_⟩
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

variable {depth : Nat} {epsilon0 beta gamma : Real}

/-- Source-level low/high split after expanding and absorbing the literal
same-block Córdoba logarithms.  The high branch retains the actual occupied
label membership and pays only the local `selected.card`, never the ambient
label type. -/
theorem exists_source_fresh_katzTaoParameter_bound_or_sameOccurrenceWeightedCordoba_logAbsorbed_selectedCard
    {betaKT epsilonKT etaKT : Real} {delta0 : NNReal}
    (hKTP : KatzTaoAtParameters betaKT epsilonKT etaKT delta0)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (L : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C L.N L.epsilon L.eta S)
    (A : ENNReal)
    (htauHalf : S.tau W.m <= (2 : NNReal)⁻¹)
    (hgeometry : TauActiveCoarseAdmissibility
      (fullRefinementDatum D) C S W)
    (hdelta0 : S.tau W.m / 8 <= delta0)
    (hdensityBudget :
      (((S.tau W.m / 8 : NNReal) : ENNReal) ^ etaKT) *
          (2 * (128 * (sourceKatzTaoFreshLoss A : ENNReal))) <=
        (activeParentActualTubeDatum
          (tauScaleCover (fullRefinementDatum D) C S W)
          (fullRefinementDatum D).shading).shading.shadingDensity)
    (hcoefficient :
      128 * A <=
        ((S.tau W.m / 8 : NNReal) : ENNReal) ^ (-etaKT))
    {sourceEtaKT : Real} (hSourceKT : KatzTaoHypotheses D sourceEtaKT)
    (r : NNReal) (hr : 0 < r)
    (KT : ENNReal)
    (hKT : IsKatzTao KT
      (tauScaleCover (fullRefinementDatum D) C S W).activeCoarseFamily)
    {lossEta : Real} (hlossEta : 0 < lossEta)
    (hsideThreshold :
      S.tau W.m <= selectedParentLogarithmicSideBucketAbsorptionThreshold
        1 (lossEta / 2))
    (hangleThreshold :
      S.tau W.m / 2 <=
        selectedParentLogarithmicSideBucketAbsorptionThreshold
          4 (lossEta / 4)) :
    let firstCap : ENNReal :=
      Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
        delta (S.tau W.m) ((delta : ENNReal) ^ (-sourceEtaKT))
    (exists selectedLow : Finset
          {k // k ∈ (tauScaleCover
            (fullRefinementDatum D) C S W).activeCoarse},
        exists selectedFresh : Finset {k // k ∈ selectedLow},
          selectedFresh.Nonempty /\
          selectedFresh.card <= selectedLow.card /\
          D.shading.averageMultiplicity <=
            firstCap *
              ((2 * (sourceKatzTaoFreshLoss A : ENNReal)) *
                katzTaoMultiplicityRHS
                  (S.tau W.m / 8) selectedFresh.card epsilonKT betaKT)) \/
      exists G : GreedyDensityPartition
          (activeParentActualTubeDatum
            (tauScaleCover (fullRefinementDatum D) C S W)
            (fullRefinementDatum D).shading).family.bodyFamily
          (hullCandidates (Finset.univ : Finset
            {k // k ∈ (tauScaleCover
              (fullRefinementDatum D) C S W).activeCoarse}))
          (hullContainer
            (activeParentActualTubeDatum
              (tauScaleCover (fullRefinementDatum D) C S W)
              (fullRefinementDatum D).shading).family.bodyFamily)
          Finset.univ,
        exists selected : Finset
            {k // k ∈ (tauScaleCover
              (fullRefinementDatum D) C S W).activeCoarse},
          exists hcover : (forall k, k ∈ selected ->
            exists q : Fin (blocks
              (activeParentActualTubeDatum
                (tauScaleCover (fullRefinementDatum D) C S W)
                (fullRefinementDatum D).shading).family.bodyFamily G).length,
              k ∈ (blockAt
                (activeParentActualTubeDatum
                  (tauScaleCover (fullRefinementDatum D) C S W)
                  (fullRefinementDatum D).shading).family.bodyFamily
                G q).fiber /\
              ActualHighConcentrationOccurrence
                (activeParentActualTubeDatum
                  (tauScaleCover (fullRefinementDatum D) C S W)
                  (fullRefinementDatum D).shading)
                G A q),
          exists q : CertifiedHighOccurrenceLabel
              (activeParentActualTubeDatum
                (tauScaleCover (fullRefinementDatum D) C S W)
                (fullRefinementDatum D).shading) G A,
            q ∈ occupiedCertifiedHighOccurrences
              (activeParentActualTubeDatum
                (tauScaleCover (fullRefinementDatum D) C S W)
                (fullRefinementDatum D).shading)
              G A selected hcover /\
            let B := (blockAt
              (tauScaleCover (fullRefinementDatum D) C S W).activeCoarseFamily
              G q.1).fiber
            let e := contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame
                (tauScaleCover (fullRefinementDatum D) C S W)
                (by exact hD.delta_pos.trans_le (S.delta_le_tau W.m))
                G q.1) r hr
            let parent := {p // p ∈ B}
            let side : parent -> Fin 3 -> NNReal := fun p =>
              selectedParentLongRelabeledSide e
                (tauScaleCover (fullRefinementDatum D) C S W) B
                (by exact hD.delta_pos.trans_le (S.delta_le_tau W.m)) p
            let Z := sameOccurrenceBlockShading
              (activeParentActualTubeDatum
                (tauScaleCover (fullRefinementDatum D) C S W)
                (fullRefinementDatum D).shading)
              G A selected hcover q
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
                        (bucketNormalizedAffineEquiv e label)
                        (tauScaleCover (fullRefinementDatum D) C S W) B p),
                let Ybucket := selectedParentArbitraryPlankBucketShading
                  e (tauScaleCover (fullRefinementDatum D) C S W) B
                  (by exact hD.delta_pos.trans_le (S.delta_le_tau W.m))
                  label Z
                D.shading.averageMultiplicity <=
                  firstCap *
                    ((2 * (selected.card : ENNReal)) *
                      (((S.tau W.m : NNReal) : ENNReal) ^ (-lossEta) *
                        (KT *
                          (certifiedPlankThresholdedAngleScaleCap 576 *
                            (((((sideShapeUpper label 2)⁻¹ * r : NNReal) :
                                ENNReal) ^ 3) /
                              quantitativeCarrierFloor Ybucket))))) := by
  dsimp only
  have hsplit :=
    exists_source_fresh_katzTaoParameter_bound_or_sameOccurrenceWeightedCordoba
      hKTP D hD C S L W A htauHalf hgeometry hdelta0 hdensityBudget
        hcoefficient hSourceKT r hr KT hKT
  rcases hsplit with hlow | hhigh
  · exact Or.inl hlow
  · right
    obtain ⟨G, selected, hcover, q, hq, label, hoccupied, ha, hab, hb,
      hplank, hbound⟩ := hhigh
    refine ⟨G, selected, hcover, q, hq, label, hoccupied, ha, hab, hb,
      hplank, ?_⟩
    have hqCardNat := occupiedCertifiedHighOccurrences_card_le_selected
      (activeParentActualTubeDatum
        (tauScaleCover (fullRefinementDatum D) C S W)
        (fullRefinementDatum D).shading)
      G A selected hcover
    have hqCard :
        ((occupiedCertifiedHighOccurrences
          (activeParentActualTubeDatum
            (tauScaleCover (fullRefinementDatum D) C S W)
            (fullRefinementDatum D).shading)
          G A selected hcover).card : ENNReal) <=
            (selected.card : ENNReal) := by
      exact_mod_cast hqCardNat
    have hqFactor :
        2 * ((occupiedCertifiedHighOccurrences
          (activeParentActualTubeDatum
            (tauScaleCover (fullRefinementDatum D) C S W)
            (fullRefinementDatum D).shading)
          G A selected hcover).card : ENNReal) <=
            2 * (selected.card : ENNReal) :=
      mul_le_mul' le_rfl hqCard
    have hboundSelected := hbound.trans
      (mul_le_mul' le_rfl (mul_le_mul' hqFactor le_rfl))
    have hrho : 0 < S.tau W.m :=
      hD.delta_pos.trans_le (S.delta_le_tau W.m)
    exact sourceAverage_le_sameBlockCordoba_logAbsorbed
      (tauScaleCover (fullRefinementDatum D) C S W) hrho htauHalf
      hgeometry.contained_in_unit_ball G q.1 r hr
      (sameOccurrenceBlockShading
        (activeParentActualTubeDatum
          (tauScaleCover (fullRefinementDatum D) C S W)
          (fullRefinementDatum D).shading)
        G A selected hcover q)
      label hoccupied hplank D.shading.averageMultiplicity
      (Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
        delta (S.tau W.m) ((delta : ENNReal) ^ (-sourceEtaKT)))
      (2 * (selected.card : ENNReal)) KT hlossEta hsideThreshold
      hangleThreshold hboundSelected

/-- Mass-strengthened source split.  In the high branch the same literal
`q`, block, zero-extended shading `Z`, and side bucket `Ybucket` carry all
three payments: selected mass into `Z`, tau-source mass into `Z`, and affine
`Z` mass into `Ybucket`.  The final source-average estimate is the same
selected-card logarithmically absorbed bound. -/
theorem exists_source_fresh_katzTaoParameter_bound_or_sameOccurrenceWeightedCordoba_logAbsorbed_selectedCard_massStrengthened
    {betaKT epsilonKT etaKT : Real} {delta0 : NNReal}
    (hKTP : KatzTaoAtParameters betaKT epsilonKT etaKT delta0)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover (fullRefinementDatum D).family)
    (S : FiniteScaleSequence delta depth)
    (L : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family C L.N L.epsilon L.eta S)
    (A : ENNReal)
    (htauHalf : S.tau W.m <= (2 : NNReal)⁻¹)
    (hgeometry : TauActiveCoarseAdmissibility
      (fullRefinementDatum D) C S W)
    (hdelta0 : S.tau W.m / 8 <= delta0)
    (hdensityBudget :
      (((S.tau W.m / 8 : NNReal) : ENNReal) ^ etaKT) *
          (2 * (128 * (sourceKatzTaoFreshLoss A : ENNReal))) <=
        (activeParentActualTubeDatum
          (tauScaleCover (fullRefinementDatum D) C S W)
          (fullRefinementDatum D).shading).shading.shadingDensity)
    (hcoefficient :
      128 * A <=
        ((S.tau W.m / 8 : NNReal) : ENNReal) ^ (-etaKT))
    {sourceEtaKT : Real} (hSourceKT : KatzTaoHypotheses D sourceEtaKT)
    (r : NNReal) (hr : 0 < r)
    (KT : ENNReal)
    (hKT : IsKatzTao KT
      (tauScaleCover (fullRefinementDatum D) C S W).activeCoarseFamily)
    {lossEta : Real} (hlossEta : 0 < lossEta)
    (hsideThreshold :
      S.tau W.m <= selectedParentLogarithmicSideBucketAbsorptionThreshold
        1 (lossEta / 2))
    (hangleThreshold :
      S.tau W.m / 2 <=
        selectedParentLogarithmicSideBucketAbsorptionThreshold
          4 (lossEta / 4)) :
    let firstCap : ENNReal :=
      Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
        delta (S.tau W.m) ((delta : ENNReal) ^ (-sourceEtaKT))
    (exists selectedLow : Finset
          {k // k ∈ (tauScaleCover
            (fullRefinementDatum D) C S W).activeCoarse},
        exists selectedFresh : Finset {k // k ∈ selectedLow},
          selectedFresh.Nonempty /\
          selectedFresh.card <= selectedLow.card /\
          D.shading.averageMultiplicity <=
            firstCap *
              ((2 * (sourceKatzTaoFreshLoss A : ENNReal)) *
                katzTaoMultiplicityRHS
                  (S.tau W.m / 8) selectedFresh.card epsilonKT betaKT)) \/
      exists G : GreedyDensityPartition
          (activeParentActualTubeDatum
            (tauScaleCover (fullRefinementDatum D) C S W)
            (fullRefinementDatum D).shading).family.bodyFamily
          (hullCandidates (Finset.univ : Finset
            {k // k ∈ (tauScaleCover
              (fullRefinementDatum D) C S W).activeCoarse}))
          (hullContainer
            (activeParentActualTubeDatum
              (tauScaleCover (fullRefinementDatum D) C S W)
              (fullRefinementDatum D).shading).family.bodyFamily)
          Finset.univ,
        exists selected : Finset
            {k // k ∈ (tauScaleCover
              (fullRefinementDatum D) C S W).activeCoarse},
          exists hcover : (forall k, k ∈ selected ->
            exists q : Fin (blocks
              (activeParentActualTubeDatum
                (tauScaleCover (fullRefinementDatum D) C S W)
                (fullRefinementDatum D).shading).family.bodyFamily G).length,
              k ∈ (blockAt
                (activeParentActualTubeDatum
                  (tauScaleCover (fullRefinementDatum D) C S W)
                  (fullRefinementDatum D).shading).family.bodyFamily
                G q).fiber /\
              ActualHighConcentrationOccurrence
                (activeParentActualTubeDatum
                  (tauScaleCover (fullRefinementDatum D) C S W)
                  (fullRefinementDatum D).shading)
                G A q),
          exists q : CertifiedHighOccurrenceLabel
              (activeParentActualTubeDatum
                (tauScaleCover (fullRefinementDatum D) C S W)
                (fullRefinementDatum D).shading) G A,
            q ∈ occupiedCertifiedHighOccurrences
              (activeParentActualTubeDatum
                (tauScaleCover (fullRefinementDatum D) C S W)
                (fullRefinementDatum D).shading)
              G A selected hcover /\
            let B := (blockAt
              (tauScaleCover (fullRefinementDatum D) C S W).activeCoarseFamily
              G q.1).fiber
            let e := contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame
                (tauScaleCover (fullRefinementDatum D) C S W)
                (by exact hD.delta_pos.trans_le (S.delta_le_tau W.m))
                G q.1) r hr
            let parent := {p // p ∈ B}
            let side : parent -> Fin 3 -> NNReal := fun p =>
              selectedParentLongRelabeledSide e
                (tauScaleCover (fullRefinementDatum D) C S W) B
                (by exact hD.delta_pos.trans_le (S.delta_le_tau W.m)) p
            let Z := sameOccurrenceBlockShading
              (activeParentActualTubeDatum
                (tauScaleCover (fullRefinementDatum D) C S W)
                (fullRefinementDatum D).shading)
              G A selected hcover q
            (restrictActualTubeDatum
              (activeParentActualTubeDatum
                (tauScaleCover (fullRefinementDatum D) C S W)
                (fullRefinementDatum D).shading)
              selected).shading.shadingMass <=
                ((occupiedCertifiedHighOccurrences
                  (activeParentActualTubeDatum
                    (tauScaleCover (fullRefinementDatum D) C S W)
                    (fullRefinementDatum D).shading)
                  G A selected hcover).card : ENNReal) * Z.shadingMass /\
            (activeParentActualTubeDatum
              (tauScaleCover (fullRefinementDatum D) C S W)
              (fullRefinementDatum D).shading).shading.shadingMass <=
                (2 * ((occupiedCertifiedHighOccurrences
                  (activeParentActualTubeDatum
                    (tauScaleCover (fullRefinementDatum D) C S W)
                    (fullRefinementDatum D).shading)
                  G A selected hcover).card : ENNReal)) * Z.shadingMass /\
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
                        (bucketNormalizedAffineEquiv e label)
                        (tauScaleCover (fullRefinementDatum D) C S W) B p),
                let Ybucket := selectedParentArbitraryPlankBucketShading
                  e (tauScaleCover (fullRefinementDatum D) C S W) B
                  (by exact hD.delta_pos.trans_le (S.delta_le_tau W.m))
                  label Z
                affineJacobian (bucketNormalizedAffineEquiv e label) *
                    Z.shadingMass <=
                  (selectedParentLogarithmicSideBucketLoss
                    (S.tau W.m) : ENNReal) * Ybucket.shadingMass /\
                Ybucket.shadingMass ≠ 0 /\
                D.shading.averageMultiplicity <=
                  firstCap *
                    ((2 * (selected.card : ENNReal)) *
                      (((S.tau W.m : NNReal) : ENNReal) ^ (-lossEta) *
                        (KT *
                          (certifiedPlankThresholdedAngleScaleCap 576 *
                            (((((sideShapeUpper label 2)⁻¹ * r : NNReal) :
                                ENNReal) ^ 3) /
                              quantitativeCarrierFloor Ybucket))))) := by
  dsimp only
  have hfirst : D.shading.averageMultiplicity <=
      (Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
        delta (S.tau W.m) ((delta : ENNReal) ^ (-sourceEtaKT)) : ENNReal) *
        (activeParentActualTubeDatum
          (tauScaleCover (fullRefinementDatum D) C S W)
          (fullRefinementDatum D).shading).shading.averageMultiplicity := by
    change D.shading.averageMultiplicity <=
      (Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
        delta (S.tau W.m) ((delta : ENNReal) ^ (-sourceEtaKT)) : ENNReal) *
        (parentAggregatedShading
          (tauScaleCover (fullRefinementDatum D) C S W)
          (fullRefinementDatum D).shading).averageMultiplicity
    rw [← show sourceTauCover (fullRefinementDatum D) C S W.m =
      tauScaleCover (fullRefinementDatum D) C S W from rfl]
    exact
      Family8NormalizedLongCoreFirstOuterParentTransportV2.NormalizedLongIntervalCoreWitness.fullRefinement_averageMultiplicity_le_firstCap_mul_sourceTauParent
        D hD C S L W hSourceKT
  have hsplit :=
    exists_tauActiveParent_fresh_katzTaoParameter_bound_or_actualHighOccurrencePrefix
      hKTP (fullRefinementDatum D) hD.delta_pos C S W A htauHalf hgeometry
        hdelta0 hdensityBudget hcoefficient
  rcases hsplit with hlow | hhigh
  · left
    obtain ⟨selectedLow, selectedFresh, hnonempty, hcard, hbound⟩ := hlow
    refine ⟨selectedLow, selectedFresh, hnonempty, hcard, ?_⟩
    exact hfirst.trans (mul_le_mul' le_rfl hbound)
  · right
    obtain ⟨G, selected, hmass, _haverage, _hselectedAdmissible,
      hcover⟩ := hhigh
    have hrho : 0 < S.tau W.m :=
      hD.delta_pos.trans_le (S.delta_le_tau W.m)
    have hscalePosNN : 0 < S.tau W.m / 8 :=
      div_pos hrho (by norm_num)
    have hscalePos :
        0 < (((S.tau W.m / 8 : NNReal) : ENNReal)) :=
      ENNReal.coe_pos.mpr hscalePosNN
    have hpowerPos :
        0 < ((S.tau W.m / 8 : NNReal) : ENNReal) ^ etaKT :=
      ENNReal.rpow_pos hscalePos ENNReal.coe_ne_top
    have hlossPos : 0 < (sourceKatzTaoFreshLoss A : ENNReal) := by
      exact_mod_cast sourceKatzTaoFreshLoss_pos A
    have hdensityPos :
        0 < (activeParentActualTubeDatum
          (tauScaleCover (fullRefinementDatum D) C S W)
          (fullRefinementDatum D).shading).shading.shadingDensity := by
      have hproductPos :
          0 < (((S.tau W.m / 8 : NNReal) : ENNReal) ^ etaKT) *
            (2 * (128 * (sourceKatzTaoFreshLoss A : ENNReal))) := by
        positivity
      exact hproductPos.trans_le hdensityBudget
    have hsourceMassNe :
        (activeParentActualTubeDatum
          (tauScaleCover (fullRefinementDatum D) C S W)
          (fullRefinementDatum D).shading).shading.shadingMass ≠ 0 := by
      intro hzero
      have hdensityZero :
          (activeParentActualTubeDatum
            (tauScaleCover (fullRefinementDatum D) C S W)
            (fullRefinementDatum D).shading).shading.shadingDensity = 0 := by
        rw [Shading.shadingDensity, hzero]
        simp
      rw [hdensityZero] at hdensityPos
      exact (lt_irrefl 0) hdensityPos
    have hselection :=
      exists_sameOccurrenceBlockShading_weighted_retention_of_source_ne_zero
        (activeParentActualTubeDatum
          (tauScaleCover (fullRefinementDatum D) C S W)
          (fullRefinementDatum D).shading)
        G A selected hcover (2 : ENNReal) hmass hsourceMassNe
    obtain ⟨q, hq, hselectedMass, hsourceMass, hsourceAverage⟩ :=
      hselection
    let Z := sameOccurrenceBlockShading
      (activeParentActualTubeDatum
        (tauScaleCover (fullRefinementDatum D) C S W)
        (fullRefinementDatum D).shading)
      G A selected hcover q
    have hbucket :=
      exists_selectedParentArbitraryPlankBucket_massRetention_and_averageMultiplicity_le_of_activeCoarse_contained
        (tauScaleCover (fullRefinementDatum D) C S W) hrho
        hgeometry.contained_in_unit_ball G q.1 r hr Z KT hKT
    dsimp only at hbucket
    obtain ⟨label, hoccupied, ha, hab, hb, hplank, hretained,
      hZaverage⟩ := hbucket
    have hZMassNe : Z.shadingMass ≠ 0 := by
      intro hzero
      have hle := hsourceMass
      rw [hzero, mul_zero] at hle
      exact hsourceMassNe (bot_unique hle)
    have hYbucketMassNe :=
      bucket_ne_zero_of_nonzero_source_and_retention
        (affineJacobian_pos
          (bucketNormalizedAffineEquiv
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame
                (tauScaleCover (fullRefinementDatum D) C S W)
                hrho G q.1) r hr) label)).ne'
        hZMassNe hretained
    have hactiveAverage := hsourceAverage.trans
      (mul_le_mul' le_rfl hZaverage)
    have hsourceBound := hfirst.trans
      (mul_le_mul' le_rfl hactiveAverage)
    have hqCardNat := occupiedCertifiedHighOccurrences_card_le_selected
      (activeParentActualTubeDatum
        (tauScaleCover (fullRefinementDatum D) C S W)
        (fullRefinementDatum D).shading)
      G A selected hcover
    have hqCard :
        ((occupiedCertifiedHighOccurrences
          (activeParentActualTubeDatum
            (tauScaleCover (fullRefinementDatum D) C S W)
            (fullRefinementDatum D).shading)
          G A selected hcover).card : ENNReal) <=
            (selected.card : ENNReal) := by
      exact_mod_cast hqCardNat
    have hqFactor :
        2 * ((occupiedCertifiedHighOccurrences
          (activeParentActualTubeDatum
            (tauScaleCover (fullRefinementDatum D) C S W)
            (fullRefinementDatum D).shading)
          G A selected hcover).card : ENNReal) <=
            2 * (selected.card : ENNReal) :=
      mul_le_mul' le_rfl hqCard
    have hboundSelected := hsourceBound.trans
      (mul_le_mul' le_rfl (mul_le_mul' hqFactor le_rfl))
    have hfinal := sourceAverage_le_sameBlockCordoba_logAbsorbed
      (tauScaleCover (fullRefinementDatum D) C S W) hrho htauHalf
      hgeometry.contained_in_unit_ball G q.1 r hr Z label hoccupied hplank
      D.shading.averageMultiplicity
      (Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3.katzTaoDoubledFiberNatCap
        delta (S.tau W.m) ((delta : ENNReal) ^ (-sourceEtaKT)))
      (2 * (selected.card : ENNReal)) KT hlossEta hsideThreshold
      hangleThreshold hboundSelected
    refine ⟨G, selected, hcover, q, hq, hselectedMass, hsourceMass,
      label, hoccupied, ha, hab, hb, hplank, hretained, ?_, hfinal⟩
    exact hYbucketMassNe

#print axioms
  selectedParent_angleBucketLoss_le_logarithmic_of_activeCoarse_contained
#print axioms sourceAverage_le_logarithmicSameBlockCordobaEnvelope
#print axioms sourceAverage_le_sameBlockCordoba_logAbsorbed
#print axioms bucket_ne_zero_of_nonzero_source_and_retention
#print axioms
  exists_source_fresh_katzTaoParameter_bound_or_sameOccurrenceWeightedCordoba_logAbsorbed_selectedCard
#print axioms
  exists_selectedParentArbitraryPlankBucket_massRetention_and_averageMultiplicity_le_of_activeCoarse_contained
#print axioms
  exists_source_fresh_katzTaoParameter_bound_or_sameOccurrenceWeightedCordoba_logAbsorbed_selectedCard_massStrengthened

end
end Family8TauActiveParentSameOccurrenceWeightedCordobaScalarEnvelopeV1
