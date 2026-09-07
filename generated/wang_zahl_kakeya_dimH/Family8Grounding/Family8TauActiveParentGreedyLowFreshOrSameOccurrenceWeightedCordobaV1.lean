import Family8Grounding.Family8GreedyHighPrefixSameOccurrenceWeightedCordobaConnectorV1
import Family8Grounding.Family8TauActiveParentGreedyLowFreshOrActualHighOccurrenceV1
import Mathlib.Tactic

/-!
# Tau-active greedy low/high to same-occurrence quantitative Cordoba

The older selected-parent plank bucket requested unit-ball support for every
fine tube, although its proof uses that premise only to bound the winning
hull of the active coarse parents.  At the literal tau scale the exact
`TauActiveCoarseAdmissibility` certificate already supplies the latter
support directly.  The local support lemmas below expose that weaker input.

The final theorem keeps the literal tau-parent datum, the greedy partition,
the selected high prefix, the occupied high-occurrence label, and its
zero-extended same-block shading.  No global admissibility hypothesis on the
original fine datum is introduced.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8TauActiveParentGreedyLowFreshOrSameOccurrenceWeightedCordobaV1

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
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8GreedyHighPrefixActualOccurrenceV1
open Family8GreedyHighPrefixSameOccurrenceWeightedMassV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8PositiveCarrierShadingRestrictionV4
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentArbitraryBlockPlankBucketV4
open Family8SelectedParentArbitraryBlockQuantitativeCordobaV2
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8ScaleContainedB2NativeFreshKatzTaoEndpointV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8StickyParentHullSupportOnlyV2
open Family8StickyParentHullVolumeBoundV1
open Family8TauActiveParentGreedyLowFreshOrActualHighOccurrenceV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyWZ2AmbientShearDistortedTubeAdapterV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Active coarse support, rather than support of every fine tube, controls
the winning-hull John sides. -/
theorem selectedParentGreedyBlockJohnSide_le_2304_of_activeCoarse_contained
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hcoarseContained : forall p : ActiveParentIndex S,
      (S.activeCoarseFamily p : Set Space) ⊆
        Metric.closedBall (0 : Space) 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length) (i : Fin 3) :
    (selectedParentGreedyBlockJohnFrame S hrho P k).side i <= 2304 := by
  let J := selectedParentGreedyBlockJohnFrame S hrho P k
  let B := J.certificate.box.rescale (288 : NNReal)⁻¹
  have hHull :
      ((blockAt S.activeCoarseFamily P k).body : Set Space) ⊆
        Metric.closedBall (0 : Space) 4 := by
    simpa only [coe_closedBallFourBody] using
      (blockAt_body_subset_of_base S.activeCoarseFamily Finset.univ P
        closedBallFourBody (fun p _hp => by
          intro x hx
          have hx1 := hcoarseContained p hx
          have hx4 : x ∈ Metric.closedBall (0 : Space) 4 := by
            rw [Metric.mem_closedBall] at hx1 ⊢
            exact hx1.trans (by norm_num)
          simpa only [coe_closedBallFourBody] using hx4) k)
  have hxBall : B.positiveFacePoint i ∈ Metric.closedBall (0 : Space) 4 :=
    hHull (J.certificate.inner_le (B.positiveFacePoint_mem_carrier i))
  have hyBall : B.negativeFacePoint i ∈ Metric.closedBall (0 : Space) 4 :=
    hHull (J.certificate.inner_le (B.negativeFacePoint_mem_carrier i))
  have hdistReal :
      dist (B.positiveFacePoint i) (B.negativeFacePoint i) <= (8 : Real) := by
    rw [Metric.mem_closedBall] at hxBall hyBall
    calc
      dist (B.positiveFacePoint i) (B.negativeFacePoint i) <=
          dist (B.positiveFacePoint i) 0 +
            dist 0 (B.negativeFacePoint i) := dist_triangle _ _ _
      _ <= 4 + 4 := add_le_add hxBall (by simpa [dist_comm] using hyBall)
      _ = 8 := by norm_num
  rw [B.dist_positiveFacePoint_negativeFacePoint] at hdistReal
  have hdist : B.side i <= (8 : NNReal) := by exact_mod_cast hdistReal
  change (288 : NNReal)⁻¹ * J.certificate.box.side i <= 8 at hdist
  rw [J.certificate.side_eq] at hdist
  have hscaled :=
    (inv_mul_le_iff₀ (by norm_num : (0 : NNReal) < 288)).1 hdist
  norm_num at hscaled ⊢
  exact hscaled

/-- The common contracted ball survives using only active-coarse support. -/
theorem selectedParentContracted_closedBall_subset_of_activeCoarse_contained
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hcoarseContained : forall p : ActiveParentIndex S,
      (S.activeCoarseFamily p : Set Space) ⊆
        Metric.closedBall (0 : Space) 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r)
    (p : {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber}) :
    let J := selectedParentGreedyBlockJohnFrame S hrho P k
    let e := contractedJohnAffineEquiv J r hr
    let T := S.coarse.tubes p.1.1
    Metric.closedBall (e T.axis.base)
        (((r * rho / 6912 : NNReal) : Real)) ⊆
      (selectedParentAffineFamily e S
        (blockAt S.activeCoarseFamily P k).fiber p : Set Space) := by
  dsimp only
  let J := selectedParentGreedyBlockJohnFrame S hrho P k
  let e := contractedJohnAffineEquiv J r hr
  let T := S.coarse.tubes p.1.1
  have hJside : forall i, J.side i <= (2304 : NNReal) := by
    intro i
    exact selectedParentGreedyBlockJohnSide_le_2304_of_activeCoarse_contained
      S hrho hcoarseContained P k i
  intro y hy
  rw [selectedParentAffineFamily_apply]
  change y ∈ e '' T.carrier
  refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
  apply Metric.closedBall_subset_cthickening T.axis.base_mem_carrier
  rw [Metric.mem_closedBall]
  rw [Metric.mem_closedBall] at hy
  have hinverse := contractedJohnAffineEquiv_symm_dist_le
    J 2304 r hr hJside y (e T.axis.base)
  calc
    dist (e.symm y) T.axis.base =
        dist (e.symm y) (e.symm (e T.axis.base)) := by
          rw [e.symm_apply_apply]
    _ <= ((3 * 2304 / r : NNReal) : Real) * dist y (e T.axis.base) :=
      hinverse
    _ <= ((3 * 2304 / r : NNReal) : Real) *
          (((r * rho / 6912 : NNReal) : Real)) := by
      exact mul_le_mul_of_nonneg_left hy (by positivity)
    _ = (rho : Real) := by
      norm_num [NNReal.coe_div, NNReal.coe_mul]
      field_simp [show (r : Real) ≠ 0 by exact_mod_cast hr.ne']

/-- Quantitative lower John-side floor from active-coarse support. -/
theorem selectedParentContractedJohnSide_floor_of_activeCoarse_contained
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hcoarseContained : forall p : ActiveParentIndex S,
      (S.activeCoarseFamily p : Set Space) ⊆
        Metric.closedBall (0 : Space) 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r)
    (p : {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
    (i : Fin 3) :
    selectedParentSideFloor rho r <=
      selectedParentAffineJohnSide
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S (blockAt S.activeCoarseFamily P k).fiber hrho p i := by
  let J := selectedParentGreedyBlockJohnFrame S hrho P k
  let e := contractedJohnAffineEquiv J r hr
  let T := S.coarse.tubes p.1.1
  have hball :
      Metric.closedBall (e T.axis.base)
          (((r * rho / 6912 : NNReal) : Real)) ⊆
        (selectedParentAffineFamily e S
          (blockAt S.activeCoarseFamily P k).fiber p : Set Space) := by
    simpa [J, e, T] using
      (selectedParentContracted_closedBall_subset_of_activeCoarse_contained
        S hrho hcoarseContained P k r hr p)
  have hlower := boxCertificate_side_lower_of_closedBall_subset
    (e T.axis.base) hball
    (selectedParentAffineJohnCertificate e S
      (blockAt S.activeCoarseFamily P k).fiber hrho p) i
  have hfloor :
      2 * (r * rho / 6912) = selectedParentSideFloor rho r := by
    apply NNReal.eq
    norm_num [selectedParentSideFloor, NNReal.coe_div, NNReal.coe_mul]
    ring
  simpa [J, e, T, hfloor] using hlower

/-- Long-axis relabeling preserves the active-coarse side floor. -/
theorem selectedParentContractedLongRelabeledSide_floor_of_activeCoarse_contained
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hcoarseContained : forall p : ActiveParentIndex S,
      (S.activeCoarseFamily p : Set Space) ⊆
        Metric.closedBall (0 : Space) 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r)
    (p : {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
    (i : Fin 3) :
    selectedParentSideFloor rho r <=
      selectedParentLongRelabeledSide
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S (blockAt S.activeCoarseFamily P k).fiber hrho p i := by
  simp only [selectedParentLongRelabeledSide, relabeledSide_apply]
  exact selectedParentContractedJohnSide_floor_of_activeCoarse_contained
    S hrho hcoarseContained P k r hr p _

/-- The occupied side labels have the same scale-free logarithmic bound
under the exact active-coarse support premise. -/
theorem selectedParent_occupiedSideShapeLabels_card_le_logarithmic_of_activeCoarse_contained
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hcoarseContained : forall p : ActiveParentIndex S,
      (S.activeCoarseFamily p : Set Space) ⊆
        Metric.closedBall (0 : Space) 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) :
    let parent := {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber}
    let side : parent -> Fin 3 -> NNReal := fun p =>
      selectedParentLongRelabeledSide
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S (blockAt S.activeCoarseFamily P k).fiber hrho p
    (occupiedWeightBuckets (Finset.univ : Finset parent)
      (fun p => sideShapeLabel (side p))).card <=
        selectedParentLogarithmicSideBucketLoss rho := by
  dsimp only
  have hcard :
      (occupiedWeightBuckets
        (Finset.univ : Finset
          {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
        (fun p => sideShapeLabel
          (selectedParentLongRelabeledSide
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
            S (blockAt S.activeCoarseFamily P k).fiber hrho p))).card <=
          selectedParentSideBucketLoss rho r := by
    apply card_occupied_sideShapeLabel_le
      (lower := (selectedParentSideFloor rho r : Real))
      (upper := ((1728 * r : NNReal) : Real))
    · exact_mod_cast selectedParentSideFloor_pos hrho hr
    · intro p _hp i
      constructor
      · exact_mod_cast
          selectedParentContractedLongRelabeledSide_floor_of_activeCoarse_contained
            S hrho hcoarseContained P k r hr p i
      · exact_mod_cast selectedParentContractedLongRelabeledSide_le
          S hrho P k r hr p i
  exact hcard.trans (selectedParentSideBucketLoss_le_logarithmic hrho r hr)

/-- Weighted plank-bucket retention from the exact active-coarse support
premise. -/
theorem exists_selectedParentActualIsPlankBucket_logarithmicLoss_of_activeCoarse_contained
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hcoarseContained : forall p : ActiveParentIndex S,
      (S.activeCoarseFamily p : Set Space) ⊆
        Metric.closedBall (0 : Space) 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r)
    (weight :
      {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber} -> Real)
    (hweightNonneg : forall p, 0 <= weight p) :
    let parent := {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber}
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let side : parent -> Fin 3 -> NNReal := fun p =>
      selectedParentLongRelabeledSide e S
        (blockAt S.activeCoarseFamily P k).fiber hrho p
    exists label : Fin 3 -> Int,
      label ∈ occupiedWeightBuckets (Finset.univ : Finset parent)
        (fun p => sideShapeLabel (side p)) ∧
      (∑ p : parent, weight p) <=
        selectedParentLogarithmicSideBucketLoss rho *
          (∑ p ∈ sideShapeBucket Finset.univ side label, weight p) ∧
      0 < bucketShortA label ∧
      bucketShortA label <= bucketShortB label ∧
      bucketShortB label <= 1 ∧
      forall p, p ∈ sideShapeBucket Finset.univ side label ->
        IsPlank 576 (bucketShortA label) (bucketShortB label)
          (selectedParentAffineFamily
            (bucketNormalizedAffineEquiv e label) S
            (blockAt S.activeCoarseFamily P k).fiber p) := by
  dsimp only
  have hbucket := exists_selectedParentActualIsPlankBucket_weight_retention
    S hrho P k r hr weight
  dsimp only at hbucket
  obtain ⟨label, hoccupied, hretained, ha, hab, hb, hplank⟩ := hbucket
  have hcard :=
    selectedParent_occupiedSideShapeLabels_card_le_logarithmic_of_activeCoarse_contained
      S hrho hcoarseContained P k r hr
  dsimp only at hcard
  have hbucketNonneg :
      0 <= ∑ p ∈ sideShapeBucket Finset.univ
        (fun p => selectedParentLongRelabeledSide
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho p) label,
          weight p := by
    apply Finset.sum_nonneg
    intro p _hp
    exact hweightNonneg p
  refine ⟨label, hoccupied, ?_, ha, hab, hb, hplank⟩
  calc
    (∑ p : {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber}, weight p) <=
        (occupiedWeightBuckets
          (Finset.univ : Finset
            {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
          (fun p => sideShapeLabel
            (selectedParentLongRelabeledSide
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
              S (blockAt S.activeCoarseFamily P k).fiber hrho p))).card *
          (∑ p ∈ sideShapeBucket Finset.univ
            (fun p => selectedParentLongRelabeledSide
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
              S (blockAt S.activeCoarseFamily P k).fiber hrho p) label,
            weight p) := hretained
    _ <= selectedParentLogarithmicSideBucketLoss rho *
          (∑ p ∈ sideShapeBucket Finset.univ
            (fun p => selectedParentLongRelabeledSide
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
              S (blockAt S.activeCoarseFamily P k).fiber hrho p) label,
            weight p) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hbucketNonneg

/-- The weakest arbitrary-block quantitative Cordoba endpoint using only
active-coarse support. -/
theorem exists_selectedParentArbitraryPlankBucket_averageMultiplicity_le_of_activeCoarse_contained
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
  refine ⟨label, hoccupied, ha, hab, hb, hplank, ?_⟩
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

variable {depth N : Nat} {epsilonLong : Real} {etaLong : Nat -> Real}

/-- The literal tau-active greedy split, assembled through the same occupied
high occurrence into the quantitative Cordoba endpoint. -/
theorem exists_tauActiveParent_fresh_katzTaoParameter_bound_or_sameOccurrenceWeightedCordoba
    {betaKT epsilonKT etaKT : Real} {delta0 : NNReal}
    (hKTP : KatzTaoAtParameters betaKT epsilonKT etaKT delta0)
    (D : ActualTubeDatum delta index) (hdeltaPos : 0 < delta)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness
      D.family C N epsilonLong etaLong S)
    (A : ENNReal)
    (htauHalf : S.tau W.m <= (2 : NNReal)⁻¹)
    (hgeometry : TauActiveCoarseAdmissibility D C S W)
    (hdelta0 : S.tau W.m / 8 <= delta0)
    (hdensityBudget :
      (((S.tau W.m / 8 : NNReal) : ENNReal) ^ etaKT) *
          (2 * (128 * (sourceKatzTaoFreshLoss A : ENNReal))) <=
        (activeParentActualTubeDatum
          (tauScaleCover D C S W) D.shading).shading.shadingDensity)
    (hcoefficient :
      128 * A <=
        ((S.tau W.m / 8 : NNReal) : ENNReal) ^ (-etaKT))
    (r : NNReal) (hr : 0 < r)
    (KT : ENNReal)
    (hKT : IsKatzTao KT (tauScaleCover D C S W).activeCoarseFamily) :
    (exists selectedLow : Finset
          {k // k ∈ (tauScaleCover D C S W).activeCoarse},
        exists selectedFresh : Finset {k // k ∈ selectedLow},
          selectedFresh.Nonempty /\
          selectedFresh.card <= selectedLow.card /\
          (activeParentActualTubeDatum
              (tauScaleCover D C S W) D.shading).shading.averageMultiplicity <=
            (2 * (sourceKatzTaoFreshLoss A : ENNReal)) *
              katzTaoMultiplicityRHS
                (S.tau W.m / 8) selectedFresh.card epsilonKT betaKT) \/
      exists P : GreedyDensityPartition
          (activeParentActualTubeDatum
            (tauScaleCover D C S W) D.shading).family.bodyFamily
          (hullCandidates (Finset.univ : Finset
            {k // k ∈ (tauScaleCover D C S W).activeCoarse}))
          (hullContainer
            (activeParentActualTubeDatum
              (tauScaleCover D C S W) D.shading).family.bodyFamily)
          Finset.univ,
        exists selected : Finset
            {k // k ∈ (tauScaleCover D C S W).activeCoarse},
          exists hcover : (forall k, k ∈ selected ->
            exists q : Fin (blocks
              (activeParentActualTubeDatum
                (tauScaleCover D C S W) D.shading).family.bodyFamily P).length,
              k ∈ (blockAt
                (activeParentActualTubeDatum
                  (tauScaleCover D C S W) D.shading).family.bodyFamily
                P q).fiber /\
              ActualHighConcentrationOccurrence
                (activeParentActualTubeDatum
                  (tauScaleCover D C S W) D.shading)
                P A q),
          exists q : CertifiedHighOccurrenceLabel
              (activeParentActualTubeDatum
                (tauScaleCover D C S W) D.shading) P A,
            q ∈ occupiedCertifiedHighOccurrences
              (activeParentActualTubeDatum
                (tauScaleCover D C S W) D.shading)
              P A selected hcover /\
            let B := (blockAt
              (tauScaleCover D C S W).activeCoarseFamily P q.1).fiber
            let e := contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame
                (tauScaleCover D C S W) (by
                  exact hdeltaPos.trans_le (S.delta_le_tau W.m)) P q.1)
              r hr
            let parent := {p // p ∈ B}
            let side : parent -> Fin 3 -> NNReal := fun p =>
              selectedParentLongRelabeledSide e
                (tauScaleCover D C S W) B
                (by exact hdeltaPos.trans_le (S.delta_le_tau W.m)) p
            let Z := sameOccurrenceBlockShading
              (activeParentActualTubeDatum
                (tauScaleCover D C S W) D.shading)
              P A selected hcover q
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
                        (tauScaleCover D C S W) B p),
                let Ybucket := selectedParentArbitraryPlankBucketShading
                  e (tauScaleCover D C S W) B
                  (by exact hdeltaPos.trans_le (S.delta_le_tau W.m))
                  label Z
                let hplankPos : forall t,
                    IsPlank 576 (bucketShortA label) (bucketShortB label)
                      (quantitativePositiveCarrierFamily Ybucket t) := fun t =>
                  selectedParentPlankBucket_isPlank
                    e (tauScaleCover D C S W) B
                    (by exact hdeltaPos.trans_le (S.delta_le_tau W.m))
                    label hplank t.1
                let cert := chosenPlankCertificate hplankPos
                (activeParentActualTubeDatum
                    (tauScaleCover D C S W) D.shading).shading.averageMultiplicity <=
                  (2 *
                    ((occupiedCertifiedHighOccurrences
                      (activeParentActualTubeDatum
                        (tauScaleCover D C S W) D.shading)
                      P A selected hcover).card : ENNReal)) *
                    ((selectedParentLogarithmicSideBucketLoss
                        (S.tau W.m) : ENNReal) *
                      (2 * certifiedPlankDyadicFactor
                        (certifiedPlankThresholdedLevels cert) KT
                          (certifiedPlankThresholdedAngleScaleCap 576 *
                            (((((sideShapeUpper label 2)⁻¹ * r : NNReal) :
                                ENNReal) ^ 3) /
                              quantitativeCarrierFloor Ybucket)))) := by
  have hsplit :=
    exists_tauActiveParent_fresh_katzTaoParameter_bound_or_actualHighOccurrencePrefix
      hKTP D hdeltaPos C S W A htauHalf hgeometry hdelta0
        hdensityBudget hcoefficient
  rcases hsplit with hlow | hhigh
  · exact Or.inl hlow
  · rcases hhigh with ⟨P, selected, hmass, _haverage, _hselectedAdmissible,
      hcover⟩
    right
    refine ⟨P, selected, hcover, ?_⟩
    have hrho : 0 < S.tau W.m :=
      hdeltaPos.trans_le (S.delta_le_tau W.m)
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
          (tauScaleCover D C S W) D.shading).shading.shadingDensity := by
      have hproductPos :
          0 < (((S.tau W.m / 8 : NNReal) : ENNReal) ^ etaKT) *
            (2 * (128 * (sourceKatzTaoFreshLoss A : ENNReal))) := by
        positivity
      exact hproductPos.trans_le hdensityBudget
    have hsourceMassNe :
        (activeParentActualTubeDatum
          (tauScaleCover D C S W) D.shading).shading.shadingMass ≠ 0 := by
      intro hzero
      have hdensityZero :
          (activeParentActualTubeDatum
            (tauScaleCover D C S W) D.shading).shading.shadingDensity = 0 := by
        rw [Shading.shadingDensity, hzero]
        simp
      rw [hdensityZero] at hdensityPos
      exact (lt_irrefl 0) hdensityPos
    have hselection :=
      exists_sameOccurrenceBlockShading_weighted_retention_of_source_ne_zero
        (activeParentActualTubeDatum
          (tauScaleCover D C S W) D.shading)
        P A selected hcover (2 : ENNReal) hmass hsourceMassNe
    obtain ⟨q, hq, _hselectedMass, _hsourceMass, hsourceAverage⟩ :=
      hselection
    let Z := sameOccurrenceBlockShading
      (activeParentActualTubeDatum
        (tauScaleCover D C S W) D.shading)
      P A selected hcover q
    have hcordoba :=
      exists_selectedParentArbitraryPlankBucket_averageMultiplicity_le_of_activeCoarse_contained
        (tauScaleCover D C S W) hrho hgeometry.contained_in_unit_ball
        P q.1 r hr Z KT hKT
    dsimp only at hcordoba
    obtain ⟨label, hoccupied, ha, hab, hb, hplank, hbound⟩ := hcordoba
    refine ⟨q, hq, label, hoccupied, ha, hab, hb, hplank, ?_⟩
    exact hsourceAverage.trans (mul_le_mul' le_rfl hbound)

#print axioms
  selectedParentGreedyBlockJohnSide_le_2304_of_activeCoarse_contained
#print axioms
  selectedParent_occupiedSideShapeLabels_card_le_logarithmic_of_activeCoarse_contained
#print axioms
  exists_selectedParentArbitraryPlankBucket_averageMultiplicity_le_of_activeCoarse_contained
#print axioms
  exists_tauActiveParent_fresh_katzTaoParameter_bound_or_sameOccurrenceWeightedCordoba

end
end Family8TauActiveParentGreedyLowFreshOrSameOccurrenceWeightedCordobaV1
