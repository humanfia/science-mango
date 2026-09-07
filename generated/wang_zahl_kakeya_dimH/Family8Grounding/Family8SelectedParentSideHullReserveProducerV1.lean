import Family8Grounding.Family8SelectedParentBlockDensityHullReserveInnerJointV1
import Family8Grounding.Family8SelectedParentJohnPlankQuantitativeLossV9
import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessProducerV1
import Mathlib.Tactic

/-!
# Literal selected-side upper envelope for the block-density hull reserve

The residual `blockCard / blockDensity` is first bounded by the volume of
the very same winning hull in tube-area units.  The John box has two sides
bounded by `2304`, while its shortest side is bounded by the short width of
the already selected side label.  Thus no adaptive fibre count and no new
selection enter the estimate.

The terminal theorem leaves only one pure scale inequality, now expressed
entirely through `rho`, the literal `bucketShortA label`, the source density,
and the desired count-one inner factor.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentSideHullReserveProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentBlockDensityHullReserveInnerJointV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessGeometryV1
open Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessProducerV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The explicit normalized-hull envelope produced by one occupied short
side label.  It is deliberately left as a quotient by the literal tube area;
this is the form needed by the density/card cancellation. -/
def selectedParentSideHullEnvelope (rho a : NNReal) : ENNReal :=
  ((2304 : ENNReal) ^ 2 *
      (((286654464 : NNReal) * rho / a : NNReal) : ENNReal)) /
    ((rho : ENNReal) ^ 2 / 2)

/-- The winning hull is bounded by two ambient John sides and its literal
shortest John side. -/
theorem selectedParent_hullVolume_le_fixedSq_mul_shortestSide
    (hfineContained : forall i, (fine.tubes i).carrier <=
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length) :
    let J := selectedParentGreedyBlockJohnFrame S hrho P k
    volume ((blockAt S.activeCoarseFamily P k).body : Set Space) <=
      (2304 : ENNReal) ^ 2 * (hullShortestSide J : ENNReal) := by
  dsimp only
  let J := selectedParentGreedyBlockJohnFrame S hrho P k
  have hside (i : Fin 3) : (J.side i : ENNReal) <= 2304 := by
    exact_mod_cast selectedParentGreedyBlockJohnSide_le_2304
      hfineContained S hrho hrhoOne P k i
  have hprod :
      (J.side 0 : ENNReal) * (J.side 1 : ENNReal) * (J.side 2 : ENNReal) <=
        (2304 : ENNReal) ^ 2 * (hullShortestSide J : ENNReal) := by
    by_cases h0 : J.side 0 <= min (J.side 1) (J.side 2)
    · have hm : hullShortestSide J = J.side 0 := by
        simp only [hullShortestSide, min_eq_left h0]
      rw [hm]
      calc
        (J.side 0 : ENNReal) * (J.side 1 : ENNReal) *
              (J.side 2 : ENNReal) <=
            (J.side 0 : ENNReal) * 2304 * 2304 := by
          exact mul_le_mul' (mul_le_mul' le_rfl (hside 1)) (hside 2)
        _ = (2304 : ENNReal) ^ 2 * (J.side 0 : ENNReal) := by ring
    · have h0' : min (J.side 1) (J.side 2) <= J.side 0 := le_of_not_ge h0
      have hm : hullShortestSide J = min (J.side 1) (J.side 2) := by
        simp only [hullShortestSide, min_eq_right h0']
      rw [hm]
      by_cases h12 : J.side 1 <= J.side 2
      · rw [min_eq_left h12]
        calc
          (J.side 0 : ENNReal) * (J.side 1 : ENNReal) *
                (J.side 2 : ENNReal) <=
              2304 * (J.side 1 : ENNReal) * 2304 := by
            exact mul_le_mul' (mul_le_mul' (hside 0) le_rfl) (hside 2)
          _ = (2304 : ENNReal) ^ 2 * (J.side 1 : ENNReal) := by ring
      · have h21 : J.side 2 <= J.side 1 := le_of_not_ge h12
        rw [min_eq_right h21]
        calc
          (J.side 0 : ENNReal) * (J.side 1 : ENNReal) *
                (J.side 2 : ENNReal) <=
              2304 * 2304 * (J.side 2 : ENNReal) := by
            exact mul_le_mul' (mul_le_mul' (hside 0) (hside 1)) le_rfl
          _ = (2304 : ENNReal) ^ 2 * (J.side 2 : ENNReal) := by ring
  calc
    volume ((blockAt S.activeCoarseFamily P k).body : Set Space) <=
        volume J.certificate.box.carrier := measure_mono J.certificate.outer_le
    _ = (J.side 0 : ENNReal) * (J.side 1 : ENNReal) *
        (J.side 2 : ENNReal) := by
      rw [FrameBox.volume_carrier, J.certificate.side_eq,
        Fin.prod_univ_three]
    _ <= (2304 : ENNReal) ^ 2 *
        (hullShortestSide J : ENNReal) := hprod

/-- The occupied side label bounds the same winning hull, with no dependence
on the auxiliary contraction radius. -/
theorem selectedParent_hullVolume_le_sideEnvelopeNumerator
    (hfineContained : forall i, (fine.tubes i).carrier <=
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label}) :
    volume ((blockAt S.activeCoarseFamily P k).body : Set Space) <=
      (2304 : ENNReal) ^ 2 *
        (((286654464 : NNReal) * rho / bucketShortA label : NNReal) :
          ENNReal) := by
  let J := selectedParentGreedyBlockJohnFrame S hrho P k
  have hratio : bucketShortA label <=
      286654464 * rho / hullShortestSide J := by
    simpa only [J] using selectedParent_bucketShortA_le_hullRatio
      hfineContained S hrho hrhoOne P k r hr label W
  have hm0 : 0 < hullShortestSide J := hullShortestSide_pos J
  have ha0 : 0 < bucketShortA label := bucketShortA_pos label
  have hamul : bucketShortA label * hullShortestSide J <=
      286654464 * rho := (le_div_iff₀ hm0).mp hratio
  have hm : hullShortestSide J <=
      286654464 * rho / bucketShortA label := by
    apply (le_div_iff₀ ha0).2
    simpa only [mul_comm] using hamul
  calc
    volume ((blockAt S.activeCoarseFamily P k).body : Set Space) <=
        (2304 : ENNReal) ^ 2 * (hullShortestSide J : ENNReal) := by
      simpa only [J] using
        selectedParent_hullVolume_le_fixedSq_mul_shortestSide
          hfineContained S hrho hrhoOne P k
    _ <= (2304 : ENNReal) ^ 2 *
        (((286654464 : NNReal) * rho / bucketShortA label : NNReal) :
          ENNReal) := by
      exact mul_le_mul' le_rfl (by exact_mod_cast hm)

/-- Exact literal card/density residual bounded by the selected-side hull
envelope. -/
theorem selectedParent_card_mul_blockDensity_inv_le_sideHullEnvelope
    (hfineContained : forall i, (fine.tubes i).carrier <=
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label})
    (hd0 : blockDensity S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P k) ≠ 0)
    (hdTop : blockDensity S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P k) ≠ ∞) :
    ((blockAt S.activeCoarseFamily P k).fiber.card : ENNReal) *
        (blockDensity S.activeCoarseFamily
          (blockAt S.activeCoarseFamily P k))⁻¹ <=
      selectedParentSideHullEnvelope rho (bucketShortA label) := by
  have hratio :=
    selectedParentBlock_card_mul_blockDensity_inv_le_hullVolume_div_area
      S hrho hrhoHalf P k hd0 hdTop
  have hvolume := selectedParent_hullVolume_le_sideEnvelopeNumerator
    hfineContained S hrho hrhoOne P k r hr label W
  calc
    ((blockAt S.activeCoarseFamily P k).fiber.card : ENNReal) *
          (blockDensity S.activeCoarseFamily
            (blockAt S.activeCoarseFamily P k))⁻¹ <=
        volume ((blockAt S.activeCoarseFamily P k).body : Set Space) /
          ((rho : ENNReal) ^ 2 / 2) := hratio
    _ <= selectedParentSideHullEnvelope rho (bucketShortA label) := by
      unfold selectedParentSideHullEnvelope
      exact ENNReal.div_le_div_right hvolume _

/-- The thinnest scalar adapter: an endpoint power ledger only has to pay
the explicit selected-side hull envelope. -/
theorem selectedParent_blockDensity_hullReserve_of_sideScaleReserve
    (hfineContained : forall i, (fine.tubes i).carrier <=
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (sourceDensity geometryLoss : ENNReal)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label})
    {epsilon beta : Real} (hbeta0 : 0 <= beta)
    (hd0 : blockDensity S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P k) ≠ 0)
    (hdTop : blockDensity S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P k) ≠ ∞)
    (hscale :
      (16 * certifiedPlankThresholdedAngleScaleCap 576 *
          (288 : ENNReal) ^ 3) *
          (selectedParentSideHullEnvelope rho
            (bucketShortA label)) ^ (beta / 2) <=
        (sourceDensity * geometryLoss) *
          proposition66AInnerFactor rho
            (bucketShortA label) (bucketShortB label) 1 epsilon beta) :
    let d := blockDensity S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P k)
    let card := ((blockAt S.activeCoarseFamily P k).fiber.card : ENNReal)
    (16 * certifiedPlankThresholdedAngleScaleCap 576 *
        (288 : ENNReal) ^ 3) * (card * d⁻¹) ^ (beta / 2) <=
      (sourceDensity * geometryLoss) *
        proposition66AInnerFactor rho
          (bucketShortA label) (bucketShortB label) 1 epsilon beta := by
  dsimp only
  have hratio := selectedParent_card_mul_blockDensity_inv_le_sideHullEnvelope
    hfineContained S hrho hrhoOne hrhoHalf P k r hr label W hd0 hdTop
  exact (mul_le_mul' le_rfl
    (ENNReal.rpow_le_rpow hratio (by linarith))).trans hscale

/-- Direct corrected inner-joint producer.  All object-level geometry is now
automatic; `hscale` is the only remaining pure endpoint exponent ledger. -/
theorem selectedParent_blockDensity_innerJoint_of_sideScaleReserve
    (hfineContained : forall i, (fine.tubes i).carrier <=
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (sourceDensity geometryLoss : ENNReal)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label})
    {epsilon beta : Real}
    (hbeta0 : 0 <= beta) (hbetaOne : beta <= 1)
    (hd0 : blockDensity S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P k) ≠ 0)
    (hdTop : blockDensity S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P k) ≠ ∞)
    (hscale :
      (16 * certifiedPlankThresholdedAngleScaleCap 576 *
          (288 : ENNReal) ^ 3) *
          (selectedParentSideHullEnvelope rho
            (bucketShortA label)) ^ (beta / 2) <=
        (sourceDensity * geometryLoss) *
          proposition66AInnerFactor rho
            (bucketShortA label) (bucketShortB label) 1 epsilon beta) :
    let d := blockDensity S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P k)
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let sourceFactor := affineJacobian (bucketNormalizedAffineEquiv e label) *
      (sourceDensity * ((rho : ENNReal) ^ 2 / 2))
    let G := certifiedPlankThresholdedAngleScaleCap 576 *
      (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3))
    d ^ (1 - beta / 2) * G <=
      (sourceFactor * geometryLoss) *
        proposition66AInnerFactor rho
          (bucketShortA label) (bucketShortB label)
          (blockAt S.activeCoarseFamily P k).fiber.card epsilon beta := by
  apply selectedParent_blockDensity_innerJoint_of_hullReserve
    S hrho hrhoHalf P k sourceDensity geometryLoss r hr label
      hbeta0 hbetaOne hd0 hdTop
  exact selectedParent_blockDensity_hullReserve_of_sideScaleReserve
    hfineContained S hrho hrhoOne hrhoHalf P k sourceDensity geometryLoss
      r hr label W hbeta0 hd0 hdTop hscale

#print axioms selectedParent_hullVolume_le_fixedSq_mul_shortestSide
#print axioms selectedParent_hullVolume_le_sideEnvelopeNumerator
#print axioms selectedParent_card_mul_blockDensity_inv_le_sideHullEnvelope
#print axioms selectedParent_blockDensity_hullReserve_of_sideScaleReserve
#print axioms selectedParent_blockDensity_innerJoint_of_sideScaleReserve

end
end Family8SelectedParentSideHullReserveProducerV1
