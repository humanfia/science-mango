import Family8Grounding.Family8SelectedParentSideHullReserveProducerV1
import Family8Grounding.Family8Prop51JointOccurrenceWeightedSelectionV1
import Mathlib.Tactic

/-!
# Dyadic-density cancellation for the selected-side hull envelope

The selected block satisfies the literal geometric estimate

`blockCard * blockDensity⁻¹ ≤ selectedParentSideHullEnvelope rho a`.

On a V552 dyadic density band `[d0, 2*d0)`, this turns the exact joint
outer/John residual

`blockCard^(beta/2) * d0^{-(1-beta/2)}`

into at most

`2^(beta/2) * selectedParentSideHullEnvelope rho a^(beta/2)`.

This keeps the inverse `d0` supplied by the exact outer coefficient and does
not split the outer and hull reserves into two stronger independent gates.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentSideHullDyadicCancellationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family8Prop51JointOccurrenceWeightedSelectionV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentSideHullReserveProducerV1
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-- Abstract scalar cancellation behind the selected-side producer.  The
exponent left by the exact outer coefficient is essential: for `beta ≤ 1`,
the remaining power of the dyadic lower endpoint is nonpositive. -/
theorem card_rpow_mul_dyadicLower_inv_rpow_le_two_mul_envelope_rpow_mul_lower_rpow
    {card density lower envelope : ENNReal} {beta : Real}
    (hbeta0 : 0 ≤ beta) (_hbetaOne : beta ≤ 1)
    (hlowerOne : 1 ≤ lower) (hlowerTop : lower ≠ ∞)
    (hlowerDensity : lower ≤ density)
    (hdensityUpper : density ≤ 2 * lower)
    (hcardDensity : card * density⁻¹ ≤ envelope) :
    card ^ (beta / 2) * lower ^ (-(1 - beta / 2)) ≤
      ((2 : ENNReal) ^ (beta / 2) * envelope ^ (beta / 2)) *
        lower ^ (beta - 1) := by
  have hp : 0 ≤ beta / 2 := by linarith
  have hlower0 : lower ≠ 0 :=
    (zero_lt_one.trans_le hlowerOne).ne'
  have hdensity0 : density ≠ 0 :=
    (zero_lt_one.trans_le (hlowerOne.trans hlowerDensity)).ne'
  have hdensityTop : density ≠ ∞ :=
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (by norm_num) hlowerTop) hdensityUpper
  have hcard : card ≤ envelope * (2 * lower) := by
    calc
      card = (card * density⁻¹) * density := by
        rw [mul_assoc, ENNReal.inv_mul_cancel hdensity0 hdensityTop,
          mul_one]
      _ ≤ envelope * (2 * lower) :=
        mul_le_mul' hcardDensity hdensityUpper
  have hresidual :
      lower ^ (beta / 2) * lower ^ (-(1 - beta / 2)) =
        lower ^ (beta - 1) := by
    rw [← ENNReal.rpow_add _ _ hlower0 hlowerTop]
    congr 1
    ring
  have hcardPow : card ^ (beta / 2) ≤
      (envelope * (2 * lower)) ^ (beta / 2) :=
    ENNReal.rpow_le_rpow hcard hp
  calc
    card ^ (beta / 2) * lower ^ (-(1 - beta / 2)) ≤
        (envelope * (2 * lower)) ^ (beta / 2) *
          lower ^ (-(1 - beta / 2)) :=
      mul_le_mul' hcardPow le_rfl
    _ = ((2 : ENNReal) ^ (beta / 2) * envelope ^ (beta / 2)) *
        (lower ^ (beta / 2) * lower ^ (-(1 - beta / 2))) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp,
        ENNReal.mul_rpow_of_nonneg _ _ hp]
      ac_rfl
    _ = ((2 : ENNReal) ^ (beta / 2) * envelope ^ (beta / 2)) *
        lower ^ (beta - 1) := by rw [hresidual]

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Object-level form for one selected parent block and its literal V552
dyadic density band.  The only geometric input is membership in the already
selected side bucket. -/
theorem selectedParent_card_rpow_mul_dyadicLower_inv_rpow_le_sideEnvelope_mul_dyadicGain
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1) (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label})
    (base : ENNReal) (bucketKey : Nat)
    (hband : InENNRealDyadicBand base bucketKey
      (blockDensity S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P k)))
    (hbaseOne : 1 ≤ base) (hbaseTop : base ≠ ∞)
    {beta : Real} (hbeta0 : 0 ≤ beta) (hbetaOne : beta ≤ 1) :
    ((blockAt S.activeCoarseFamily P k).fiber.card : ENNReal) ^
          (beta / 2) *
        ((2 : ENNReal) ^ bucketKey * base) ^
          (-(1 - beta / 2)) ≤
      ((2 : ENNReal) ^ (beta / 2) *
        (selectedParentSideHullEnvelope rho
          (bucketShortA label)) ^ (beta / 2)) *
        ((2 : ENNReal) ^ bucketKey * base) ^ (beta - 1) := by
  let d0 : ENNReal := (2 : ENNReal) ^ bucketKey * base
  let d : ENNReal := blockDensity S.activeCoarseFamily
    (blockAt S.activeCoarseFamily P k)
  have hd0One : 1 ≤ d0 := by
    dsimp only [d0]
    calc
      (1 : ENNReal) = 1 * 1 := by simp
      _ ≤ (2 : ENNReal) ^ bucketKey * base :=
        mul_le_mul' (one_le_pow₀ (by norm_num)) hbaseOne
  have hd0Top : d0 ≠ ∞ := by
    dsimp only [d0]
    exact ENNReal.mul_ne_top (by simp) hbaseTop
  have hd0d : d0 ≤ d := by
    simpa only [d0, d] using hband.1
  have hdd0 : d ≤ 2 * d0 := by
    calc
      d ≤ (2 : ENNReal) ^ (bucketKey + 1) * base := by
        simpa only [d] using hband.2.le
      _ = 2 * d0 := by
        dsimp only [d0]
        rw [pow_succ]
        ac_rfl
  have hd0 : d ≠ 0 :=
    (zero_lt_one.trans_le (hd0One.trans hd0d)).ne'
  have hdTop : d ≠ ∞ :=
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (by norm_num) hd0Top) hdd0
  have hratio :
      ((blockAt S.activeCoarseFamily P k).fiber.card : ENNReal) * d⁻¹ ≤
        selectedParentSideHullEnvelope rho (bucketShortA label) := by
    simpa only [d] using
      selectedParent_card_mul_blockDensity_inv_le_sideHullEnvelope
        hfineContained S hrho hrhoOne hrhoHalf P k r hr label W hd0 hdTop
  simpa only [d0, d] using
    card_rpow_mul_dyadicLower_inv_rpow_le_two_mul_envelope_rpow_mul_lower_rpow
      hbeta0 hbetaOne hd0One hd0Top hd0d hdd0 hratio

/-- Minimal remaining side-scale ledger after the exact V552 outer
coefficient has supplied `d0^{-(1-beta/2)}`.  In particular, this premise
pays the selected-side envelope only once, jointly with the outer reserve. -/
theorem selectedParent_jointOuterCardDensityResidual_of_sideScaleReserve
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1) (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (sourceDensity geometryLoss johnLoss : ENNReal)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label})
    (base : ENNReal) (bucketKey : Nat)
    (hband : InENNRealDyadicBand base bucketKey
      (blockDensity S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P k)))
    (hbaseOne : 1 ≤ base) (hbaseTop : base ≠ ∞)
    {epsilon beta : Real} (hbeta0 : 0 ≤ beta) (hbetaOne : beta ≤ 1)
    (hscale :
      johnLoss *
          (((2 : ENNReal) ^ (beta / 2) *
            (selectedParentSideHullEnvelope rho
              (bucketShortA label)) ^ (beta / 2)) *
            ((2 : ENNReal) ^ bucketKey * base) ^ (beta - 1)) ≤
        (sourceDensity * geometryLoss) *
          proposition66AInnerFactor rho
            (bucketShortA label) (bucketShortB label) 1 epsilon beta) :
    johnLoss *
          ((blockAt S.activeCoarseFamily P k).fiber.card : ENNReal) ^
            (beta / 2) *
        ((2 : ENNReal) ^ bucketKey * base) ^
          (-(1 - beta / 2)) ≤
      (sourceDensity * geometryLoss) *
        proposition66AInnerFactor rho
          (bucketShortA label) (bucketShortB label) 1 epsilon beta := by
  have hcancel :=
    selectedParent_card_rpow_mul_dyadicLower_inv_rpow_le_sideEnvelope_mul_dyadicGain
      hfineContained S hrho hrhoOne hrhoHalf P k r hr label W base bucketKey
      hband hbaseOne hbaseTop hbeta0 hbetaOne
  calc
    johnLoss *
          ((blockAt S.activeCoarseFamily P k).fiber.card : ENNReal) ^
            (beta / 2) *
        ((2 : ENNReal) ^ bucketKey * base) ^
          (-(1 - beta / 2)) =
        johnLoss *
          (((blockAt S.activeCoarseFamily P k).fiber.card : ENNReal) ^
              (beta / 2) *
            ((2 : ENNReal) ^ bucketKey * base) ^
              (-(1 - beta / 2))) := by ac_rfl
    _ ≤ johnLoss *
        (((2 : ENNReal) ^ (beta / 2) *
          (selectedParentSideHullEnvelope rho
            (bucketShortA label)) ^ (beta / 2)) *
          ((2 : ENNReal) ^ bucketKey * base) ^ (beta - 1)) :=
      mul_le_mul' le_rfl hcancel
    _ ≤ (sourceDensity * geometryLoss) *
        proposition66AInnerFactor rho
          (bucketShortA label) (bucketShortB label) 1 epsilon beta := hscale

#print axioms card_rpow_mul_dyadicLower_inv_rpow_le_two_mul_envelope_rpow_mul_lower_rpow
#print axioms selectedParent_card_rpow_mul_dyadicLower_inv_rpow_le_sideEnvelope_mul_dyadicGain
#print axioms selectedParent_jointOuterCardDensityResidual_of_sideScaleReserve

end
end Family8SelectedParentSideHullDyadicCancellationV1
