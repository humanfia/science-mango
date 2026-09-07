import Family8Grounding.Family8SelectedParentSideHullDyadicCancellationV1
import Mathlib.Tactic

/-!
# Actual-count scalar from the selected-side dyadic hull cancellation

The two-scale whole-product producer keeps the literal inner count `m`.
Accordingly, this file does not ask for an independent count-one hull bound.
It splits

`m = m^(beta/2) * m^(1-beta/2)`

only inside one joint scalar: the first power is paid by the same-block hull
and the exact outer `d0` reserve, while the second power stays beside the
actual-count inner factor.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentSideHullDyadicActualCountScalarV1

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
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentSideHullDyadicCancellationV1
open Family8SelectedParentSideHullReserveProducerV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1

noncomputable section

/-- Pure actual-count lifting.  The premise is deliberately one joint
inequality at the actual count; no independent `Inner(1)` payment occurs. -/
theorem actualCount_inverseDensity_hscalar_of_cardRpowResidual
    {delta a b : NNReal} {m : Nat}
    {d0 residual johnLoss sourceDensity geometryLoss : ENNReal}
    {epsilon beta : Real}
    (hm0 : (m : ENNReal) ≠ 0)
    (hresidual :
      (m : ENNReal) ^ (beta / 2) *
          d0 ^ (-(1 - beta / 2)) ≤ residual)
    (hjointScale :
      johnLoss *
          (residual * (m : ENNReal) ^ (1 - beta / 2)) ≤
        (sourceDensity * geometryLoss) *
          proposition66AInnerFactor delta a b m epsilon beta) :
    johnLoss * (m : ENNReal) * d0 ^ (-(1 - beta / 2)) ≤
      (sourceDensity * geometryLoss) *
        proposition66AInnerFactor delta a b m epsilon beta := by
  have hmTop : (m : ENNReal) ≠ ∞ := by simp
  have hmSplit : (m : ENNReal) =
      (m : ENNReal) ^ (beta / 2) *
        (m : ENNReal) ^ (1 - beta / 2) := by
    calc
      (m : ENNReal) = (m : ENNReal) ^ (1 : Real) :=
        (ENNReal.rpow_one _).symm
      _ = (m : ENNReal) ^
          ((beta / 2) + (1 - beta / 2)) := by ring_nf
      _ = (m : ENNReal) ^ (beta / 2) *
          (m : ENNReal) ^ (1 - beta / 2) := by
        rw [ENNReal.rpow_add _ _ hm0 hmTop]
  have hmSplitMul := congrArg
    (fun x : ENNReal =>
      johnLoss * x * d0 ^ (-(1 - beta / 2))) hmSplit
  calc
    johnLoss * (m : ENNReal) * d0 ^ (-(1 - beta / 2)) =
        johnLoss *
          ((m : ENNReal) ^ (beta / 2) *
            (m : ENNReal) ^ (1 - beta / 2)) *
          d0 ^ (-(1 - beta / 2)) := hmSplitMul
    _ = johnLoss *
        (((m : ENNReal) ^ (beta / 2) *
            d0 ^ (-(1 - beta / 2))) *
          (m : ENNReal) ^ (1 - beta / 2)) := by
      ac_rfl
    _ ≤ johnLoss *
        (residual * (m : ENNReal) ^ (1 - beta / 2)) :=
      mul_le_mul' le_rfl (mul_le_mul' hresidual le_rfl)
    _ ≤ (sourceDensity * geometryLoss) *
        proposition66AInnerFactor delta a b m epsilon beta := hjointScale

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Literal selected-parent specialization for the hscalar of the two-scale
actual-count joint producer.  The inner count is exactly the selected block
cardinality, and the surviving `d0^(beta-1)` gain stays in the one joint
scale premise. -/
theorem selectedParent_twoScale_actualCount_hscalar_of_sideEnvelope
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
    (hjointScale :
      johnLoss *
          ((((2 : ENNReal) ^ (beta / 2) *
                (selectedParentSideHullEnvelope rho
                  (bucketShortA label)) ^ (beta / 2)) *
              ((2 : ENNReal) ^ bucketKey * base) ^ (beta - 1)) *
            ((blockAt S.activeCoarseFamily P k).fiber.card : ENNReal) ^
              (1 - beta / 2)) ≤
        (sourceDensity * geometryLoss) *
          proposition66AInnerFactor rho
            (bucketShortA label) (bucketShortB label)
            (blockAt S.activeCoarseFamily P k).fiber.card epsilon beta) :
    johnLoss *
          ((blockAt S.activeCoarseFamily P k).fiber.card : ENNReal) *
        ((2 : ENNReal) ^ bucketKey * base) ^
          (-(1 - beta / 2)) ≤
      (sourceDensity * geometryLoss) *
        proposition66AInnerFactor rho
          (bucketShortA label) (bucketShortB label)
          (blockAt S.activeCoarseFamily P k).fiber.card epsilon beta := by
  let B := (blockAt S.activeCoarseFamily P k).fiber
  have hBnonempty : B.Nonempty := by
    exact ⟨W.1.1, W.1.2⟩
  have hcard0 : (B.card : ENNReal) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hBnonempty
  have hresidual :=
    selectedParent_card_rpow_mul_dyadicLower_inv_rpow_le_sideEnvelope_mul_dyadicGain
      hfineContained S hrho hrhoOne hrhoHalf P k r hr label W base bucketKey
      hband hbaseOne hbaseTop hbeta0 hbetaOne
  exact actualCount_inverseDensity_hscalar_of_cardRpowResidual
    (delta := rho) (a := bucketShortA label) (b := bucketShortB label)
    (m := B.card) (d0 := (2 : ENNReal) ^ bucketKey * base)
    (residual :=
      ((2 : ENNReal) ^ (beta / 2) *
          (selectedParentSideHullEnvelope rho
            (bucketShortA label)) ^ (beta / 2)) *
        ((2 : ENNReal) ^ bucketKey * base) ^ (beta - 1))
    (johnLoss := johnLoss) (sourceDensity := sourceDensity)
    (geometryLoss := geometryLoss) (epsilon := epsilon) (beta := beta)
    (by simpa only [B] using hcard0)
    (by simpa only [B] using hresidual)
    (by simpa only [B] using hjointScale)

#print axioms actualCount_inverseDensity_hscalar_of_cardRpowResidual
#print axioms selectedParent_twoScale_actualCount_hscalar_of_sideEnvelope

end
end Family8SelectedParentSideHullDyadicActualCountScalarV1
