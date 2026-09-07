import Family8Grounding.Family8ComparableRLocalKTWholeEq32ScalarV1
import Family8Grounding.Family8SelectedParentSideHullDyadicActualCountScalarV1
import Mathlib.Tactic

/-!
# The literal block count introduces no extra joint-scale gate

The Proposition 6.6(A) inner factor contains the exact power
`m^(1-beta/2)`.  Thus a count-one scale payment can be multiplied by this
same power to give the actual-count payment required by the selected-side
hull route.  This file records that algebra and then specializes it to the
literal selected greedy block.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentSideHullDyadicActualCountGateV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family8Prop51JointOccurrenceWeightedSelectionV1
open Family8ComparableRLocalKTWholeEq32ScalarV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentSideHullDyadicActualCountScalarV1
open Family8SelectedParentSideHullReserveProducerV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1

noncomputable section

/-- Multiplying a count-one scale payment by the exact count power gives the
actual-count payment.  No comparison between the literal count and an
adaptive cap is used. -/
theorem jointScale_actualCount_of_countOne
    {delta a b : NNReal} {m : Nat}
    {johnLoss residual sourceDensity geometryLoss : ENNReal}
    {epsilon beta : Real}
    (hbetaOne : beta <= 1)
    (hscale :
      johnLoss * residual <=
        (sourceDensity * geometryLoss) *
          proposition66AInnerFactor delta a b 1 epsilon beta) :
    johnLoss *
          (residual * (m : ENNReal) ^ (1 - beta / 2)) <=
      (sourceDensity * geometryLoss) *
        proposition66AInnerFactor delta a b m epsilon beta := by
  have hcount := proposition66AInnerFactor_eq_countOne_mul_card_rpow
    delta a b m epsilon beta hbetaOne
  calc
    johnLoss * (residual * (m : ENNReal) ^ (1 - beta / 2)) =
        (johnLoss * residual) *
          (m : ENNReal) ^ (1 - beta / 2) := by ac_rfl
    _ <= ((sourceDensity * geometryLoss) *
          proposition66AInnerFactor delta a b 1 epsilon beta) *
        (m : ENNReal) ^ (1 - beta / 2) :=
      mul_le_mul' hscale le_rfl
    _ = (sourceDensity * geometryLoss) *
        proposition66AInnerFactor delta a b m epsilon beta := by
      rw [hcount]
      ac_rfl

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Literal selected-parent specialization.  The only remaining analytic
input is the count-one scale ledger; the block cardinality is inserted and
cancelled automatically by the exact inner-factor count identity. -/
theorem selectedParent_twoScale_actualCount_hscalar_of_sideEnvelope_of_countOne
    (hfineContained : forall i, (fine.tubes i).carrier <=
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1) (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (sourceDensity geometryLoss johnLoss : ENNReal)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label})
    (base : ENNReal) (bucketKey : Nat)
    (hband : InENNRealDyadicBand base bucketKey
      (blockDensity S.activeCoarseFamily
        (blockAt S.activeCoarseFamily P k)))
    (hbaseOne : 1 <= base) (hbaseTop : base ≠ ∞)
    {epsilon beta : Real} (hbeta0 : 0 <= beta) (hbetaOne : beta <= 1)
    (hscale :
      johnLoss *
          (((2 : ENNReal) ^ (beta / 2) *
                (selectedParentSideHullEnvelope rho
                  (bucketShortA label)) ^ (beta / 2)) *
            ((2 : ENNReal) ^ bucketKey * base) ^ (beta - 1)) <=
        (sourceDensity * geometryLoss) *
          proposition66AInnerFactor rho
            (bucketShortA label) (bucketShortB label) 1 epsilon beta) :
    johnLoss *
          ((blockAt S.activeCoarseFamily P k).fiber.card : ENNReal) *
        ((2 : ENNReal) ^ bucketKey * base) ^
          (-(1 - beta / 2)) <=
      (sourceDensity * geometryLoss) *
        proposition66AInnerFactor rho
          (bucketShortA label) (bucketShortB label)
          (blockAt S.activeCoarseFamily P k).fiber.card epsilon beta := by
  apply selectedParent_twoScale_actualCount_hscalar_of_sideEnvelope
    hfineContained S hrho hrhoOne hrhoHalf P k
      sourceDensity geometryLoss johnLoss r hr label W base bucketKey
      hband hbaseOne hbaseTop hbeta0 hbetaOne
  exact jointScale_actualCount_of_countOne hbetaOne hscale

#print axioms jointScale_actualCount_of_countOne
#print axioms
  selectedParent_twoScale_actualCount_hscalar_of_sideEnvelope_of_countOne

end
end Family8SelectedParentSideHullDyadicActualCountGateV1
