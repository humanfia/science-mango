import Family8Grounding.Family8WinnerSideJointBucketLargeBWeightedOverlapConsumerV1
import Mathlib.Tactic

/-!
# Exact scalar seam for the weighted-overlap large-b route

The weighted-overlap consumer asks for an aggregate outer overlap factor
`outerBound` and a whole outer-times-inner joint budget.  Once the already
isolated same-q inner scale has been paid, the latter reduces to one scalar
comparison.  This file records that reduction without a carrier floor and
without a lower bound on every shaded member.

The genuinely missing large-b producer should choose `outerBound` and prove
both `SelectedNormalizedOuterWeightedOverlapBudgetAt` and
`WinnerSideLargeBWeightedOverlapOuterInnerPaymentAt`.  Taking
`outerBound = Rside.card` is always available for the first condition, but it
strengthens the second condition by a full linear occurrence count.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8WinnerSideJointBucketLargeBWeightedOverlapJointScalarReductionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family8GreedyWinnerAutomaticJohnSideBucketV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8WinnerSideJointBucketLargeBWeightedOverlapConsumerV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

/-- Pure ordered-semiring reduction.  It deliberately does not cancel the
inner residual, so zero and infinity edge cases remain harmless. -/
theorem jointOuterInner_of_innerScale_and_outerPayment
    {johnLoss tubesPerPlank outerBound innerResidual sourceDensity
      geometryLoss densityLoss outerFactor innerFactor : ENNReal}
    (hinner : johnLoss * innerResidual <=
      (sourceDensity * geometryLoss) * innerFactor)
    (houter : tubesPerPlank * outerBound <=
      (densityLoss * outerFactor) * innerResidual) :
    johnLoss * tubesPerPlank * outerBound <=
      (sourceDensity * geometryLoss * densityLoss) *
        (outerFactor * innerFactor) := by
  calc
    johnLoss * tubesPerPlank * outerBound =
        johnLoss * (tubesPerPlank * outerBound) := by ac_rfl
    _ <= johnLoss * ((densityLoss * outerFactor) * innerResidual) :=
      mul_le_mul' le_rfl houter
    _ = (densityLoss * outerFactor) * (johnLoss * innerResidual) := by
      ac_rfl
    _ <= (densityLoss * outerFactor) *
        ((sourceDensity * geometryLoss) * innerFactor) :=
      mul_le_mul' le_rfl hinner
    _ = (sourceDensity * geometryLoss * densityLoss) *
        (outerFactor * innerFactor) := by ac_rfl

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {sourceFine : UniformTubeFamily delta index}

/-- The one large-b-specific scalar still required after the same-q inner
scale has been paid.  Unlike a separate outer-factor bound, this condition
keeps the actual aggregate overlap factor coupled to the inner residual. -/
def WinnerSideLargeBWeightedOverlapOuterInnerPaymentAt
    (S : StickyScaleCover sourceFine rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (Rside : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (q : Fin (blocks S.activeCoarseFamily P).length)
    (labelOuter _labelInner : Fin 3 -> Int)
    (outerBound outerKT densityLoss innerResidual : ENNReal)
    (epsilon gamma : Real) : Prop :=
  ((blockAt S.activeCoarseFamily P q).fiber.card : ENNReal) * outerBound <=
    (densityLoss *
      proposition66AOuterFactor rho
        (bucketShortA labelOuter) (bucketShortB labelOuter)
        Rside.card outerKT epsilon gamma) * innerResidual

/-- Exact specialization to the existing large-b joint-budget predicate.
The first premise is precisely the same-q inner-scale estimate; the second is
the only remaining outer/inner scalar payment. -/
theorem winnerSideLargeBWeightedOverlapJointBudgetAt_of_innerScale_and_outerPayment
    (S : StickyScaleCover sourceFine rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (Rside : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (source : Shading S.activeCoarseFamily)
    (q : Fin (blocks S.activeCoarseFamily P).length)
    (labelOuter labelInner : Fin 3 -> Int)
    (outerBound outerKT geometryLoss densityLoss innerResidual : ENNReal)
    (epsilon gamma : Real)
    (hinner : winnerSideLargeBWeightedOverlapJohnLoss * innerResidual <=
      (source.shadingDensity * geometryLoss) *
        proposition66AInnerFactor rho
          (bucketShortA labelInner) (bucketShortB labelInner)
          (blockAt S.activeCoarseFamily P q).fiber.card epsilon gamma)
    (houter : WinnerSideLargeBWeightedOverlapOuterInnerPaymentAt
      S P Rside q labelOuter labelInner outerBound outerKT densityLoss
        innerResidual epsilon gamma) :
    WinnerSideLargeBWeightedOverlapJointBudgetAt
      S P Rside source q labelOuter labelInner outerBound outerKT
        geometryLoss densityLoss epsilon gamma := by
  unfold WinnerSideLargeBWeightedOverlapJointBudgetAt
  apply jointOuterInner_of_innerScale_and_outerPayment hinner
  simpa only [WinnerSideLargeBWeightedOverlapOuterInnerPaymentAt] using
    houter

#print axioms jointOuterInner_of_innerScale_and_outerPayment
#print axioms WinnerSideLargeBWeightedOverlapOuterInnerPaymentAt
#print axioms
  winnerSideLargeBWeightedOverlapJointBudgetAt_of_innerScale_and_outerPayment

end
end Family8WinnerSideJointBucketLargeBWeightedOverlapJointScalarReductionV1
