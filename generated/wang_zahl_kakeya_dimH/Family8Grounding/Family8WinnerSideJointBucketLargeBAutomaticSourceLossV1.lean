import Family8Grounding.Family8SelectedOccurrenceOptionFrozenLossPowerV1
import Family8Grounding.Family8SelectedOccurrenceWinnerSideBucketLossPowerV1
import Mathlib.Tactic

/-!
# Automatic source loss for the direct winner-side large-`b` route

This file absorbs exactly the losses introduced before the direct large-`b`
Equation-(32) estimate: the joint occurrence bucket, the winner-side bucket,
the source-to-refinement frozen comparison, and the literal factor `4` in the
outer/inner product.  The outer and inner analytic losses, the two-label scale
mismatch, the count comparison, and the Section-Eight coefficient remain
separate.
-/

open scoped ENNReal NNReal

namespace Family8WinnerSideJointBucketLargeBAutomaticSourceLossV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8FrozenComparableActualAverageMassDensityV1
open Family8GreedyWinnerAutomaticJohnSideBucketV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8Prop51JointOccurrenceWeightedSelectionV1
open Family8SelectedOccurrenceOptionFrozenLossPowerV1
open Family8SelectedOccurrenceWinnerSideBucketLossPowerV1
open Family8SelectedParentJohnPlankQuantitativeLossV10
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- A source-scale threshold which gives half of the requested exponent to the
joint/frozen/four product and half to the winner-side bucket. -/
noncomputable def winnerSideJointBucketLargeBAutomaticSourceLossThreshold
    (lossEta : Real) : NNReal :=
  min
    (selectedOccurrenceJointFrozenExternalLossThreshold (lossEta / 2))
    (selectedParentLogarithmicSideBucketAbsorptionThreshold
      1 (lossEta / 2))

theorem winnerSideJointBucketLargeBAutomaticSourceLossThreshold_pos
    (lossEta : Real) :
    0 < winnerSideJointBucketLargeBAutomaticSourceLossThreshold lossEta := by
  unfold winnerSideJointBucketLargeBAutomaticSourceLossThreshold
  exact lt_min
    (selectedOccurrenceJointFrozenExternalLossThreshold_pos _)
    (selectedParentLogarithmicSideBucketAbsorptionThreshold_pos _ _)

/-- The exact automatic source coefficient of the direct large-`b` route is
an arbitrarily small negative power of the source scale.  No inner, mismatch,
count, or Section-Eight factor is included. -/
theorem winnerSideJointBucketLargeBAutomaticSourceLoss_le_rpow
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family delta)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (hactiveParent : 0 < Fintype.card (ActiveParentIndex S))
    {lossEta : Real} (hlossEta : 0 < lossEta)
    (hsmall : delta <=
      winnerSideJointBucketLargeBAutomaticSourceLossThreshold lossEta) :
    ((((2 * prop51JointOccurrenceLoss (ActiveParentIndex S)
          (Nat.log 2 (Fintype.card (ActiveParentIndex S))) : Nat) : ENNReal) *
        (winnerSideBucketLoss delta : ENNReal) *
        (frozenComparableLoss (ActiveParentIndex S)
          (Option (Fin (blocks S.activeCoarseFamily P).length)) : ENNReal)) *
      4 <= (delta : ENNReal) ^ (-lossEta)) := by
  let halfEta : Real := lossEta / 2
  let jointLoss : ENNReal :=
    ((2 * prop51JointOccurrenceLoss (ActiveParentIndex S)
      (Nat.log 2 (Fintype.card (ActiveParentIndex S))) : Nat) : ENNReal)
  let winnerLoss : ENNReal := (winnerSideBucketLoss delta : ENNReal)
  let frozenLoss : ENNReal :=
    (frozenComparableLoss (ActiveParentIndex S)
      (Option (Fin (blocks S.activeCoarseFamily P).length)) : ENNReal)
  change (jointLoss * winnerLoss * frozenLoss) * 4 <=
    (delta : ENNReal) ^ (-lossEta)
  have hhalfEta : 0 < halfEta := by
    dsimp only [halfEta]
    positivity
  have hjointFrozenFour : (jointLoss * frozenLoss) * 4 <=
      (delta : ENNReal) ^ (-halfEta) := by
    simpa only [jointLoss, frozenLoss] using
      (selectedOccurrenceJointFrozenExternalLoss_le_rpow
        D hD S P hactiveParent hhalfEta
          (hsmall.trans (by
            unfold winnerSideJointBucketLargeBAutomaticSourceLossThreshold
            exact min_le_left _ _)))
  have hwinner :
      winnerLoss <= (delta : ENNReal) ^ (-halfEta) := by
    simpa only [winnerLoss] using
      (winnerSideBucketLoss_le_rpow hD.delta_pos hhalfEta
        (hsmall.trans (by
          unfold winnerSideJointBucketLargeBAutomaticSourceLossThreshold
          exact min_le_right _ _)))
  have hdelta0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  calc
    (jointLoss * winnerLoss * frozenLoss) * 4 =
        ((jointLoss * frozenLoss) * 4) * winnerLoss := by
      ac_rfl
    _ <= (delta : ENNReal) ^ (-halfEta) *
        (delta : ENNReal) ^ (-halfEta) :=
      mul_le_mul' hjointFrozenFour hwinner
    _ = (delta : ENNReal) ^ (-lossEta) := by
      rw [<- ENNReal.rpow_add _ _ hdelta0 ENNReal.coe_ne_top]
      congr 1
      dsimp only [halfEta]
      ring

#print axioms winnerSideJointBucketLargeBAutomaticSourceLossThreshold_pos
#print axioms winnerSideJointBucketLargeBAutomaticSourceLoss_le_rpow

end
end Family8WinnerSideJointBucketLargeBAutomaticSourceLossV1
