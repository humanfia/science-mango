import Family8Grounding.Family8SelectedOccurrenceOptionFrozenLossPowerV1
import Family8Grounding.Family8SelectedOccurrenceWinnerSideBucketLossPowerV1
import Family8Grounding.Family8OuterInnerMismatchHighGammaPackingBridgeV1
import Family8Grounding.Family8SelectedParentCombinedLogLossPowerAbsorptionV3
import Mathlib.Tactic

/-!
# Automatic loss power for the winner-side joint-bucket Equation (32) route

This is only the scalar ledger which is automatic after the endpoint's joint
bucket and winner-side selections.  It absorbs

* the canonical joint fibre/density bucket loss;
* the winner-side bucket loss;
* both occurrences of the selected-parent side-label loss and the certified
  angle-bucket loss;
* the exact Option-block frozen-comparable loss and the literal factor `4`;
* the finite outer/inner mismatch constant; and
* the literal count comparison `countLoss = 2`.

The target is the literal expansion of the consumer's packed coefficient with
`outerLoss = geometryLoss = 1`.  It is stated independently of that large
object-level module so the scalar loss theorem has a small import boundary.
Thus this theorem does not manufacture or absorb either the unknown outer
Equation-(45) loss or the unknown joint-scale geometric loss needed to
construct an `EndpointIdentityLossAwareEq32PaymentAt`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open scoped ENNReal NNReal

namespace Family8WinnerSideJointBucketEndpointPackedEq32LossPowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8FrozenComparableActualAverageMassDensityV1
open Family8GreedyWinnerAutomaticJohnSideBucketV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8OuterInnerMismatchHighGammaPackingBridgeV1
open Family8Prop51JointOccurrenceWeightedSelectionV1
open Family8SelectedOccurrenceOptionFrozenLossPowerV1
open Family8SelectedOccurrenceWinnerSideBucketLossPowerV1
open Family8SelectedParentAngleBucketLogarithmicLossV2
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentCombinedLogLossPowerAbsorptionV3
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankQuantitativeLossV10
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The finite coefficient left after replacing the actual certified angle
bucket loss by twice the canonical angle-ratio logarithm.  The leading `8`
is `2` from the explicit Cordoba bucket, `2` from that comparison, and `2`
inside `selectedOccurrenceFrozenSameQPositiveCarrierLoss`. -/
noncomputable def winnerSideEndpointFiniteAngleMismatchCountConstant
    (beta : Real) : ENNReal :=
  8 * outerInnerMismatchEndpointConstant beta *
    (2 : ENNReal) ^ (1 - beta / 2)

/-- The literal automatic part of the endpoint-packed consumer coefficient.
This is

`jointLoss * winnerSideBucketLoss * winnerSideEndpointPackedLoss 1 1 beta`

with the latter definition expanded.  In particular there is no parameter in
which an outer Equation-(45) or joint-scale geometry loss could be hidden. -/
noncomputable def winnerSideJointBucketEndpointPackedAutomaticLoss
    (S : StickyScaleCover fine delta)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (label : Fin 3 -> Int) (beta : Real) : ENNReal :=
  ((2 * prop51JointOccurrenceLoss (ActiveParentIndex S)
      (Nat.log 2 (Fintype.card (ActiveParentIndex S))) : Nat) : ENNReal) *
    (winnerSideBucketLoss delta : ENNReal) *
    (((4 : ENNReal) *
        ((selectedParentLogarithmicSideBucketLoss delta : ENNReal) *
          (2 * (certifiedPlankThresholdedAngleBucketLoss
            (bucketShortA label) (bucketShortB label) : ENNReal))) *
        (((frozenComparableLoss (ActiveParentIndex S)
            (Option (Fin (blocks S.activeCoarseFamily P).length)) : ENNReal) *
          (selectedParentLogarithmicSideBucketLoss delta : ENNReal)) * 2)) *
      (outerInnerMismatchEndpointConstant beta *
        (2 : ENNReal) ^ (1 - beta / 2)))

/-- One explicit small-scale threshold assembled only from the existing loss
power thresholds.  One quarter of `lossEta` is assigned respectively to the
joint/frozen loss, the winner-side loss, the second side-label loss hidden in
the positive-carrier payment, and the combined side/angle logarithms. -/
noncomputable def winnerSideJointBucketEndpointPackedAutomaticLossThreshold
    (lossEta beta : Real) : NNReal :=
  min
    (selectedOccurrenceJointFrozenExternalLossThreshold (lossEta / 4))
    (min
      (selectedParentLogarithmicSideBucketAbsorptionThreshold
        1 (lossEta / 4))
      (min
        (selectedParentLogarithmicSideBucketAbsorptionThreshold
          1 ((lossEta / 4) / 2))
        (selectedParentLogarithmicSideBucketAbsorptionThreshold
          (winnerSideEndpointFiniteAngleMismatchCountConstant beta)
          ((lossEta / 4) / 4))))

theorem winnerSideJointBucketEndpointPackedAutomaticLossThreshold_pos
    (lossEta beta : Real) :
    0 < winnerSideJointBucketEndpointPackedAutomaticLossThreshold
      lossEta beta := by
  unfold winnerSideJointBucketEndpointPackedAutomaticLossThreshold
  exact lt_min
    (selectedOccurrenceJointFrozenExternalLossThreshold_pos _)
    (lt_min
      (selectedParentLogarithmicSideBucketAbsorptionThreshold_pos _ _)
      (lt_min
        (selectedParentLogarithmicSideBucketAbsorptionThreshold_pos _ _)
        (selectedParentLogarithmicSideBucketAbsorptionThreshold_pos _ _)))

/-- Every genuinely automatic finite/logarithmic coefficient in the
winner-side joint-bucket consumer is an arbitrarily small negative power of
the source scale.

The angle premise is the scalar output of
`selectedParent_angleBucketLoss_le_logarithmic` for the selected inner label.
The displayed packed loss has both external analytic factors specialized to one;
unknown outer Equation-(45) and joint-scale geometric powers therefore remain
outside this statement. -/
theorem jointWinnerSide_endpointPackedAutomaticLoss_le_rpow
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family delta)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (hactiveParent : 0 < Fintype.card (ActiveParentIndex S))
    (label : Fin 3 -> Int) (beta : Real)
    {lossEta : Real} (hlossEta : 0 < lossEta)
    (hangle :
      (certifiedPlankThresholdedAngleBucketLoss
          (bucketShortA label) (bucketShortB label) : ENNReal) <=
        2 * (threeSideDyadicRatioLoss
          (11943936 / (delta : Real)) : ENNReal))
    (hsmall : delta <=
      winnerSideJointBucketEndpointPackedAutomaticLossThreshold
        lossEta beta) :
    winnerSideJointBucketEndpointPackedAutomaticLoss S P label beta <=
      (delta : ENNReal) ^ (-lossEta) := by
  let etaQuarter : Real := lossEta / 4
  let jointLoss : ENNReal :=
    ((2 * prop51JointOccurrenceLoss (ActiveParentIndex S)
      (Nat.log 2 (Fintype.card (ActiveParentIndex S))) : Nat) : ENNReal)
  let frozenLoss : ENNReal :=
    (frozenComparableLoss (ActiveParentIndex S)
      (Option (Fin (blocks S.activeCoarseFamily P).length)) : ENNReal)
  let winnerLoss : ENNReal := (winnerSideBucketLoss delta : ENNReal)
  let sideLoss : ENNReal :=
    (selectedParentLogarithmicSideBucketLoss delta : ENNReal)
  let angleLoss : ENNReal :=
    (certifiedPlankThresholdedAngleBucketLoss
      (bucketShortA label) (bucketShortB label) : ENNReal)
  let ratioLoss : ENNReal :=
    (threeSideDyadicRatioLoss (11943936 / (delta : Real)) : ENNReal)
  let mismatchCount : ENNReal :=
    outerInnerMismatchEndpointConstant beta *
      (2 : ENNReal) ^ (1 - beta / 2)
  let fixedConstant : ENNReal :=
    winnerSideEndpointFiniteAngleMismatchCountConstant beta
  have hetaQuarter : 0 < etaQuarter := by
    dsimp only [etaQuarter]
    positivity
  have hjointSmall : delta <=
      selectedOccurrenceJointFrozenExternalLossThreshold etaQuarter := by
    exact hsmall.trans (by
      unfold winnerSideJointBucketEndpointPackedAutomaticLossThreshold
      exact min_le_left _ _)
  have hwinnerSmall : delta <=
      selectedParentLogarithmicSideBucketAbsorptionThreshold 1 etaQuarter := by
    exact hsmall.trans (by
      unfold winnerSideJointBucketEndpointPackedAutomaticLossThreshold
      exact (min_le_right _ _).trans (min_le_left _ _))
  have hsideSmall : delta <=
      selectedParentLogarithmicSideBucketAbsorptionThreshold
        1 (etaQuarter / 2) := by
    exact hsmall.trans (by
      unfold winnerSideJointBucketEndpointPackedAutomaticLossThreshold
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
  have hangleSmallRaw : delta <=
      selectedParentLogarithmicSideBucketAbsorptionThreshold
        fixedConstant (etaQuarter / 4) := by
    exact hsmall.trans (by
      unfold winnerSideJointBucketEndpointPackedAutomaticLossThreshold
      simpa only [fixedConstant, etaQuarter] using
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_right _ _))))
  have hdeltaDivTwo : delta / 2 <= delta := by
    exact div_le_self (by positivity : (0 : NNReal) <= delta)
      (by norm_num : (1 : NNReal) <= 2)
  have hangleSmall : delta / 2 <=
      selectedParentLogarithmicSideBucketAbsorptionThreshold
        fixedConstant (etaQuarter / 4) :=
    hdeltaDivTwo.trans hangleSmallRaw
  have hjointFrozen : (jointLoss * frozenLoss) * 4 <=
      (delta : ENNReal) ^ (-etaQuarter) := by
    simpa only [jointLoss, frozenLoss] using
      (selectedOccurrenceJointFrozenExternalLoss_le_rpow
        D hD S P hactiveParent hetaQuarter hjointSmall)
  have hwinner : winnerLoss <=
      (delta : ENNReal) ^ (-etaQuarter) := by
    simpa only [winnerLoss] using
      (winnerSideBucketLoss_le_rpow hD.delta_pos hetaQuarter hwinnerSmall)
  have hside : sideLoss <=
      (delta : ENNReal) ^ (-etaQuarter) := by
    simpa only [sideLoss] using
      (selectedParentLogarithmicSideBucketLoss_le_rpow
        hetaQuarter hD.delta_pos hwinnerSmall)
  have hmismatchFinite : outerInnerMismatchEndpointConstant beta ≠ ∞ := by
    unfold outerInnerMismatchEndpointConstant
    exact ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num))
      (ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num))
  have hcountFinite : (2 : ENNReal) ^ (1 - beta / 2) ≠ ∞ := by
    exact ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)
  have hfixedFinite : fixedConstant ≠ ∞ := by
    dsimp only [fixedConstant,
      winnerSideEndpointFiniteAngleMismatchCountConstant]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) hmismatchFinite) hcountFinite
  have hcombined : sideLoss * (fixedConstant * ratioLoss) <=
      (delta : ENNReal) ^ (-etaQuarter) := by
    simpa only [sideLoss, fixedConstant, ratioLoss] using
      (fixedConstant_mul_combinedSelectedParentLogLoss_le_rpow
        hfixedFinite hetaQuarter hD.delta_pos hD.delta_le_half hsideSmall
          hangleSmall)
  have hangleScaled : 2 * angleLoss <= 4 * ratioLoss := by
    calc
      2 * angleLoss <= 2 * (2 * ratioLoss) := by
        exact mul_le_mul' le_rfl (by simpa only [angleLoss, ratioLoss] using hangle)
      _ = 4 * ratioLoss := by ring
  have hinner : sideLoss * (((2 * angleLoss) * 2) * mismatchCount) <=
      (delta : ENNReal) ^ (-etaQuarter) := by
    apply le_trans (b := sideLoss * (fixedConstant * ratioLoss))
    · apply mul_le_mul' le_rfl
      calc
        ((2 * angleLoss) * 2) * mismatchCount <=
            (8 * ratioLoss) * mismatchCount := by
          apply mul_le_mul' ?_ le_rfl
          calc
            (2 * angleLoss) * 2 <= (4 * ratioLoss) * 2 :=
              mul_le_mul' hangleScaled le_rfl
            _ = 8 * ratioLoss := by ring
        _ = fixedConstant * ratioLoss := by
          dsimp only [fixedConstant,
            winnerSideEndpointFiniteAngleMismatchCountConstant, mismatchCount]
          ac_rfl
    · exact hcombined
  have hdelta0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  calc
    winnerSideJointBucketEndpointPackedAutomaticLoss S P label beta =
      ((jointLoss * frozenLoss) * 4 * winnerLoss) *
        sideLoss * (sideLoss * (((2 * angleLoss) * 2) * mismatchCount)) := by
          dsimp only [winnerSideJointBucketEndpointPackedAutomaticLoss,
            jointLoss, frozenLoss, winnerLoss, sideLoss, angleLoss,
            mismatchCount]
          ac_rfl
    _ <= ((((delta : ENNReal) ^ (-etaQuarter)) *
          ((delta : ENNReal) ^ (-etaQuarter))) *
        ((delta : ENNReal) ^ (-etaQuarter))) *
      ((delta : ENNReal) ^ (-etaQuarter)) :=
      mul_le_mul' (mul_le_mul' (mul_le_mul' hjointFrozen hwinner) hside) hinner
    _ = (delta : ENNReal) ^ (-lossEta) := by
      rw [<- ENNReal.rpow_add _ _ hdelta0 ENNReal.coe_ne_top]
      rw [<- ENNReal.rpow_add _ _ hdelta0 ENNReal.coe_ne_top]
      rw [<- ENNReal.rpow_add _ _ hdelta0 ENNReal.coe_ne_top]
      congr 1
      dsimp only [etaQuarter]
      ring

/-- The complete automatic coefficient needed when the endpoint source
average is transported to the refinement consumed by the packed Equation
(32) theorem.  The leading frozen-comparable loss is a second, genuinely
distinct occurrence: it pays source-average retention.  The occurrence
inside `winnerSideJointBucketEndpointPackedAutomaticLoss` instead pays the
positive-carrier/source-density comparison. -/
noncomputable def winnerSideJointBucketEndpointPackedAutomaticSourceLoss
    (S : StickyScaleCover fine delta)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (label : Fin 3 -> Int) (beta : Real) : ENNReal :=
  (frozenComparableLoss (ActiveParentIndex S)
      (Option (Fin (blocks S.activeCoarseFamily P).length)) : ENNReal) *
    winnerSideJointBucketEndpointPackedAutomaticLoss S P label beta

/-- Explicit threshold for the full endpoint-source coefficient.  Half of
the requested exponent pays the already packed automatic ledger and half
pays the additional frozen source-average retention. -/
noncomputable def
    winnerSideJointBucketEndpointPackedAutomaticSourceLossThreshold
    (lossEta beta : Real) : NNReal :=
  min
    (winnerSideJointBucketEndpointPackedAutomaticLossThreshold
      (lossEta / 2) beta)
    (selectedOccurrenceOptionFrozenLossThreshold (lossEta / 2))

theorem
    winnerSideJointBucketEndpointPackedAutomaticSourceLossThreshold_pos
    (lossEta beta : Real) :
    0 < winnerSideJointBucketEndpointPackedAutomaticSourceLossThreshold
      lossEta beta := by
  unfold winnerSideJointBucketEndpointPackedAutomaticSourceLossThreshold
  exact lt_min
    (winnerSideJointBucketEndpointPackedAutomaticLossThreshold_pos _ _)
    (selectedOccurrenceOptionFrozenLossThreshold_pos _)

/-- All automatic losses needed to return the packed consumer from its
selected refinement to the original endpoint source are an arbitrarily
small negative source-scale power.  In particular the two distinct
frozen-comparable payments are both displayed and neither external analytic
factor is present. -/
theorem jointWinnerSide_endpointPackedAutomaticSourceLoss_le_rpow
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family delta)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (hactiveParent : 0 < Fintype.card (ActiveParentIndex S))
    (label : Fin 3 -> Int) (beta : Real)
    {lossEta : Real} (hlossEta : 0 < lossEta)
    (hangle :
      (certifiedPlankThresholdedAngleBucketLoss
          (bucketShortA label) (bucketShortB label) : ENNReal) <=
        2 * (threeSideDyadicRatioLoss
          (11943936 / (delta : Real)) : ENNReal))
    (hsmall : delta <=
      winnerSideJointBucketEndpointPackedAutomaticSourceLossThreshold
        lossEta beta) :
    winnerSideJointBucketEndpointPackedAutomaticSourceLoss S P label beta <=
      (delta : ENNReal) ^ (-lossEta) := by
  have hhalf : 0 < lossEta / 2 := by positivity
  have hpacked :
      winnerSideJointBucketEndpointPackedAutomaticLoss S P label beta <=
        (delta : ENNReal) ^ (-(lossEta / 2)) := by
    exact jointWinnerSide_endpointPackedAutomaticLoss_le_rpow
      D hD S P hactiveParent label beta hhalf hangle
        (hsmall.trans (min_le_left _ _))
  have hfrozen :
      (frozenComparableLoss (ActiveParentIndex S)
          (Option (Fin (blocks S.activeCoarseFamily P).length)) : ENNReal) <=
        (delta : ENNReal) ^ (-(lossEta / 2)) := by
    exact selectedOccurrenceOptionFrozenComparableLoss_le_rpow
      D hD S P hactiveParent hhalf
        (hsmall.trans (min_le_right _ _))
  have hdelta0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  calc
    winnerSideJointBucketEndpointPackedAutomaticSourceLoss S P label beta <=
        (delta : ENNReal) ^ (-(lossEta / 2)) *
          (delta : ENNReal) ^ (-(lossEta / 2)) := by
      unfold winnerSideJointBucketEndpointPackedAutomaticSourceLoss
      exact mul_le_mul' hfrozen hpacked
    _ = (delta : ENNReal) ^ (-lossEta) := by
      rw [<- ENNReal.rpow_add _ _ hdelta0 ENNReal.coe_ne_top]
      congr 1
      ring

#print axioms winnerSideJointBucketEndpointPackedAutomaticLossThreshold_pos
#print axioms jointWinnerSide_endpointPackedAutomaticLoss_le_rpow
#print axioms
  winnerSideJointBucketEndpointPackedAutomaticSourceLossThreshold_pos
#print axioms jointWinnerSide_endpointPackedAutomaticSourceLoss_le_rpow

end
end Family8WinnerSideJointBucketEndpointPackedEq32LossPowerV1
