import Family8Grounding.Family8EndpointIdentityCorrelatedRecomputedThirdBaseBudgetV1
import Family8Grounding.Family8EndpointIdentityHighGammaParentwiseLongCoreTrueSplitEtaDSOV3
import Family8Grounding.Family8FirstCrossingRecomputedThirdFullLossPowerV1
import Mathlib.Tactic

/-!
# Literal correlated third-loss producer

The full B2 base and the third-loss field use the same literal endpoint cover
and the same card-scale power.  This module first forms the scalar residual
internally from the correlated source cancellation; it never asks for a
standalone Katz--Tao power.  The fixed third normalization is then absorbed at
the stage-local exponent eta(stage) / 4.

The public conclusion is exactly the literal field consumed by Parentwise DSO
V3.  Neither the scalar base nor a separate third-exponent budget is exposed.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8EndpointIdentityCorrelatedLiteralThirdLossProducerV1

open Submission.Kakeya.ConvexGeometry
open Family8EighthNormalizedSelectedFrostmanThirdFactorV3
open Family8EndpointIdentityCorrelatedRecomputedThirdBaseBudgetV1
open Family8EndpointIdentityHighGammaParentwiseLongCoreTrueSplitEtaDSOV3
open Family8FirstCrossingRecomputedThirdFixedLossPowerV3
open Family8FirstCrossingRecomputedThirdFullLossPowerV1
open Family8FullRefinementActualDatumV1
open Family8IdentitySourceFrostmanKatzTaoCardScaleCancellationV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8RelativeScaleFixedNuEndpointOrchestrationV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- One raw threshold supplies both finite absorptions used internally:
the correlated ceiling at the chosen absorption exponent and the literal third
normalization at the stage-local quarter exponent. -/
def endpointIdentityCorrelatedLiteralThirdLossThreshold
    (P : ParameterLadder epsilon0 beta gamma)
    (absorbEta thirdEta targetEpsilon : Real) (stage : Nat) : NNReal :=
  min
    (endpointCorrelatedBaseThreshold absorbEta)
    (recomputedThirdFixedLossPowerThreshold thirdEta
      (longCoreHighGammaThirdAbsorb P stage)
      (sectionEightSourceLoss P targetEpsilon) gamma)

theorem endpointIdentityCorrelatedLiteralThirdLossThreshold_pos
    (P : ParameterLadder epsilon0 beta gamma)
    (absorbEta thirdEta targetEpsilon : Real) (stage : Nat) :
    0 < endpointIdentityCorrelatedLiteralThirdLossThreshold
      P absorbEta thirdEta targetEpsilon stage := by
  exact lt_min
    (endpointCorrelatedBaseThreshold_pos _)
    (recomputedThirdFixedLossPowerThreshold_pos _ _ _ _)

/-- Produce exactly the literal third-loss power consumed by Parentwise DSO
V3.  The scalar residual is generated and discharged inside this theorem.
The only analytic input is the card-scale power on the same literal U; its
exponent remains arbitrary and is charged honestly in hbaseBudget. -/
theorem endpointIdentity_correlated_literalThirdLoss
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hepsilonHalf : P.epsilon <= 1 / 2)
    (targetEpsilon outputEta cardScaleEta thirdEta absorbEta : Real)
    (hTargetEpsilon : 0 < targetEpsilon)
    (hOutputEta : 0 <= outputEta)
    (hAbsorbEta : 0 < absorbEta)
    (hCard : 0 <= cardScaleEta)
    (hThirdEta : 0 < thirdEta)
    (hThirdCap : thirdEta <= P.eta 0)
    (hXPower :
      let E := fullRefinementDatum D
      let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
      let C := identityRadiusCoherentCover E.family
      let S := endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))
      let U0 := canonicalBufferedTauActiveCover E hE C S W
        P.epsilon_pos.le hepsilonHalf
      let U := activeFineRestrictedScaleCover U0
      (activeCoarseCardScaleMass U : ENNReal) <=
        (delta : ENNReal) ^ (-cardScaleEta))
    (hsmall : delta <=
      endpointIdentityCorrelatedLiteralThirdLossThreshold
        P absorbEta thirdEta targetEpsilon W.stage)
    (hbaseBudget :
      2 * outputEta + cardScaleEta + absorbEta <=
        (1 - P.epsilon) * thirdEta) :
    let rho := canonicalBufferedRadius W
    let CKT := identitySourceFrostmanKatzTaoConstant D rho outputEta
    let conflictThreshold :=
      Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal)
    eighthSelectedThirdFactorLoss rho
        ((432 : ENNReal) *
          ((conflictThreshold + 1 : Nat) : ENNReal))
        (sectionEightSourceLoss P targetEpsilon) gamma <=
      (delta : ENNReal) ^ (-3 * P.eta W.stage) := by
  dsimp only
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let rho := canonicalBufferedRadius W
  let CKT := identitySourceFrostmanKatzTaoConstant D rho outputEta
  let sourceLoss := sectionEightSourceLoss P targetEpsilon
  let thirdAbsorb := longCoreHighGammaThirdAbsorb P W.stage
  have hthirdAbsorb : 0 < thirdAbsorb := by
    dsimp only [thirdAbsorb, longCoreHighGammaThirdAbsorb]
    exact div_pos (P.eta_pos W.stage) (by norm_num)
  have hsmallBase : delta <= endpointCorrelatedBaseThreshold absorbEta := by
    exact hsmall.trans (min_le_left _ _)
  have hsmallThird : delta <=
      recomputedThirdFixedLossPowerThreshold thirdEta thirdAbsorb
        sourceLoss gamma := by
    exact hsmall.trans (min_le_right _ _)
  have hscalar :=
    endpointIdentity_correlated_recomputedThird_scalarBase
      D hD P W hepsilonHalf hOutputEta hCard hThirdEta.le hAbsorbEta
        hXPower hsmallBase hbaseBudget
  have hrho : 0 < rho := by
    dsimp only [rho]
    exact canonicalBufferedRadius_pos W hD.delta_pos P.epsilon_pos.le
  have hdeltaRho : delta <= rho := by
    dsimp only [rho, S]
    exact
      ((endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))).delta_le_tau W.m).trans
        (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
  have hsourceLoss : 0 < sourceLoss := by
    dsimp only [sourceLoss]
    exact sectionEightSourceLoss_pos P hTargetEpsilon
  have hthirdStage : thirdEta <= P.eta W.stage := by
    exact hThirdCap.trans
      (eta_zero_le_eta_of_stage_le P W.stage W.stage_le)
  have hsourceStage : sourceLoss <= P.eta W.stage := by
    calc
      sourceLoss = sectionEightSourceLoss P targetEpsilon := rfl
      _ <= sectionEightFixedNu P :=
        sectionEightSourceLoss_le_fixedNu P targetEpsilon
      _ = P.eta 0 := rfl
      _ <= P.eta W.stage :=
        eta_zero_le_eta_of_stage_le P W.stage W.stage_le
  have hthirdBudget :
      thirdEta + thirdAbsorb + sourceLoss <=
        3 * P.eta W.stage := by
    dsimp only [thirdAbsorb, longCoreHighGammaThirdAbsorb]
    linarith
  have hfull :=
    recomputedThird_fullLoss_le_delta_negativePower
      hD.delta_pos (hD.delta_le_half.trans (by norm_num))
      hrho hdeltaRho hOutputEta hThirdEta.le hthirdAbsorb
      hsourceLoss.le hscalar hsmallThird hthirdBudget
  simpa only [rho, CKT, sourceLoss, thirdAbsorb, neg_mul] using hfull

#print axioms endpointIdentityCorrelatedLiteralThirdLossThreshold_pos
#print axioms endpointIdentity_correlated_literalThirdLoss

end
end Family8EndpointIdentityCorrelatedLiteralThirdLossProducerV1
