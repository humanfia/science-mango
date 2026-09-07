import Family8Grounding.Family8EndpointIdentityCorrelatedLiteralThirdLossProducerV1
import Family8Grounding.Family8EndpointIdentityHighGammaSelectedTrueSplitEtaXPowerV4
import Mathlib.Tactic

/-!
# Selected automatic adapter for the literal third loss

This adapter fixes only the scalar allocation selected by the top wrapper.
It does not prove the remaining same-object card-scale estimate: that exact
X-power seam is its sole analytic input.  The scalar base, both finite
thresholds, and the third-loss exponent budget are discharged internally.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8EndpointIdentityHighGammaSelectedLiteralThirdLossAdapterV1

open Submission.Kakeya.ConvexGeometry
open Family8CanonicalGlobalOuterParameterAllocationV1
open Family8EighthNormalizedSelectedFrostmanThirdFactorV3
open Family8EndpointIdentityCorrelatedRecomputedThirdBaseBudgetV1
open Family8FirstCrossingRecomputedThirdFixedLossPowerV3
open Family8EndpointIdentityCorrelatedLiteralThirdLossProducerV1
open Family8EndpointIdentityFirstCrossingImpossibleV1
open Family8EndpointIdentityHighGammaAutomaticHLongGeometryAdapterV1
open Family8EndpointIdentityHighGammaParentwiseLongCoreAutomaticV1
open Family8EndpointIdentityHighGammaSelectedTrueSplitEtaXPowerV4
open Family8FullRefinementActualDatumV1
open Family8HighGammaParameterLadderV1
open Family8IdentitySourceFrostmanKatzTaoCardScaleCancellationV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ParameterSelectedTrueSplitEtaStrongFrostmanLongCoreOnlyMainLemmaV3
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8RelativeScaleFixedNuEndpointOrchestrationV1
open Family8SectionEightOutputEtaV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- The selected AtRaw X-power produces exactly the literal third-loss field
for the same automatic witness.  No CKT cap, scalar base, separate fixed-third
threshold, or third-exponent budget occurs in the interface. -/
theorem selectedTrueSplitEta_literalThirdLoss_of_XPowerAtRaw
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (targetEpsilon etaKT thirdEta : Real) (delta0 : NNReal)
    (hTargetEpsilon : 0 < targetEpsilon)
    (hThirdEta : 0 < thirdEta)
    (hThirdCap : thirdEta <= H.ladder.eta 0)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (hdeltaRaw : delta <= highGammaSelectedTrueSplitEtaRawDelta0
      H targetEpsilon etaKT thirdEta delta0)
    (hFOutput : FrostmanHypotheses D
      (selectedTrueSplitOutputEta H.ladder thirdEta))
    (hXPower : selectedTrueSplitEtaXPowerAtRaw
      H hbeta hgamma targetEpsilon etaKT thirdEta delta0
        D hD hdeltaRaw hFOutput) :
    let P := H.ladder
    let outputEta := selectedTrueSplitOutputEta P thirdEta
    let hselectorSmall : delta <=
        endpointIdentityFirstCrossingImpossibleThreshold P :=
      hdeltaRaw.trans
        (highGammaSelectedTrueSplitEtaRawDelta0_le_selector
          H targetEpsilon etaKT thirdEta delta0)
    let W := automaticNormalizedLongCoreWitness
      D hD P hbeta hgamma hselectorSmall hFOutput
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
  let P := H.ladder
  let outputEta := selectedTrueSplitOutputEta P thirdEta
  let q := selectedTrueSplitQuantum P thirdEta
  let cardScaleEta := selectedTrueSplitCardScaleEta P thirdEta
  let sourceLoss := sectionEightSourceLoss P targetEpsilon
  have hselectorSmall : delta <=
      endpointIdentityFirstCrossingImpossibleThreshold P :=
    hdeltaRaw.trans
      (highGammaSelectedTrueSplitEtaRawDelta0_le_selector
        H targetEpsilon etaKT thirdEta delta0)
  let W := automaticNormalizedLongCoreWitness
    D hD P hbeta hgamma hselectorSmall hFOutput
  have hepsilonHalf : P.epsilon <= 1 / 2 := by
    dsimp only [P]
    exact highGammaLadder_epsilon_le_half H hbeta hgamma
  have hEpsilonOne : P.epsilon < 1 := by
    dsimp only [P]
    exact Family8EndpointIdentityCoreSelectorV2.parameterLadder_epsilon_lt_one
      H.ladder hbeta hgamma
  have hOutputEta : 0 < outputEta := by
    dsimp only [outputEta]
    exact selectedTrueSplitOutputEta_pos P hEpsilonOne hThirdEta
  have hSectionEta :
      0 < sectionEightOutputEta P outputEta :=
    sectionEightOutputEta_pos P hOutputEta
  have hq : 0 < q := by
    dsimp only [q, selectedTrueSplitQuantum, selectedTrueSplitSectionEta]
    exact canonicalGlobalOuterQuantum_pos P hSectionEta
  have hCard : 0 < cardScaleEta := by
    dsimp only [cardScaleEta]
    exact selectedTrueSplitCardScaleEta_pos P hEpsilonOne hThirdEta
  have hX :
      let E := fullRefinementDatum D
      let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
      let C := identityRadiusCoherentCover E.family
      let S := endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))
      let U0 := canonicalBufferedTauActiveCover E hE C S W
        P.epsilon_pos.le hepsilonHalf
      let U := activeFineRestrictedScaleCover U0
      (activeCoarseCardScaleMass U : ENNReal) <=
        (delta : ENNReal) ^ (-cardScaleEta) := by
    simpa only [selectedTrueSplitEtaXPowerAtRaw, P, q, cardScaleEta,
      hselectorSmall, W] using hXPower
  have hdeltaOld : delta <=
      highGammaAutomaticRawDelta0
        H targetEpsilon etaKT thirdEta delta0 :=
    hdeltaRaw.trans
      (highGammaSelectedTrueSplitEtaRawDelta0_le_old
        H targetEpsilon etaKT thirdEta delta0)
  have hsmallBase : delta <= endpointCorrelatedBaseThreshold q :=
    hdeltaRaw.trans
      (highGammaSelectedTrueSplitEtaRawDelta0_le_correlated
        H targetEpsilon etaKT thirdEta delta0)
  have hsmallUniform : delta <=
      highGammaAutomaticUniformStageThreshold P thirdEta sourceLoss := by
    exact hdeltaOld.trans
      (highGammaAutomaticRawDelta0_le_uniformStage
        H targetEpsilon etaKT thirdEta delta0)
  have hsmallStage : delta <=
      highGammaAutomaticStageThreshold
        P thirdEta sourceLoss W.stage :=
    hsmallUniform.trans
      (highGammaAutomaticUniformStageThreshold_le
        P thirdEta sourceLoss W.stage_le)
  have hsmallThirdOld : delta <=
      recomputedThirdFixedLossPowerThreshold thirdEta
        (Family8EndpointIdentityHighGammaParentwiseLongCoreDSOV1.longCoreHighGammaThirdAbsorb
          P W.stage) sourceLoss gamma :=
    hsmallStage.trans
      (highGammaAutomaticStageThreshold_le_third
        P thirdEta sourceLoss W.stage)
  have hsmallThird : delta <=
      recomputedThirdFixedLossPowerThreshold thirdEta
        (Family8EndpointIdentityHighGammaParentwiseLongCoreTrueSplitEtaDSOV3.longCoreHighGammaThirdAbsorb
          P W.stage) sourceLoss gamma := by
    simpa only [
      Family8EndpointIdentityHighGammaParentwiseLongCoreDSOV1.longCoreHighGammaThirdAbsorb,
      Family8EndpointIdentityHighGammaParentwiseLongCoreTrueSplitEtaDSOV3.longCoreHighGammaThirdAbsorb]
      using hsmallThirdOld
  have hsmall : delta <=
      endpointIdentityCorrelatedLiteralThirdLossThreshold
        P q thirdEta targetEpsilon W.stage := by
    exact le_min hsmallBase hsmallThird
  have hbaseBudget :
      2 * outputEta + cardScaleEta + q <=
        (1 - P.epsilon) * thirdEta := by
    have hraw :=
      selectedTrueSplitOutputEta_correlated_base_budget
        P hEpsilonOne hThirdEta
    simpa only [outputEta, q, cardScaleEta,
      selectedTrueSplitQuantum, selectedTrueSplitSectionEta] using hraw
  have hliteral :=
    endpointIdentity_correlated_literalThirdLoss
      D hD P W hepsilonHalf targetEpsilon outputEta cardScaleEta thirdEta q
      hTargetEpsilon hOutputEta.le hq hCard.le hThirdEta hThirdCap
      hX hsmall hbaseBudget
  simpa only [P, outputEta, hselectorSmall, W] using hliteral

#print axioms selectedTrueSplitEta_literalThirdLoss_of_XPowerAtRaw

end
end Family8EndpointIdentityHighGammaSelectedLiteralThirdLossAdapterV1
