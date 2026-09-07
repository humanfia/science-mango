import Family8Grounding.Family8EndpointIdentityHighGammaSelectedTrueSplitEtaXPowerV4
import Family8Grounding.Family8EndpointIdentityHighGammaParentwiseLongCoreTrueSplitEtaDSOV3
import Family8Grounding.Family8EndpointIdentityCorrelatedSelectedDensityGateProducerV1
import Family8Grounding.Family8EndpointIdentityHighGammaSelectedLiteralThirdLossAdapterV1
import Mathlib.Tactic

/-!
# Automatic high-gamma endpoint for the selected true split

The public successor in this module fixes the one exponent pair selected by
the top wrapper.  The only analytic seam is the same-cover card-scale power
`selectedTrueSplitEtaXPowerAtRaw`; the density assembly, complete correlated
B2 product, and literal third loss are generated internally on the same
automatic witness.  No cover, witness, or assembly is reselected.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8EndpointIdentityHighGammaSelectedTrueSplitEtaAutomaticAdapterV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ActiveFrozenComparableLogLossAbsorptionV4
open Family8AllFrostmanStickyUnionProducerV1
open Family8CanonicalGlobalOuterParameterAllocationV1
open Family8CanonicalEndpointBaseThresholdV1
open Family8EndpointIdentityCorrelatedRecomputedThirdBaseBudgetV1
open Family8EndpointIdentityCorrelatedSelectedDensityGateProducerV1
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointIdentityFirstCrossingImpossibleV1
open Family8EndpointIdentityHighGammaAutomaticHLongGeometryAdapterV1
open Family8EndpointIdentityHighGammaParentwiseLongCoreAutomaticV1
open Family8EndpointIdentityHighGammaParentwiseLongCoreTrueSplitEtaDSOV3
open Family8EndpointIdentityHighGammaSelectedTrueSplitEtaXPowerV4
open Family8EndpointIdentityHighGammaSelectedLiteralThirdLossAdapterV1
open Family8EndpointLongCoreSixteenthRadiusThresholdV1
open Family8EndpointLongCoreTauActiveSourceMassIdentityV1
open Family8EighthNormalizedSelectedFrostmanThirdFactorV3
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FullRefinementActualDatumV1
open Family8HighGammaParameterLadderV1
open Family8IdentityCoreTauActiveSingletonFiberV4
open Family8IdentitySourceFrostmanKatzTaoCardScaleCancellationV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8ParameterSelectedTrueSplitEtaStrongFrostmanLongCoreOnlyMainLemmaV3
open Family8RelativeScaleFixedNuEndpointOrchestrationV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open Family8SectionEightOutputEtaV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyBoundedFiberPartitionCoreV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrozenComparableAdapterV2
open Family8StickyShadingAwareLogBucketSelectionV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- The three literal conclusions of the Parentwise DSO, bundled only as an
internal connector.  The final theorem below does not expose this payload. -/
def selectedTrueSplitEtaLiteralPayloadAtRaw
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (targetEpsilon etaKT thirdEta : Real) (delta0 : NNReal)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (hdeltaRaw : delta <= highGammaSelectedTrueSplitEtaRawDelta0
      H targetEpsilon etaKT thirdEta delta0)
    (hFOutput : FrostmanHypotheses D
      (selectedTrueSplitOutputEta H.ladder thirdEta)) : Prop :=
  let P := H.ladder
  let outputEta := selectedTrueSplitOutputEta P thirdEta
  let sourceLoss := sectionEightSourceLoss P targetEpsilon
  let hselectorSmall : delta <=
      endpointIdentityFirstCrossingImpossibleThreshold P :=
    hdeltaRaw.trans
      (highGammaSelectedTrueSplitEtaRawDelta0_le_selector
        H targetEpsilon etaKT thirdEta delta0)
  let W := automaticNormalizedLongCoreWitness
    D hD P hbeta hgamma hselectorSmall hFOutput
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let rho := canonicalBufferedRadius W
  let U0 := canonicalBufferedTauActiveCover E hE C S W
    P.epsilon_pos.le (highGammaLadder_epsilon_le_half H hbeta hgamma)
  let Dtau := tauActiveCoarseDatum E C S W
  let U := activeFineRestrictedScaleCover U0
  let Y := activeFineRestrictedShading U0 Dtau.shading
  let hsource :
      (IndexedShadingRefinement.restrictTo Y
        U.activeFine).shading.shadingMass ≠ 0 := by
    have hmass : D.shading.shadingMass ≠ 0 := by
      have hfloor := delta_rpow_two_eta_le_shadingMass_of_frostman
        D hD hFOutput
      exact ne_of_gt ((ENNReal.rpow_pos
        (ENNReal.coe_pos.mpr hD.delta_pos)
        ENNReal.coe_ne_top).trans_le hfloor)
    have hOn : shadingMassOn Y U.activeFine ≠ 0 := by
      rw [endpointLongCore_canonicalBufferedTauActive_shadingMassOn_eq_source
        D hD P W (highGammaLadder_epsilon_le_half H hbeta hgamma)]
      exact hmass
    rw [shadingMass_restrictTo_eq_sum]
    exact hOn
  let hM : forall k, k ∈ U.activeCoarse -> (U.fiber k).card <= 1 := by
    intro k _hk
    simpa only [Fintype.card_coe] using
      identityCore_canonicalBufferedTauActiveRestricted_fiber_card_le_one
        E hE S W P.epsilon_pos.le
          (highGammaLadder_epsilon_le_half H hbeta hgamma) k
  let hcoarse : U.activeCoarse.Nonempty :=
    activeCoarse_nonempty_of_restricted_shadingMass_ne_zero U Y hsource
  let Pcoarse := boundedFiberCoarseTubePartition U
    (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
    hcoarse 1 hM
  let CKT := identitySourceFrostmanKatzTaoConstant D rho outputEta
  let conflictThreshold :=
    Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal)
  (exists A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      Pcoarse.asConvexFactorization Y 1,
    A.loss = frozenComparableLoss {i // i ∈ U0.activeFine}
        (Fin U.coarseCard) /\
    A.frozenCoarse =
        Pcoarse.asConvexFactorization.inducedShading
          A.refinement.shading /\
    (((rho / 8 : NNReal) : ENNReal) ^ thirdEta *
        (128 * ((conflictThreshold + 1 : Nat) : ENNReal)) <=
      Y.shadingDensity ^ 2 /
        ((A.loss : ENNReal) *
          (768 * (Pcoarse.branchingLoss : ENNReal) ^ 2)))) /\
  (((conflictThreshold + 1 : Nat) : ENNReal) *
      ((128 * CKT) * volume (unitBallBody : Set Space)) <=
    ((rho / 8 : NNReal) : ENNReal) ^ (-thirdEta) *
      ((Fintype.card (Fin U.coarseCard) : ENNReal) *
        ((((rho / 8 : NNReal) : ENNReal) ^ 2) / 2))) /\
  eighthSelectedThirdFactorLoss rho
      ((432 : ENNReal) *
        ((conflictThreshold + 1 : Nat) : ENNReal))
      sourceLoss gamma <=
    (delta : ENNReal) ^ (-3 * P.eta W.stage)

/-- Mechanical automatic connector from the three exact DSO conclusions.
It is deliberately internal-facing: the final V4 theorem constructs the
payload from one selected X-power estimate. -/
theorem dividingScaleOutput_of_endpointIdentity_highGamma_selectedTrueSplitEta_automatic_of_literalPayload
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (targetEpsilon etaKT thirdEta : Real) (delta0 : NNReal)
    (hTarget : 0 < targetEpsilon)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (hdeltaRaw : delta <= highGammaSelectedTrueSplitEtaRawDelta0
      H targetEpsilon etaKT thirdEta delta0)
    (hFOutput : FrostmanHypotheses D
      (selectedTrueSplitOutputEta H.ladder thirdEta))
    (hFExact : FrostmanAtParameters gamma
      (sectionEightSourceLoss H.ladder targetEpsilon) thirdEta delta0)
    (hLiteral : selectedTrueSplitEtaLiteralPayloadAtRaw
      H hbeta hgamma targetEpsilon etaKT thirdEta delta0
        D hD hdeltaRaw hFOutput) :
    DividingScaleOutput D H.ladder
      (4 * sectionEightSourceLoss H.ladder targetEpsilon) := by
  let P := H.ladder
  let outputEta := selectedTrueSplitOutputEta P thirdEta
  let sourceLoss := sectionEightSourceLoss P targetEpsilon
  have hepsilonHalf : P.epsilon <= 1 / 2 :=
    highGammaLadder_epsilon_le_half H hbeta hgamma
  have hdeltaOld : delta <= highGammaAutomaticRawDelta0
      H targetEpsilon etaKT thirdEta delta0 :=
    hdeltaRaw.trans
      (highGammaSelectedTrueSplitEtaRawDelta0_le_old
        H targetEpsilon etaKT thirdEta delta0)
  have hselectorSmall : delta <=
      endpointIdentityFirstCrossingImpossibleThreshold P :=
    hdeltaRaw.trans
      (highGammaSelectedTrueSplitEtaRawDelta0_le_selector
        H targetEpsilon etaKT thirdEta delta0)
  have hdeltaBase : delta <=
      canonicalEndpointBaseThreshold P (4 * sourceLoss) etaKT :=
    hdeltaOld.trans
      (highGammaAutomaticRawDelta0_le_base
        H targetEpsilon etaKT thirdEta delta0)
  have hsmallSixteenth : delta <=
      endpointLongCoreSixteenthRadiusThreshold P :=
    hdeltaOld.trans
      (highGammaAutomaticRawDelta0_le_sixteenth
        H targetEpsilon etaKT thirdEta delta0)
  have hsmallDelta0Radius : delta <=
      endpointLongCoreTargetRadiusThreshold P ((8 : NNReal) * delta0) :=
    hdeltaOld.trans
      (highGammaAutomaticRawDelta0_le_delta0Radius
        H targetEpsilon etaKT thirdEta delta0)
  let W := automaticNormalizedLongCoreWitness
    D hD P hbeta hgamma hselectorSmall hFOutput
  have hbufferedSixteenth :
      canonicalBufferedRadius W <= (1 / 16 : NNReal) :=
    canonicalBufferedRadius_le_sixteenth_of_endpointSmall
      P hbeta hgamma (hD.delta_le_half.trans (by norm_num)) W
        hsmallSixteenth
  have hbufferedDelta0 :
      canonicalBufferedRadius W <= (8 : NNReal) * delta0 :=
    canonicalBufferedRadius_le_target_of_endpointSmall
      P hbeta hgamma (hD.delta_le_half.trans (by norm_num)) W
        ((8 : NNReal) * delta0) hsmallDelta0Radius
  have hthirdDelta0 : canonicalBufferedRadius W / 8 <= delta0 := by
    apply (div_le_iff₀ (by norm_num : (0 : NNReal) < 8)).2
    simpa only [mul_comm] using hbufferedDelta0
  have hsmallUniform : delta <=
      highGammaAutomaticUniformStageThreshold P thirdEta sourceLoss :=
    hdeltaOld.trans
      (highGammaAutomaticRawDelta0_le_uniformStage
        H targetEpsilon etaKT thirdEta delta0)
  have hStageSmall : delta <=
      highGammaAutomaticStageThreshold P thirdEta sourceLoss W.stage :=
    hsmallUniform.trans
      (highGammaAutomaticUniformStageThreshold_le
        P thirdEta sourceLoss W.stage_le)
  have hsmallFrozenV1 : delta <=
      activeFrozenComparableLossAbsorptionThreshold
        (Family8EndpointIdentityHighGammaParentwiseLongCoreDSOV1.longCoreHighGammaQuarterReserve
          P W.stage) :=
    hStageSmall.trans
      (highGammaAutomaticStageThreshold_le_frozen
        P thirdEta sourceLoss W.stage)
  have hsmallFrozen : delta <=
      activeFrozenComparableLossAbsorptionThreshold
        (longCoreHighGammaQuarterReserve P W.stage) := by
    simpa only [
      Family8EndpointIdentityHighGammaParentwiseLongCoreDSOV1.longCoreHighGammaQuarterReserve,
      Family8EndpointIdentityHighGammaParentwiseLongCoreDSOV1.longCoreHighGammaReserve,
      longCoreHighGammaQuarterReserve, longCoreHighGammaReserve] using
        hsmallFrozenV1
  have hsmallFourV1 : delta <=
      finiteConstantSmallDeltaThreshold (4 : ENNReal)
        (Family8EndpointIdentityHighGammaParentwiseLongCoreDSOV1.longCoreHighGammaQuarterReserve
          P W.stage) :=
    hStageSmall.trans
      (highGammaAutomaticStageThreshold_le_four
        P thirdEta sourceLoss W.stage)
  have hsmallFour : delta <=
      finiteConstantSmallDeltaThreshold (4 : ENNReal)
        (longCoreHighGammaQuarterReserve P W.stage) := by
    simpa only [
      Family8EndpointIdentityHighGammaParentwiseLongCoreDSOV1.longCoreHighGammaQuarterReserve,
      Family8EndpointIdentityHighGammaParentwiseLongCoreDSOV1.longCoreHighGammaReserve,
      longCoreHighGammaQuarterReserve, longCoreHighGammaReserve] using
        hsmallFourV1
  have hhigh :
      10 * P.eta W.stage < P.epsilon ^ 2 * (3 * gamma - 2) :=
    H.ten_eta_lt_gain W.stage
  have hEffectiveTarget : 0 < 4 * sourceLoss := by
    have hSourceLoss : 0 < sourceLoss := by
      dsimp only [sourceLoss]
      exact sectionEightSourceLoss_pos P hTarget
    positivity
  have hFExactEffective : FrostmanAtParameters gamma
      ((4 * sourceLoss) / 4) thirdEta delta0 := by
    convert hFExact using 1
    ring
  have hLiteral' := hLiteral
  simp only [selectedTrueSplitEtaLiteralPayloadAtRaw] at hLiteral'
  obtain ⟨hDensity, hBase, hThird⟩ := hLiteral'
  have hThirdEffective :
      let rho := canonicalBufferedRadius W
      let CKT := identitySourceFrostmanKatzTaoConstant D rho outputEta
      let conflictThreshold :=
        Nat.ceil ((480000 * (128 * CKT) : ENNReal).toReal)
      eighthSelectedThirdFactorLoss rho
          ((432 : ENNReal) *
            ((conflictThreshold + 1 : Nat) : ENNReal))
          ((4 * sourceLoss) / 4) gamma <=
        (delta : ENNReal) ^ (-3 * P.eta W.stage) := by
    dsimp only
    simpa only [show (4 * sourceLoss) / 4 = sourceLoss by ring] using hThird
  exact
    dividingScaleOutput_of_endpointIdentity_highGamma_parentwiseLongCore_trueSplitEta_directCorrelated
      D hD P
      (automaticParentwiseLongCoreWitness
        D hD P hbeta hgamma hselectorSmall)
      (fullRefinement_refined_nonempty_of_frostmanHypotheses
        D hD hFOutput)
      (4 * sourceLoss) etaKT outputEta thirdEta delta0
      hEffectiveTarget hgamma hepsilonHalf
      hbufferedSixteenth hdeltaBase hFOutput hFExactEffective hhigh
      hsmallFrozen hsmallFour hsmallFour hthirdDelta0
      hDensity hBase hThirdEffective

/-- Conditional-on-X automatic high-gamma checkpoint for the selected pair.
The single hypothesis `hXPower` is the honest unresolved analytic seam on the
one automatic identity-cover witness.  All scalar ledgers, the selected
density assembly, the complete B2 base, and the literal third loss are
constructed internally; this theorem is not advertised as final top closure. -/
theorem dividingScaleOutput_of_endpointIdentity_highGamma_selectedTrueSplitEta_automatic_conditionalOnX
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (targetEpsilon etaKT thirdEta : Real) (delta0 : NNReal)
    (hTarget : 0 < targetEpsilon)
    (hThirdEta : 0 < thirdEta)
    (hThirdCap : thirdEta <= H.ladder.eta 0)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (hdeltaRaw : delta <= highGammaSelectedTrueSplitEtaRawDelta0
      H targetEpsilon etaKT thirdEta delta0)
    (hFOutput : FrostmanHypotheses D
      (selectedTrueSplitOutputEta H.ladder thirdEta))
    (hFExact : FrostmanAtParameters gamma
      (sectionEightSourceLoss H.ladder targetEpsilon) thirdEta delta0)
    (hXPower : selectedTrueSplitEtaXPowerAtRaw
      H hbeta hgamma targetEpsilon etaKT thirdEta delta0
        D hD hdeltaRaw hFOutput) :
    DividingScaleOutput D H.ladder
      (4 * sectionEightSourceLoss H.ladder targetEpsilon) := by
  let P := H.ladder
  let outputEta := selectedTrueSplitOutputEta P thirdEta
  let q := selectedTrueSplitQuantum P thirdEta
  let cardScaleEta := selectedTrueSplitCardScaleEta P thirdEta
  have hepsilonHalf : P.epsilon <= 1 / 2 := by
    dsimp only [P]
    exact highGammaLadder_epsilon_le_half H hbeta hgamma
  have hEpsilonOne : P.epsilon < 1 :=
    hepsilonHalf.trans_lt (by norm_num)
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
  have hselectorSmall : delta <=
      endpointIdentityFirstCrossingImpossibleThreshold P :=
    hdeltaRaw.trans
      (highGammaSelectedTrueSplitEtaRawDelta0_le_selector
        H targetEpsilon etaKT thirdEta delta0)
  let W := automaticNormalizedLongCoreWitness
    D hD P hbeta hgamma hselectorSmall hFOutput
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
  have hsmallBase : delta <= endpointCorrelatedBaseThreshold q :=
    hdeltaRaw.trans
      (highGammaSelectedTrueSplitEtaRawDelta0_le_correlated
        H targetEpsilon etaKT thirdEta delta0)
  have hsmallFrozen : delta <=
      activeFrozenComparableLossAbsorptionThreshold q :=
    hdeltaRaw.trans
      (highGammaSelectedTrueSplitEtaRawDelta0_le_densityFrozen
        H targetEpsilon etaKT thirdEta delta0)
  have hbaseBudget :
      2 * outputEta + cardScaleEta + q <=
        (1 - P.epsilon) * thirdEta := by
    have hraw := selectedTrueSplitOutputEta_correlated_base_budget
      P hEpsilonOne hThirdEta
    simpa only [outputEta, q, cardScaleEta,
      selectedTrueSplitQuantum, selectedTrueSplitSectionEta] using hraw
  have hdensityBudget :
      3 * outputEta + cardScaleEta + 2 * q <=
        (1 - P.epsilon) * thirdEta := by
    have hraw := selectedTrueSplitOutputEta_correlated_density_budget
      (P := P) (thirdEta := thirdEta)
    simpa only [outputEta, q, cardScaleEta,
      selectedTrueSplitQuantum, selectedTrueSplitSectionEta] using hraw
  have hDensity :=
    exists_endpointIdentity_correlatedSelected_densityAssembly
      D hD P W hepsilonHalf hOutputEta hCard.le hThirdEta.le hq
        hFOutput hX hsmallBase hsmallFrozen hdensityBudget
  have hBase :=
    endpointIdentity_correlated_recomputedThird_baseBudget
      D hD P W hepsilonHalf hOutputEta.le hCard.le hThirdEta.le hq
        hX hsmallBase hbaseBudget
  have hThird :=
    selectedTrueSplitEta_literalThirdLoss_of_XPowerAtRaw
      H hbeta hgamma targetEpsilon etaKT thirdEta delta0
        hTarget hThirdEta hThirdCap D hD hdeltaRaw hFOutput hXPower
  have hLiteral : selectedTrueSplitEtaLiteralPayloadAtRaw
      H hbeta hgamma targetEpsilon etaKT thirdEta delta0
        D hD hdeltaRaw hFOutput := by
    simp only [selectedTrueSplitEtaLiteralPayloadAtRaw]
    exact ⟨hDensity, hBase, hThird⟩
  exact
    dividingScaleOutput_of_endpointIdentity_highGamma_selectedTrueSplitEta_automatic_of_literalPayload
      H hbeta hgamma targetEpsilon etaKT thirdEta delta0 hTarget
        D hD hdeltaRaw hFOutput hFExact hLiteral

#print axioms selectedTrueSplitEtaLiteralPayloadAtRaw
#print axioms
  dividingScaleOutput_of_endpointIdentity_highGamma_selectedTrueSplitEta_automatic_of_literalPayload
#print axioms
  dividingScaleOutput_of_endpointIdentity_highGamma_selectedTrueSplitEta_automatic_conditionalOnX

end
end Family8EndpointIdentityHighGammaSelectedTrueSplitEtaAutomaticAdapterV4
