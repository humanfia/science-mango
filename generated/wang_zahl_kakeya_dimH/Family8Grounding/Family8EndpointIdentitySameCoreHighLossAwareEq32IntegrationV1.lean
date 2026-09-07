import Family8Grounding.Family8EndpointIdentityCorrelatedSameCoreHighCloserDatumAdapterV1
import Family8Grounding.Family8EndpointIdentityProp66DirectActualPrefixTerminalV1
import Mathlib.Tactic

/-!
# Run-free endpoint integration for the literal same-core high payload

The endpoint dichotomy preserves a literal same-core high payload.  The
analytic work downstream of that payload is to produce the common
loss-aware Equation-(32) estimate, its honest product-count comparison, and
the final scalar loss ledger.  Once those three facts are available, the
minimal actual-prefix terminal closes the endpoint DSO without a paper-factor
run, a reverse ledger, a graph H-row, or an independently selected long core.

This module makes that boundary exact.  It also lifts a pointwise
high-payload-to-Equation-(32) producer through the existing correlated datum
adapter, so the remaining premise has the same quantifier order and the same
automatic witness as the actual top-level callback.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6000000

open scoped BigOperators ENNReal NNReal

namespace Family8EndpointIdentitySameCoreHighLossAwareEq32IntegrationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8AllGammaSelectedTrueSplitEtaLongGeometryCommonV3
open Family8EndpointIdentityCorrelatedSameCoreHighCloserDatumAdapterV1
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointIdentityFirstCrossingImpossibleV1
open Family8EndpointIdentityProp66DirectActualPrefixTerminalV1
open Family8EndpointIdentitySourceTauSameOccurrenceProp66APowerBudgetV1
open Family8FullRefinementActualDatumV1
open Family8GeneralizedScaleTrivialBranchV1
open Family8EndpointIdentityHighGammaParentwiseLongCoreAutomaticV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8ParameterSelectedTrueSplitEtaStrongFrostmanLongCoreOnlyMainLemmaV3
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66ASectionEightCollapsedAlgebraV1
open Family8RelativeScaleFixedNuEndpointOrchestrationV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open Family8ThreeScaleActualFrostmanFactorAbsorptionV2
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma targetEpsilon : Real}

/-- The exact run-free terminal data after the high branch has produced its
common loss-aware Equation-(32) estimate.  These are precisely the three
premises consumed by the minimal actual-prefix endpoint theorem. -/
def EndpointIdentityLossAwareEq32PaymentAt
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num)))) : Prop :=
  exists a b : NNReal,
  exists totalCount : Nat,
  exists CF externalLoss countLoss : ENNReal,
  exists epsilon : Real,
    D.shading.averageMultiplicity <=
      externalLoss * proposition66AFrostmanFactor
        delta a b totalCount CF epsilon gamma /\
    (totalCount : ENNReal) <=
      countLoss * (Fintype.card index : ENNReal) /\
    (externalLoss *
      (proposition66ASectionEightCoefficient
          delta a b CF epsilon gamma *
        (delta : ENNReal) ^ (-10 * P.eta W.stage))) *
        countLoss ^ (1 - gamma / 2) <=
      (delta : ENNReal) ^ (-3 * P.eta W.stage)

/-- A payment produced from the literal high payload closes the DSO through
the run-free actual-prefix terminal.  The high payload cannot be replaced by
the desired conclusion: it is supplied only to `hPayment`, whose output is
the concrete Equation-(32) ledger above. -/
theorem dividingScaleOutput_of_exactSameCoreHigh_lossAwareEq32Payment
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (A : ENNReal) (r : NNReal) (hr : 0 < r) (KT : ENNReal)
    (hHigh : EndpointIdentityExactSameCoreHighPayloadAt
      D hD P W A r hr KT)
    (hPayment : EndpointIdentityExactSameCoreHighPayloadAt
        D hD P W A r hr KT ->
      EndpointIdentityLossAwareEq32PaymentAt D hD P W)
    (hGammaOne : gamma <= 1)
    (hSmall : delta <=
      sectionEightThreeScaleActualThreshold gamma (targetEpsilon / 4))
    (hTargetEpsilon : 0 < targetEpsilon) :
    DividingScaleOutput D P targetEpsilon := by
  obtain ⟨a, b, totalCount, CF, externalLoss, countLoss, epsilon,
      hEq32, hLocalCount, hLossLedger⟩ := hPayment hHigh
  exact dividingScaleOutput_of_endpointIdentity_lossAware_eq32_via_actualPrefix
    D hD P W hEq32 hLocalCount hLossLedger hSmall hTargetEpsilon
      hGammaOne

/-- Top-level-shaped producer for the only remaining analytic content of the
same-core high route.  It receives exactly the literal high payload at the
automatic endpoint witness and returns the run-free Equation-(32) payment.
It does not return a DSO and has no conclusion-valued field. -/
def SelectedTrueSplitEtaExactSameCoreAutomaticHighEq32PaymentAt
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hGammaOne : gamma <= 1) : Prop :=
  forall targetEpsilon : Real, 0 < targetEpsilon ->
  forall etaKT thirdEta : Real, forall delta0 : NNReal,
    0 < etaKT ->
    etaKT <= P.epsilon ^ 2 * P.eta 0 / 32 ->
    0 < thirdEta -> thirdEta <= P.eta 0 ->
    0 < delta0 -> delta0 <= (2 : NNReal)⁻¹ ->
    KatzTaoAtParameters
      beta (sectionEightFixedNu P) etaKT delta0 ->
    KatzTaoAtRelativeScaleParameters
      beta (sectionEightFixedNu P) etaKT delta0 ->
    FrostmanAtParameters gamma
      (sectionEightSourceLoss P targetEpsilon) thirdEta delta0 ->
    FrostmanAtRelativeScaleParameters gamma
      (sectionEightSourceLoss P targetEpsilon) thirdEta delta0 ->
    16 * selectedTrueSplitOutputEta P thirdEta <= etaKT ->
    exists paymentDelta0 : NNReal, 0 < paymentDelta0 /\
      forall (delta : NNReal) (index : Type)
        [Fintype index] [DecidableEq index]
        (D : ActualTubeDatum delta index) (hD : D.IsAdmissible),
      delta <= paymentDelta0 ->
      forall (hselectorSmall : delta <=
        endpointIdentityFirstCrossingImpossibleThreshold P),
      forall (hautomaticSmall : delta <=
        endpointIdentitySourceTauCordobaPowerThreshold (P.eta 0)),
      forall (hFOutput : FrostmanHypotheses D
        (selectedTrueSplitOutputEta P thirdEta)),
        let W := automaticNormalizedLongCoreWitness
          D hD P hbeta hGammaOne hselectorSmall hFOutput
        let Sseq := endpointScaleSequence delta
          (hD.delta_le_half.trans (by norm_num))
        let KT := endpointIdentitySourceTauPackingKatzTaoConstant
          delta (Sseq.tau W.m)
        EndpointIdentityExactSameCoreHighPayloadAt
            D hD P W ((delta : ENNReal) ^ (-(etaKT / 8)))
              1 (by norm_num) KT ->
          EndpointIdentityLossAwareEq32PaymentAt D hD P W

/-- Turn a run-free Equation-(32) producer into the exact high closer used by
the correlated datum adapter.  The terminal scale is intersected with the
standard three-scale DSO threshold, so the producer itself need not repeat
that deterministic smallness premise. -/
theorem exactSameCoreAutomaticHighCloser_of_eq32Payment
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hGammaOne : gamma <= 1)
    (hPayment :
      SelectedTrueSplitEtaExactSameCoreAutomaticHighEq32PaymentAt
        P hbeta hGammaOne) :
    SelectedTrueSplitEtaExactSameCoreAutomaticHighCloserAt
      P hbeta hGammaOne := by
  intro targetEpsilon hTarget etaKT thirdEta delta0
    hEtaKT hEtaKTCap hThirdEta hThirdCap hDelta0 hDelta0Half
    hKTExact hKTRelative hFExact hFRelative hCorrelation
  obtain ⟨paymentDelta0, hPaymentDelta0, hPaymentAt⟩ :=
    hPayment targetEpsilon hTarget etaKT thirdEta delta0
      hEtaKT hEtaKTCap hThirdEta hThirdCap hDelta0 hDelta0Half
      hKTExact hKTRelative hFExact hFRelative hCorrelation
  let highDelta0 : NNReal := min paymentDelta0
    (sectionEightThreeScaleActualThreshold gamma (targetEpsilon / 4))
  have hHighDelta0 : 0 < highDelta0 := by
    dsimp only [highDelta0]
    exact lt_min hPaymentDelta0
      (sectionEightThreeScaleActualThreshold_pos gamma
        (targetEpsilon / 4))
  refine ⟨highDelta0, hHighDelta0, ?_⟩
  intro delta index _ _ D hD hdelta hselectorSmall hautomaticSmall
    hFOutput
  dsimp only
  have hdeltaPayment : delta <= paymentDelta0 :=
    hdelta.trans (by
      dsimp only [highDelta0]
      exact min_le_left _ _)
  have hSmall : delta <=
      sectionEightThreeScaleActualThreshold gamma (targetEpsilon / 4) :=
    hdelta.trans (by
      dsimp only [highDelta0]
      exact min_le_right _ _)
  let W := automaticNormalizedLongCoreWitness
    D hD P hbeta hGammaOne hselectorSmall hFOutput
  let Sseq := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let KT := endpointIdentitySourceTauPackingKatzTaoConstant
    delta (Sseq.tau W.m)
  intro hHigh
  have hPay : EndpointIdentityLossAwareEq32PaymentAt D hD P W := by
    simpa only [W, Sseq, KT] using
      (hPaymentAt delta index D hD hdeltaPayment hselectorSmall
        hautomaticSmall hFOutput hHigh)
  exact dividingScaleOutput_of_exactSameCoreHigh_lossAwareEq32Payment
    (targetEpsilon := targetEpsilon)
    D hD P W ((delta : ENNReal) ^ (-(etaKT / 8))) 1 (by norm_num) KT
      hHigh (fun _ => hPay) hGammaOne hSmall hTarget

/-- Actual correlated top-level integration.  After this theorem the sole
open high-branch object is the run-free Equation-(32) producer above; the
low branch, automatic witness, target threshold, and final DSO consumption
are all compiled. -/
theorem selectedTrueSplitEtaCorrelatedDatumDSOAt_of_exactSameCoreAutomaticHighEq32Payment
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hGammaOne : gamma <= 1)
    (hPayment :
      SelectedTrueSplitEtaExactSameCoreAutomaticHighEq32PaymentAt
        P hbeta hGammaOne) :
    SelectedTrueSplitEtaCorrelatedDatumDSOAt P := by
  apply
    selectedTrueSplitEtaCorrelatedDatumDSOAt_of_exactSameCoreAutomaticHighCloser
      P hbeta hGammaOne
  exact exactSameCoreAutomaticHighCloser_of_eq32Payment
    P hbeta hGammaOne hPayment

#print axioms EndpointIdentityLossAwareEq32PaymentAt
#print axioms dividingScaleOutput_of_exactSameCoreHigh_lossAwareEq32Payment
#print axioms SelectedTrueSplitEtaExactSameCoreAutomaticHighEq32PaymentAt
#print axioms exactSameCoreAutomaticHighCloser_of_eq32Payment
#print axioms
  selectedTrueSplitEtaCorrelatedDatumDSOAt_of_exactSameCoreAutomaticHighEq32Payment

end
end Family8EndpointIdentitySameCoreHighLossAwareEq32IntegrationV1
