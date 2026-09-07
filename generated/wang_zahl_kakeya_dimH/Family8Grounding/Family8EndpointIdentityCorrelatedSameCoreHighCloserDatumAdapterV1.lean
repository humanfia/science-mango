import Family8Grounding.Family8AllGammaSelectedTrueSplitEtaLongGeometryCommonV3
import Family8Grounding.Family8EndpointIdentityCorrelatedLowFreshLongIntervalDichotomyComposerV2
import Family8Grounding.Family8EndpointIdentityHighGammaParentwiseLongCoreAutomaticV1
import Family8Grounding.Family8EndpointIdentitySourceTauSameOccurrenceProp66APowerBudgetV1
import Mathlib.Tactic

/-!
# Fixed-ladder correlated datum adapter with an exact same-core high closer

The correlated endpoint dichotomy already closes its low branch.  This file
isolates the remaining obligation without hiding it behind a conclusion-valued
premise: `EndpointIdentityExactSameCoreHighCloserAt` takes the literal high
payload (encoded by setting the low result to `False`) and returns the requested
`DividingScaleOutput`.

The datum-level provider is otherwise automatic.  It chooses the established
endpoint long-core witness, uses its literal `stage`, fixes the harmless
contraction parameter to one, and obtains the Katz--Tao coefficient from
`endpointIdentity_directSameOccurrenceAutomaticInputs`.  The partition,
selected prefix, occurrence, and side label inside the high payload are never
selected again.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8EndpointIdentityCorrelatedSameCoreHighCloserDatumAdapterV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8AllGammaSelectedTrueSplitEtaLongGeometryCommonV3
open Family8EndpointIdentityCorrelatedLowFreshLongIntervalDichotomyComposerV2
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointIdentityFirstCrossingImpossibleV1
open Family8EndpointIdentityHighGammaParentwiseLongCoreAutomaticV1
open Family8EndpointIdentitySourceTauSameOccurrenceProp66APowerBudgetV1
open Family8EndpointIdentityTauActiveSameCoreOccurrenceWeightedCordobaMassStrengthenedV1
open Family8FullRefinementActualDatumV1
open Family8GeneralizedScaleTrivialBranchV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LowFreshCorrelatedPowerBudgetsV1
open Family8LowFreshLongIntervalBaseScaleBridgeV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8ParameterSelectedTrueSplitEtaStrongFrostmanLongCoreOnlyMainLemmaV3
open Family8RelativeScaleFixedNuEndpointOrchestrationV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open Family8SelectedTrueSplitOutputEtaKTCorrelationV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma targetEpsilon : Real}

/-- The literal same-core high branch, with the unrelated low result erased.
Unfolding this abbreviation gives `False \/ <the original high payload>`;
there is no `DividingScaleOutput` premise and no replacement selection. -/
abbrev EndpointIdentityExactSameCoreHighPayloadAt
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (A : ENNReal) (r : NNReal) (hr : 0 < r) (KT : ENNReal) : Prop :=
  EndpointIdentitySameCoreOccurrenceWeightedCordobaMassStrengthenedConclusion
    D hD P W A False r hr KT

/-- The weakest pointwise terminal seam: close exactly the already produced
same-core high payload.  In particular, its premise contains neither the
desired DSO nor independently selected `q` or `label` data. -/
abbrev EndpointIdentityExactSameCoreHighCloserAt
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (A : ENNReal) (r : NNReal) (hr : 0 < r) (KT : ENNReal)
    (targetEpsilon : Real) : Prop :=
  EndpointIdentityExactSameCoreHighPayloadAt D hD P W A r hr KT ->
    DividingScaleOutput D P targetEpsilon

/-- A fixed-ladder high closer may choose its own positive terminal scale.
All scalar hypotheses are exactly those supplied by the correlated CommonV3
callback.  At a datum it receives the automatic long-core witness and the
literal automatic Katz--Tao coefficient; the only geometric premise is the
unchanged high payload produced at `r = 1`. -/
def SelectedTrueSplitEtaExactSameCoreAutomaticHighCloserAt
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
      exists highDelta0 : NNReal, 0 < highDelta0 /\
        forall (delta : NNReal) (index : Type)
          [Fintype index] [DecidableEq index]
          (D : ActualTubeDatum delta index) (hD : D.IsAdmissible),
          delta <= highDelta0 ->
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
            EndpointIdentityExactSameCoreHighCloserAt
              D hD P W ((delta : ENNReal) ^ (-(etaKT / 8)))
                1 (by norm_num) KT targetEpsilon

/-- Common positive scale on which the endpoint witness, the closed low
branch, the normalized `delta / 8` input, and the automatic same-occurrence
Katz--Tao coefficient are simultaneously available. -/
def endpointIdentityCorrelatedSameCoreHighBaseThreshold
    (P : ParameterLadder epsilon0 beta gamma)
    (etaKT : Real) (delta0 : NNReal) : NNReal :=
  min delta0
    (min (endpointIdentityFirstCrossingImpossibleThreshold P)
      (min (lowFreshCorrelatedPowerThreshold etaKT (P.eta 0))
        (min (lowFreshLongIntervalBaseScaleThreshold P)
          (endpointIdentitySourceTauCordobaPowerThreshold (P.eta 0)))))

theorem endpointIdentityCorrelatedSameCoreHighBaseThreshold_pos
    (P : ParameterLadder epsilon0 beta gamma)
    (etaKT : Real) {delta0 : NNReal} (hdelta0 : 0 < delta0) :
    0 < endpointIdentityCorrelatedSameCoreHighBaseThreshold
      P etaKT delta0 := by
  unfold endpointIdentityCorrelatedSameCoreHighBaseThreshold
  exact lt_min hdelta0
    (lt_min (endpointIdentityFirstCrossingImpossibleThreshold_pos P)
      (lt_min (lowFreshCorrelatedPowerThreshold_pos etaKT (P.eta 0))
        (lt_min (lowFreshLongIntervalBaseScaleThreshold_pos P)
          (endpointIdentitySourceTauCordobaPowerThreshold_pos (P.eta 0)))))

/-- Reduce the fixed-`P` CommonV3 datum callback to the exact preserved high
payload.  `rawDelta0` is the intersection of the closer's chosen scale and
all automatic endpoint/low/KT scales.  The dichotomy is invoked at the
automatic witness's own `stage`; its low result is already the requested DSO,
and its high witnesses are handed to the closer by the identity map. -/
theorem selectedTrueSplitEtaCorrelatedDatumDSOAt_of_exactSameCoreAutomaticHighCloser
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hGammaOne : gamma <= 1)
    (hHighCloser :
      SelectedTrueSplitEtaExactSameCoreAutomaticHighCloserAt
        P hbeta hGammaOne) :
    SelectedTrueSplitEtaCorrelatedDatumDSOAt P := by
  intro targetEpsilon hTarget etaKT thirdEta delta0
    hEtaKT hEtaKTCap hThirdEta hThirdCap hDelta0 hDelta0Half
    hKTExact hKTRelative hFExact hFRelative hCorrelation
  obtain ⟨highDelta0, hHighDelta0, hClose⟩ :=
    hHighCloser targetEpsilon hTarget etaKT thirdEta delta0
      hEtaKT hEtaKTCap hThirdEta hThirdCap hDelta0 hDelta0Half
      hKTExact hKTRelative hFExact hFRelative hCorrelation
  let baseDelta0 : NNReal :=
    endpointIdentityCorrelatedSameCoreHighBaseThreshold P etaKT delta0
  let rawDelta0 : NNReal := min highDelta0 baseDelta0
  have hBaseDelta0 : 0 < baseDelta0 := by
    dsimp only [baseDelta0]
    exact endpointIdentityCorrelatedSameCoreHighBaseThreshold_pos
      P etaKT hDelta0
  have hRawDelta0 : 0 < rawDelta0 := by
    dsimp only [rawDelta0]
    exact lt_min hHighDelta0 hBaseDelta0
  refine ⟨rawDelta0, hRawDelta0, ?_⟩
  intro delta index _ _ D hD hdelta hFOutput
  have hdeltaHigh : delta <= highDelta0 :=
    hdelta.trans (by
      dsimp only [rawDelta0]
      exact min_le_left _ _)
  have hdeltaBase : delta <= baseDelta0 :=
    hdelta.trans (by
      dsimp only [rawDelta0]
      exact min_le_right _ _)
  have hdelta0' : delta <= delta0 :=
    hdeltaBase.trans (by
      dsimp only [baseDelta0,
        endpointIdentityCorrelatedSameCoreHighBaseThreshold]
      exact min_le_left _ _)
  have hrestOne : delta <=
      min (endpointIdentityFirstCrossingImpossibleThreshold P)
        (min (lowFreshCorrelatedPowerThreshold etaKT (P.eta 0))
          (min (lowFreshLongIntervalBaseScaleThreshold P)
            (endpointIdentitySourceTauCordobaPowerThreshold
              (P.eta 0)))) :=
    hdeltaBase.trans (by
      dsimp only [baseDelta0,
        endpointIdentityCorrelatedSameCoreHighBaseThreshold]
      exact min_le_right _ _)
  have hselectorSmall : delta <=
      endpointIdentityFirstCrossingImpossibleThreshold P :=
    hrestOne.trans (min_le_left _ _)
  have hrestTwo : delta <=
      min (lowFreshCorrelatedPowerThreshold etaKT (P.eta 0))
        (min (lowFreshLongIntervalBaseScaleThreshold P)
          (endpointIdentitySourceTauCordobaPowerThreshold (P.eta 0))) :=
    hrestOne.trans (min_le_right _ _)
  have hsmallPower : delta <=
      lowFreshCorrelatedPowerThreshold etaKT (P.eta 0) :=
    hrestTwo.trans (min_le_left _ _)
  have hrestThree : delta <=
      min (lowFreshLongIntervalBaseScaleThreshold P)
        (endpointIdentitySourceTauCordobaPowerThreshold (P.eta 0)) :=
    hrestTwo.trans (min_le_right _ _)
  have hsmallBase : delta <= lowFreshLongIntervalBaseScaleThreshold P :=
    hrestThree.trans (min_le_left _ _)
  have hautomaticSmall : delta <=
      endpointIdentitySourceTauCordobaPowerThreshold (P.eta 0) :=
    hrestThree.trans (min_le_right _ _)
  have hnormalizedDelta0 : delta / 8 <= delta0 :=
    (div_le_self (show 0 <= delta from bot_le)
      (by norm_num : (1 : NNReal) <= 8)).trans hdelta0'
  have hOutputCap : selectedTrueSplitOutputEta P thirdEta <= P.eta 0 :=
    selectedTrueSplitOutputEta_le_eta_zero P hThirdEta hThirdCap
  let W := automaticNormalizedLongCoreWitness
    D hD P hbeta hGammaOne hselectorSmall hFOutput
  let Sseq := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let KT := endpointIdentitySourceTauPackingKatzTaoConstant
    delta (Sseq.tau W.m)
  have hAutomatic := endpointIdentity_directSameOccurrenceAutomaticInputs
    D hD P W (P.eta_pos 0) hautomaticSmall
  have hKT : IsKatzTao KT
      (tauScaleCover
        (fullRefinementDatum D)
        (identityRadiusCoherentCover (fullRefinementDatum D).family)
        Sseq W).activeCoarseFamily := by
    dsimp only at hAutomatic
    simpa only [KT, Sseq] using hAutomatic.2.2.1
  have hsplit :=
    exists_endpointIdentity_correlated_dividingScaleOutput_or_sameCoreOccurrenceWeightedCordoba_massStrengthened_of_gamma_le_one
      (etaKT := etaKT)
      (outputEta := selectedTrueSplitOutputEta P thirdEta)
      (delta0 := delta0)
      D hD P hKTExact W W.stage W.stage_le hbeta hGammaOne
        hTarget.le hEtaKT hEtaKTCap hOutputCap hCorrelation
        hnormalizedDelta0 hsmallPower hsmallBase hFOutput
        (1 : NNReal) (by norm_num) KT hKT
  unfold
    EndpointIdentitySameCoreOccurrenceWeightedCordobaMassStrengthenedConclusion
    at hsplit
  rcases hsplit with hLow | hHigh
  · exact hLow
  · have hPointCloser : EndpointIdentityExactSameCoreHighCloserAt
        D hD P W ((delta : ENNReal) ^ (-(etaKT / 8)))
          1 (by norm_num) KT targetEpsilon := by
      simpa only [W, Sseq, KT] using
        (hClose delta index D hD hdeltaHigh hselectorSmall
          hautomaticSmall hFOutput)
    apply hPointCloser
    exact Or.inr hHigh

#print axioms EndpointIdentityExactSameCoreHighPayloadAt
#print axioms EndpointIdentityExactSameCoreHighCloserAt
#print axioms SelectedTrueSplitEtaExactSameCoreAutomaticHighCloserAt
#print axioms endpointIdentityCorrelatedSameCoreHighBaseThreshold_pos
#print axioms
  selectedTrueSplitEtaCorrelatedDatumDSOAt_of_exactSameCoreAutomaticHighCloser

end
end Family8EndpointIdentityCorrelatedSameCoreHighCloserDatumAdapterV1
