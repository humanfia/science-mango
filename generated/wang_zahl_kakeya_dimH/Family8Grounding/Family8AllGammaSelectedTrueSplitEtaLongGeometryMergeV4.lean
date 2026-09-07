import Family8Grounding.Family8AllGammaSelectedTrueSplitEtaLongGeometryCommonV1
import Family8Grounding.Family8EndpointIdentityLowGammaGraphFrozenGroundedRunHLongGeometryAdapterV3SelectedLocalCap
import Family8Grounding.Family8EndpointIdentityHighGammaSelectedTrueSplitEtaRetainedXAdapterV1

/-!
# Consumer-weak all-gamma merge for the selected true split, V4

The low branch is exposed at the literal common LongGeometry conclusion.  A
separate constructor below obtains that conclusion from the strict selected
local-cap V3 context, so the merge no longer requires the older global
`KatzTaoHypotheses` payload.

The high branch splits on the exact refined-card power used by the automatic
endpoint.  The card-small branch is closed internally by the retained-card
producer.  Consequently the only high provider field is a DSO on the
card-large branch; it is not asked to prove the stronger X-power estimate.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal NNReal

namespace Family8AllGammaSelectedTrueSplitEtaLongGeometryMergeV4

open Submission.Kakeya.ConvexGeometry
open Family8AllFrostmanStickyUnionProducerV1
open Family8AllGammaSelectedTrueSplitEtaLongGeometryCommonV1
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointIdentityHighGammaSelectedTrueSplitEtaRetainedXAdapterV1
open Family8EndpointIdentityHighGammaSelectedTrueSplitEtaXPowerV4
open Family8EndpointIdentityLowGammaGraphFrozenGroundedRunHLongGeometryAdapterV3SelectedLocalCap
open Family8EndpointIdentityLowGammaGroundedRunHLongGeometryAdapterV1
open Family8EndpointIdentityParameterLadderProducerV2
open Family8FullRefinementActualDatumV1
open Family8GeneralizedScaleTrivialBranchV1
open Family8HighGammaParameterLadderV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8ParameterSelectedTrueSplitEtaStrongFrostmanLongCoreOnlyMainLemmaV3
open Family8RelativeScaleFixedNuEndpointOrchestrationV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

/-! ## Low branch: strict selected local-cap context to the exact consumer -/

/-- The V3 selected-local-cap adapter supplies precisely the common selected
LongGeometry conclusion.  The output exponent is chosen before invoking the
capped source-exponent callback; no source KT conjunction is reintroduced. -/
theorem selectedTrueSplitEta_hLongGeometry_of_lowGammaLocalCapContext
    {beta gamma : Real}
    (hbeta : 0 < beta) (hgap : beta < gamma)
    (hgamma : gamma <= 1) (hlow : gamma <= (2 : Real) / 3)
    (hContext : LowGammaSelectedActualGraphFrozenLedgerLocalCapFullContextProducer
      (endpointIdentityParameterLadder hbeta hgap)) :
    SelectedTrueSplitEtaHLongGeometry beta gamma := by
  obtain ⟨epsilon0, P, hCapped⟩ :=
    cappedStrongFrostman_hLongGeometry_of_selectedActualGraphFrozenLedgerLocalCapContext
      hbeta hgap hlow hContext
  refine ⟨epsilon0, P, ?_⟩
  intro targetEpsilon hTarget etaKT thirdEta delta0
    hEtaKT hEtaKTCap hThirdEta hThirdCap hDelta0 hDelta0Half
    hKTExact hKTRelative hFExactThird hFRelativeThird
  let outputEta := selectedTrueSplitOutputEta P thirdEta
  have hEpsilonOne : P.epsilon < 1 :=
    Family8EndpointIdentityCoreSelectorV2.parameterLadder_epsilon_lt_one
      P hbeta hgamma
  have hOutputEta : 0 < outputEta := by
    dsimp only [outputEta]
    exact selectedTrueSplitOutputEta_pos P hEpsilonOne hThirdEta
  have hOutputThird : outputEta < thirdEta := by
    dsimp only [outputEta]
    exact selectedTrueSplitOutputEta_lt_thirdEta P hThirdEta
  have hOutputCap : outputEta <= P.eta 0 :=
    hOutputThird.le.trans hThirdCap
  have hFExactOutput : FrostmanAtParameters gamma
      (sectionEightSourceLoss P targetEpsilon) outputEta delta0 :=
    Family8FrostmanHypothesesLossMonotonicityV1.frostmanAtParameters_of_eta_le
      hFExactThird hOutputThird.le
  have hFRelativeOutput : FrostmanAtRelativeScaleParameters gamma
      (sectionEightSourceLoss P targetEpsilon) outputEta delta0 :=
    Family8RelativeScaleParameterMonotonicityV2.frostmanAtRelativeScaleParameters_of_eta_le
      hFRelativeThird hOutputThird.le
  obtain ⟨rawDelta0, hRawDelta0, hDatum⟩ :=
    hCapped targetEpsilon hTarget etaKT outputEta delta0
      hEtaKT hEtaKTCap hOutputEta hOutputCap hDelta0 hDelta0Half
      hKTExact hKTRelative hFExactOutput hFRelativeOutput
  refine ⟨rawDelta0, hRawDelta0, ?_⟩
  intro delta index _ _ D hD hdelta hFOutput W
  have hmass : D.shading.shadingMass ≠ 0 := by
    have hfloor :=
      delta_rpow_two_eta_le_shadingMass_of_frostman D hD hFOutput
    exact ne_of_gt ((ENNReal.rpow_pos
      (ENNReal.coe_pos.mpr hD.delta_pos) ENNReal.coe_ne_top).trans_le hfloor)
  exact hDatum delta index D hD hdelta hFOutput hmass W

/-! ## High branch: internal card-small closure, external card-large DSO -/

/-- The weakest missing high-branch interface after the exact cardinal split.
Every scalar and property premise is already present in the common callback;
the provider proves only its card-large DSO conclusion. -/
abbrev AutomaticHighGammaSelectedTrueSplitEtaCardLargeDSOProducer
    {epsilon0 beta gamma : Real}
    (H : HighGammaParameterLadder epsilon0 beta gamma) : Prop :=
  forall targetEpsilon : Real, forall _hTarget : 0 < targetEpsilon,
  forall etaKT thirdEta : Real, forall delta0 : NNReal,
  forall _hEtaKT : 0 < etaKT,
  forall _hEtaKTCap :
    etaKT <= H.ladder.epsilon ^ 2 * H.ladder.eta 0 / 32,
  forall _hThirdEta : 0 < thirdEta,
  forall _hThirdCap : thirdEta <= H.ladder.eta 0,
  forall _hDelta0 : 0 < delta0,
  forall _hDelta0Half : delta0 <= (2 : NNReal)⁻¹,
  forall _hKTExact : KatzTaoAtParameters beta
    (sectionEightFixedNu H.ladder) etaKT delta0,
  forall _hKTRelative : KatzTaoAtRelativeScaleParameters beta
    (sectionEightFixedNu H.ladder) etaKT delta0,
  forall _hFExact : FrostmanAtParameters gamma
    (sectionEightSourceLoss H.ladder targetEpsilon) thirdEta delta0,
  forall _hFRelative : FrostmanAtRelativeScaleParameters gamma
    (sectionEightSourceLoss H.ladder targetEpsilon) thirdEta delta0,
  forall (delta : NNReal) (index : Type)
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (_hD : D.IsAdmissible),
  forall _hdeltaRaw : delta <= highGammaSelectedTrueSplitEtaRawDelta0
    H targetEpsilon etaKT thirdEta delta0,
  forall _hFOutput : FrostmanHypotheses D
    (selectedTrueSplitOutputEta H.ladder thirdEta),
    Not ((Fintype.card index : ENNReal) <=
      (delta : ENNReal) ^
        (-selectedTrueSplitCardScaleEta H.ladder thirdEta)) ->
    DividingScaleOutput D H.ladder
      (4 * sectionEightSourceLoss H.ladder targetEpsilon)

/-- Turn a card-large-only provider into the exact common high-gamma
LongGeometry interface.  The complementary branch is the existing exact
retained-card endpoint, on the same datum and automatic witness. -/
theorem selectedTrueSplitEta_hLongGeometry_of_highGammaCardLargeDSO
    {epsilon0 beta gamma : Real}
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hLarge : AutomaticHighGammaSelectedTrueSplitEtaCardLargeDSOProducer
      H) :
    SelectedTrueSplitEtaHLongGeometry beta gamma := by
  refine ⟨epsilon0, H.ladder, ?_⟩
  intro targetEpsilon hTarget etaKT thirdEta delta0
    hEtaKT hEtaKTCap hThirdEta hThirdCap hDelta0 hDelta0Half
    hKTExact hKTRelative hFExact hFRelative
  let rawDelta0 := highGammaSelectedTrueSplitEtaRawDelta0
    H targetEpsilon etaKT thirdEta delta0
  have hRawDelta0 : 0 < rawDelta0 := by
    dsimp only [rawDelta0]
    exact highGammaSelectedTrueSplitEtaRawDelta0_pos
      H hbeta hgamma targetEpsilon etaKT thirdEta hDelta0
  refine ⟨rawDelta0, hRawDelta0, ?_⟩
  intro delta index _ _ D hD hdelta hFOutput _W
  have hdeltaRaw : delta <= highGammaSelectedTrueSplitEtaRawDelta0
      H targetEpsilon etaKT thirdEta delta0 := by
    simpa only [rawDelta0] using hdelta
  by_cases hCard : (Fintype.card index : ENNReal) <=
      (delta : ENNReal) ^
        (-selectedTrueSplitCardScaleEta H.ladder thirdEta)
  · exact
      dividingScaleOutput_of_endpointIdentity_highGamma_selectedTrueSplitEta_automatic_of_refinedCardPower
        H hbeta hgamma targetEpsilon etaKT thirdEta delta0
          hTarget hThirdEta hThirdCap D hD hdeltaRaw hFOutput hFExact hCard
  · exact hLarge targetEpsilon hTarget etaKT thirdEta delta0
      hEtaKT hEtaKTCap hThirdEta hThirdCap hDelta0 hDelta0Half
      hKTExact hKTRelative hFExact hFRelative
      delta index D hD hdeltaRaw hFOutput hCard

/-! ## Consumer-weak all-gamma merge -/

/-- Branch-local high-gamma initial parameter. -/
def allGammaSelectedHighGammaEpsilon0 (beta gamma : Real) : Real :=
  (gamma - beta) / 64

theorem allGammaSelectedHighGammaEpsilon0_pos
    {beta gamma : Real} (hgap : beta < gamma) :
    0 < allGammaSelectedHighGammaEpsilon0 beta gamma := by
  unfold allGammaSelectedHighGammaEpsilon0
  positivity

abbrev AllGammaSelectedCanonicalHighGammaCertificate
    {beta gamma : Real} (hbeta : 0 < beta) (hgap : beta < gamma)
    (hhigh : (2 : Real) / 3 < gamma) :
    HighGammaParameterLadder
      (allGammaSelectedHighGammaEpsilon0 beta gamma) beta gamma :=
  canonicalHighGammaCertificate
    (allGammaSelectedHighGammaEpsilon0_pos hgap) hbeta hgap hhigh

/-- V4 asks each branch for no more than the branch of the common consumer
that is not already closed mechanically. -/
structure AllGammaSelectedTrueSplitEtaBranchProviders where
  lowGamma :
    forall (beta gamma : Real)
      (_hbeta : 0 < beta) (_hgap : beta < gamma) (_hgamma : gamma <= 1)
      (_hlow : gamma <= (2 : Real) / 3),
      SelectedTrueSplitEtaHLongGeometry beta gamma
  highGammaCardLarge :
    forall (beta gamma : Real)
      (hbeta : 0 < beta) (hgap : beta < gamma) (_hgamma : gamma <= 1)
      (hhigh : (2 : Real) / 3 < gamma),
      AutomaticHighGammaSelectedTrueSplitEtaCardLargeDSOProducer
        (AllGammaSelectedCanonicalHighGammaCertificate hbeta hgap hhigh)

theorem selectedTrueSplitEta_hLongGeometry_of_allGammaBranchProviders
    (providers : AllGammaSelectedTrueSplitEtaBranchProviders)
    (beta gamma : Real)
    (hbeta : 0 < beta) (hgap : beta < gamma) (hgamma : gamma <= 1) :
    SelectedTrueSplitEtaHLongGeometry beta gamma := by
  by_cases hlow : gamma <= (2 : Real) / 3
  · exact providers.lowGamma beta gamma hbeta hgap hgamma hlow
  · have hhigh : (2 : Real) / 3 < gamma := lt_of_not_ge hlow
    let H : HighGammaParameterLadder
        (allGammaSelectedHighGammaEpsilon0 beta gamma) beta gamma :=
      AllGammaSelectedCanonicalHighGammaCertificate hbeta hgap hhigh
    have hLarge :
        AutomaticHighGammaSelectedTrueSplitEtaCardLargeDSOProducer
          H := by
      dsimp only [H]
      exact providers.highGammaCardLarge
        beta gamma hbeta hgap hgamma hhigh
    exact selectedTrueSplitEta_hLongGeometry_of_highGammaCardLargeDSO
      H hbeta hgamma hLarge

theorem mainLemmaOne_of_allGammaSelectedTrueSplitEtaBranchProviders
    (providers : AllGammaSelectedTrueSplitEtaBranchProviders)
    (beta : Real) :
    KatzTaoProperty beta -> FrostmanProperty beta := by
  apply mainLemmaOne_of_selectedTrueSplitEtaHLongGeometryProvider
  intro target source hTarget hGap hSource
  exact selectedTrueSplitEta_hLongGeometry_of_allGammaBranchProviders
    providers target source hTarget hGap hSource

#print axioms
  selectedTrueSplitEta_hLongGeometry_of_lowGammaLocalCapContext
#print axioms AutomaticHighGammaSelectedTrueSplitEtaCardLargeDSOProducer
#print axioms
  selectedTrueSplitEta_hLongGeometry_of_highGammaCardLargeDSO
#print axioms AllGammaSelectedTrueSplitEtaBranchProviders
#print axioms
  selectedTrueSplitEta_hLongGeometry_of_allGammaBranchProviders
#print axioms
  mainLemmaOne_of_allGammaSelectedTrueSplitEtaBranchProviders

end
end Family8AllGammaSelectedTrueSplitEtaLongGeometryMergeV4
