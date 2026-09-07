import Family8Grounding.Family8AllGammaSelectedTrueSplitEtaLongGeometryCommonV2
import Family8Grounding.Family8AllGammaSelectedTrueSplitEtaLongGeometryMergeV4
import Family8Grounding.Family8DividingScaleOutputTargetMonotonicityV1

/-!
# Datum-level all-gamma selected-split merge, V5

This successor removes the three avoidable strengthenings left in V4.

* Neither branch receives an external normalized LongCore witness.
* The high card-large producer may choose an additional positive terminal
  scale; the merge intersects it with the automatic high-gamma threshold.
* The public branch conclusion is the DSO at `targetEpsilon`.  The existing
  card-small endpoint is weakened to that target internally.

The low selected-local-cap implementation still proves the older effective
loss output internally.  Its automatic endpoint witness and target-loss
monotonicity are discharged in the adapter below, not exposed to the common
consumer.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal NNReal

namespace Family8AllGammaSelectedTrueSplitEtaLongGeometryMergeV5

open Submission.Kakeya.ConvexGeometry
open Family8AllGammaSelectedTrueSplitEtaLongGeometryCommonV2
open Family8AllGammaSelectedTrueSplitEtaLongGeometryMergeV4
open Family8DividingScaleOutputTargetMonotonicityV1
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointIdentityFirstCrossingImpossibleV1
open Family8EndpointIdentityHighGammaParentwiseLongCoreAutomaticV1
open Family8EndpointIdentityHighGammaSelectedTrueSplitEtaRetainedXAdapterV1
open Family8EndpointIdentityHighGammaSelectedTrueSplitEtaXPowerV4
open Family8EndpointIdentityLowGammaGraphFrozenGroundedRunHLongGeometryAdapterV3SelectedLocalCap
open Family8FullRefinementActualDatumV1
open Family8GeneralizedScaleTrivialBranchV1
open Family8HighGammaParameterLadderV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParameterLadderV1
open Family8ParameterSelectedTrueSplitEtaStrongFrostmanLongCoreOnlyMainLemmaV3
open Family8RelativeScaleFixedNuEndpointOrchestrationV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3

noncomputable section

/-! ## Low branch: eliminate the stale callback witness -/

/-- The selected local-cap low implementation at the datum-level target-loss
consumer.  The old callback is instantiated with the canonical automatic
witness below the selector threshold, and its effective-loss DSO is weakened
to the requested target internally.

The separate `gamma <= 1` premise is omitted: it follows from the low-branch
gate `gamma <= 2 / 3`. -/
theorem selectedTrueSplitEta_hDatumDSO_of_lowGammaLocalCapContext
    {beta gamma : Real}
    (hbeta : 0 < beta) (hgap : beta < gamma)
    (hlow : gamma <= (2 : Real) / 3)
    (hContext : LowGammaSelectedActualGraphFrozenLedgerLocalCapFullContextProducer
      (Family8EndpointIdentityParameterLadderProducerV2.endpointIdentityParameterLadder
        hbeta hgap)) :
    SelectedTrueSplitEtaHDatumDSO beta gamma := by
  have hgamma : gamma <= 1 := by linarith
  obtain ⟨epsilon0, P, hLong⟩ :=
    selectedTrueSplitEta_hLongGeometry_of_lowGammaLocalCapContext
      hbeta hgap hgamma hlow hContext
  refine ⟨epsilon0, P, ?_⟩
  intro targetEpsilon hTarget etaKT thirdEta delta0
    hEtaKT hEtaKTCap hThirdEta hThirdCap hDelta0 hDelta0Half
    hKTExact hKTRelative hFExact hFRelative
  obtain ⟨rawDelta0, hRawDelta0, hDatum⟩ :=
    hLong targetEpsilon hTarget etaKT thirdEta delta0
      hEtaKT hEtaKTCap hThirdEta hThirdCap hDelta0 hDelta0Half
      hKTExact hKTRelative hFExact hFRelative
  let datumRawDelta0 : NNReal :=
    min rawDelta0 (endpointIdentityFirstCrossingImpossibleThreshold P)
  have hDatumRawDelta0 : 0 < datumRawDelta0 := by
    dsimp only [datumRawDelta0]
    exact lt_min hRawDelta0
      (endpointIdentityFirstCrossingImpossibleThreshold_pos P)
  refine ⟨datumRawDelta0, hDatumRawDelta0, ?_⟩
  intro delta index _ _ D hD hdelta hFOutput
  have hdeltaRaw : delta <= rawDelta0 :=
    hdelta.trans (by
      dsimp only [datumRawDelta0]
      exact min_le_left _ _)
  have hselectorSmall : delta <=
      endpointIdentityFirstCrossingImpossibleThreshold P :=
    hdelta.trans (by
      dsimp only [datumRawDelta0]
      exact min_le_right _ _)
  let W := automaticNormalizedLongCoreWitness
    D hD P hbeta hgamma hselectorSmall hFOutput
  have hEffective : DividingScaleOutput D P
      (4 * sectionEightSourceLoss P targetEpsilon) :=
    hDatum delta index D hD hdeltaRaw hFOutput W
  have hEffectiveLe :
      4 * sectionEightSourceLoss P targetEpsilon <= targetEpsilon := by
    nlinarith [sectionEightSourceLoss_le_targetQuarter P targetEpsilon]
  exact dividingScaleOutput_mono_targetEpsilon
    D hD P hEffectiveLe hEffective

/-! ## High branch: provider-chosen threshold and target-loss DSO -/

/-- The remaining high-gamma seam after the exact refined-card split.

For each already supplied top parameter context, the analytic producer may
choose its own positive terminal scale.  It is invoked only below the
intersection of that scale and the automatic high-gamma threshold, and only
on the literal card-large complement. -/
abbrev AutomaticHighGammaSelectedTrueSplitEtaCardLargeTargetDSOProducer
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
    exists cardLargeDelta0 : NNReal, 0 < cardLargeDelta0 /\
      forall (delta : NNReal) (index : Type)
        [Fintype index] [DecidableEq index]
        (D : ActualTubeDatum delta index) (_hD : D.IsAdmissible),
      forall _hdelta : delta <= min
        (highGammaSelectedTrueSplitEtaRawDelta0
          H targetEpsilon etaKT thirdEta delta0)
        cardLargeDelta0,
      forall _hFOutput : FrostmanHypotheses D
        (selectedTrueSplitOutputEta H.ladder thirdEta),
        Not ((Fintype.card index : ENNReal) <=
          (delta : ENNReal) ^
            (-selectedTrueSplitCardScaleEta H.ladder thirdEta)) ->
        DividingScaleOutput D H.ladder targetEpsilon

/-- Merge the automatic card-small endpoint with a card-large producer that
chooses its own positive terminal scale.  Both branches return the same
datum-level target-loss conclusion. -/
theorem selectedTrueSplitEta_hDatumDSO_of_highGammaCardLargeTargetDSO
    {epsilon0 beta gamma : Real}
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hLarge :
      AutomaticHighGammaSelectedTrueSplitEtaCardLargeTargetDSOProducer H) :
    SelectedTrueSplitEtaHDatumDSO beta gamma := by
  refine ⟨epsilon0, H.ladder, ?_⟩
  intro targetEpsilon hTarget etaKT thirdEta delta0
    hEtaKT hEtaKTCap hThirdEta hThirdCap hDelta0 hDelta0Half
    hKTExact hKTRelative hFExact hFRelative
  obtain ⟨cardLargeDelta0, hCardLargeDelta0, hLargeAt⟩ :=
    hLarge targetEpsilon hTarget etaKT thirdEta delta0
      hEtaKT hEtaKTCap hThirdEta hThirdCap hDelta0 hDelta0Half
      hKTExact hKTRelative hFExact hFRelative
  let rawDelta0 : NNReal := min
    (highGammaSelectedTrueSplitEtaRawDelta0
      H targetEpsilon etaKT thirdEta delta0)
    cardLargeDelta0
  have hRawDelta0 : 0 < rawDelta0 := by
    dsimp only [rawDelta0]
    exact lt_min
      (highGammaSelectedTrueSplitEtaRawDelta0_pos
        H hbeta hgamma targetEpsilon etaKT thirdEta hDelta0)
      hCardLargeDelta0
  refine ⟨rawDelta0, hRawDelta0, ?_⟩
  intro delta index _ _ D hD hdelta hFOutput
  have hdeltaHigh : delta <= highGammaSelectedTrueSplitEtaRawDelta0
      H targetEpsilon etaKT thirdEta delta0 :=
    hdelta.trans (by
      dsimp only [rawDelta0]
      exact min_le_left _ _)
  have hdeltaLarge : delta <= min
      (highGammaSelectedTrueSplitEtaRawDelta0
        H targetEpsilon etaKT thirdEta delta0)
      cardLargeDelta0 := by
    simpa only [rawDelta0] using hdelta
  by_cases hCard : (Fintype.card index : ENNReal) <=
      (delta : ENNReal) ^
        (-selectedTrueSplitCardScaleEta H.ladder thirdEta)
  · have hEffective : DividingScaleOutput D H.ladder
        (4 * sectionEightSourceLoss H.ladder targetEpsilon) :=
      dividingScaleOutput_of_endpointIdentity_highGamma_selectedTrueSplitEta_automatic_of_refinedCardPower
        H hbeta hgamma targetEpsilon etaKT thirdEta delta0
          hTarget hThirdEta hThirdCap D hD hdeltaHigh hFOutput hFExact hCard
    have hEffectiveLe :
        4 * sectionEightSourceLoss H.ladder targetEpsilon <=
          targetEpsilon := by
      nlinarith [sectionEightSourceLoss_le_targetQuarter
        H.ladder targetEpsilon]
    exact dividingScaleOutput_mono_targetEpsilon
      D hD H.ladder hEffectiveLe hEffective
  · exact hLargeAt delta index D hD hdeltaLarge hFOutput hCard

/-! ## Consumer-weak all-gamma merge -/

/-- The branch obligations at the exact datum-level consumer.  The low gate
does not repeat the derivable `gamma <= 1` premise. -/
structure AllGammaSelectedTrueSplitEtaDatumBranchProviders where
  lowGamma :
    forall (beta gamma : Real)
      (_hbeta : 0 < beta) (_hgap : beta < gamma)
      (_hlow : gamma <= (2 : Real) / 3),
      SelectedTrueSplitEtaHDatumDSO beta gamma
  highGammaCardLarge :
    forall (beta gamma : Real)
      (hbeta : 0 < beta) (hgap : beta < gamma) (_hgamma : gamma <= 1)
      (hhigh : (2 : Real) / 3 < gamma),
      AutomaticHighGammaSelectedTrueSplitEtaCardLargeTargetDSOProducer
        (AllGammaSelectedCanonicalHighGammaCertificate hbeta hgap hhigh)

theorem selectedTrueSplitEta_hDatumDSO_of_allGammaBranchProviders
    (providers : AllGammaSelectedTrueSplitEtaDatumBranchProviders)
    (beta gamma : Real)
    (hbeta : 0 < beta) (hgap : beta < gamma) (hgamma : gamma <= 1) :
    SelectedTrueSplitEtaHDatumDSO beta gamma := by
  by_cases hlow : gamma <= (2 : Real) / 3
  · exact providers.lowGamma beta gamma hbeta hgap hlow
  · have hhigh : (2 : Real) / 3 < gamma := lt_of_not_ge hlow
    let H : HighGammaParameterLadder
        (allGammaSelectedHighGammaEpsilon0 beta gamma) beta gamma :=
      AllGammaSelectedCanonicalHighGammaCertificate hbeta hgap hhigh
    have hLarge :
        AutomaticHighGammaSelectedTrueSplitEtaCardLargeTargetDSOProducer
          H := by
      dsimp only [H]
      exact providers.highGammaCardLarge
        beta gamma hbeta hgap hgamma hhigh
    exact selectedTrueSplitEta_hDatumDSO_of_highGammaCardLargeTargetDSO
      H hbeta hgamma hLarge

theorem mainLemmaOne_of_allGammaSelectedTrueSplitEtaDatumBranchProviders
    (providers : AllGammaSelectedTrueSplitEtaDatumBranchProviders)
    (beta : Real) :
    KatzTaoProperty beta -> FrostmanProperty beta := by
  apply mainLemmaOne_of_selectedTrueSplitEtaHDatumDSOProvider
  intro target source hTarget hGap hSource
  exact selectedTrueSplitEta_hDatumDSO_of_allGammaBranchProviders
    providers target source hTarget hGap hSource

#print axioms
  selectedTrueSplitEta_hDatumDSO_of_lowGammaLocalCapContext
#print axioms
  AutomaticHighGammaSelectedTrueSplitEtaCardLargeTargetDSOProducer
#print axioms
  selectedTrueSplitEta_hDatumDSO_of_highGammaCardLargeTargetDSO
#print axioms AllGammaSelectedTrueSplitEtaDatumBranchProviders
#print axioms
  selectedTrueSplitEta_hDatumDSO_of_allGammaBranchProviders
#print axioms
  mainLemmaOne_of_allGammaSelectedTrueSplitEtaDatumBranchProviders

end
end Family8AllGammaSelectedTrueSplitEtaLongGeometryMergeV5
