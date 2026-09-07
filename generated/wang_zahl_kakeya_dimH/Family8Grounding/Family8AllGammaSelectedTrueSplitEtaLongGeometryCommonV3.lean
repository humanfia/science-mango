import Family8Grounding.Family8AllGammaSelectedTrueSplitEtaLongGeometryCommonV2
import Family8Grounding.Family8SelectedTrueSplitOutputEtaKTCorrelationV1

/-!
# Correlated datum-level selected-output interface for the all-gamma merge, V3

The V2 datum callback receives `etaKT` and the selected source exponent as
independent parameters.  Some downstream geometric providers need the
sixteen copies of that selected exponent to fit inside the same `etaKT`
budget.  This successor keeps the V2 callback unchanged except for exposing
that correlation as one additional premise.

At the top level, the third exponent is therefore the minimum of the raw
Frostman exponent, the parameter-ladder cap, and half of `etaKT`.  The final
Katz--Tao-to-Frostman conclusion is unchanged.
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal NNReal

namespace Family8AllGammaSelectedTrueSplitEtaLongGeometryCommonV3

open Submission.Kakeya.ConvexGeometry
open Family8AllGammaSelectedTrueSplitEtaLongGeometryCommonV2
open Family8AllFrostmanFixedNuBranchOrchestrationV2
open Family8AllFrostmanStickyUnionProducerV1
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8FullRefinementActualDatumV1
open Family8GeneralizedScaleTrivialBranchV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParameterCappedOutputEtaStrongFrostmanLongCoreOnlyMainLemmaV1
open Family8ParameterLadderV1
open Family8ParameterSelectedTrueSplitEtaStrongFrostmanLongCoreOnlyMainLemmaV3
open Family8RelativeScaleFixedNuEndpointOrchestrationV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open Family8SelectedTrueSplitOutputEtaKTCorrelationV1

noncomputable section

/-- The V2 datum-level callback with the selected-output/`etaKT` correlation
made available to the downstream provider.  All other inputs and the
target-loss DSO output are identical to V2. -/
def SelectedTrueSplitEtaCorrelatedDatumDSOAt
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) : Prop :=
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
      exists rawDelta0 : NNReal, 0 < rawDelta0 /\
        forall (delta : NNReal) (index : Type)
          [Fintype index] [DecidableEq index]
          (D : ActualTubeDatum delta index) (_hD : D.IsAdmissible),
            delta <= rawDelta0 ->
            FrostmanHypotheses D
              (selectedTrueSplitOutputEta P thirdEta) ->
            DividingScaleOutput D P targetEpsilon

/-- Existential branch-local ladder form of the correlated datum callback. -/
abbrev SelectedTrueSplitEtaCorrelatedHDatumDSO
    (beta gamma : Real) : Prop :=
  exists epsilon0 : Real,
  exists P : ParameterLadder epsilon0 beta gamma,
    SelectedTrueSplitEtaCorrelatedDatumDSOAt P

/-! ## Compatibility with the V2 provider -/

/-- A V2 datum provider is automatically a correlated provider: the latter
receives one additional proved fact but asks for the identical DSO output.
This adapter keeps legacy branch implementations reusable while new low
implementations may consume the correlation. -/
theorem selectedTrueSplitEtaCorrelatedDatumDSOAt_of_datumDSOAt
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (hDatum : SelectedTrueSplitEtaDatumDSOAt P) :
    SelectedTrueSplitEtaCorrelatedDatumDSOAt P := by
  intro targetEpsilon hTarget etaKT thirdEta delta0
    hEtaKT hEtaKTCap hThirdEta hThirdCap hDelta0 hDelta0Half
    hKTExact hKTRelative hFExact hFRelative _hCorrelation
  exact hDatum targetEpsilon hTarget etaKT thirdEta delta0
    hEtaKT hEtaKTCap hThirdEta hThirdCap hDelta0 hDelta0Half
    hKTExact hKTRelative hFExact hFRelative

/-- Existential branch-local form of the V2 compatibility adapter. -/
theorem selectedTrueSplitEtaCorrelatedHDatumDSO_of_hDatumDSO
    {beta gamma : Real}
    (hDatum : SelectedTrueSplitEtaHDatumDSO beta gamma) :
    SelectedTrueSplitEtaCorrelatedHDatumDSO beta gamma := by
  rcases hDatum with ⟨epsilon0, P, hP⟩
  exact ⟨epsilon0, P,
    selectedTrueSplitEtaCorrelatedDatumDSOAt_of_datumDSOAt P hP⟩

/-- Main Lemma 1 from an all-parameter correlated datum-level provider.

The raw parameter producer is unchanged from V2.  Only the final choice of
`thirdEta` is refined to `selectedTrueSplitTopThirdEta`, which supplies the
additional correlation premise without strengthening the theorem's public
conclusion. -/
theorem mainLemmaOne_of_selectedTrueSplitEtaCorrelatedHDatumDSOProvider
    (hProvider : forall (beta gamma : Real)
      (_hbeta : 0 < beta) (_hgap : beta < gamma) (_hgamma : gamma <= 1),
        SelectedTrueSplitEtaCorrelatedHDatumDSO beta gamma)
    (beta : Real) :
    KatzTaoProperty beta -> FrostmanProperty beta := by
  apply
    Family8NonzeroMassParameterEndpointOrchestrationV3.mainLemmaOne_of_parameterLadderNonzeroMassEndpoint
  intro target source hTargetPos hTargetSource hSourceOne hKT hF
  obtain ⟨epsilon0, P, hEndpoint⟩ :=
    hProvider target source hTargetPos hTargetSource hSourceOne
  refine ⟨epsilon0, P, ?_⟩
  intro targetEpsilon hTargetEpsilon
  have hSourceZero : 0 <= source := by linarith
  obtain ⟨etaKT, etaThirdRaw, delta0,
      hetaKT, hetaKTCap, hetaThirdRaw, hdelta0, hdelta0Half,
      hKTExact, hKTRelative,
      _hFExactQuarter, _hFRelativeQuarter,
      hFExactSourceRaw, hFRelativeSourceRaw⟩ :=
    exists_cappedOutputEta_split_source_parameters_with_strong_frostman
      P hKT hF hTargetPos.le hSourceZero hSourceOne hTargetEpsilon
  let thirdEta : Real :=
    selectedTrueSplitTopThirdEta P etaThirdRaw etaKT
  have hThirdEtaBundle :
      0 < thirdEta /\
        thirdEta <= etaThirdRaw /\
        thirdEta <= P.eta 0 /\
        16 * selectedTrueSplitOutputEta P thirdEta <= etaKT := by
    dsimp only [thirdEta]
    exact selectedTrueSplitTopThirdEta_correlation_bundle
      P hetaThirdRaw hetaKT
  rcases hThirdEtaBundle with
    ⟨hThirdEtaPos, hThirdEtaLeRaw, hThirdEtaCap, hOutputEtaKT⟩
  have hFExactThird : FrostmanAtParameters source
      (sectionEightSourceLoss P targetEpsilon) thirdEta delta0 :=
    Family8FrostmanHypothesesLossMonotonicityV1.frostmanAtParameters_of_eta_le
      hFExactSourceRaw hThirdEtaLeRaw
  have hFRelativeThird : FrostmanAtRelativeScaleParameters source
      (sectionEightSourceLoss P targetEpsilon) thirdEta delta0 :=
    Family8RelativeScaleParameterMonotonicityV2.frostmanAtRelativeScaleParameters_of_eta_le
      hFRelativeSourceRaw hThirdEtaLeRaw
  have hEpsilonOne : P.epsilon < 1 :=
    Family8EndpointIdentityCoreSelectorV2.parameterLadder_epsilon_lt_one
      P hTargetPos hSourceOne
  have hOutputEtaPos :
      0 < selectedTrueSplitOutputEta P thirdEta :=
    selectedTrueSplitOutputEta_pos P hEpsilonOne hThirdEtaPos
  have hOutputEtaCap :
      selectedTrueSplitOutputEta P thirdEta <= P.eta 0 :=
    selectedTrueSplitOutputEta_le_eta_zero
      P hThirdEtaPos hThirdEtaCap
  obtain ⟨rawDelta0, hRawDelta0, hDatum⟩ :=
    hEndpoint targetEpsilon hTargetEpsilon etaKT thirdEta delta0
      hetaKT hetaKTCap hThirdEtaPos hThirdEtaCap hdelta0 hdelta0Half
      hKTExact hKTRelative hFExactThird hFRelativeThird hOutputEtaKT
  let finalRawDelta0 : NNReal :=
    min rawDelta0 (allFrostmanFixedNuThreshold P targetEpsilon)
  have hFinalRawDelta0 : 0 < finalRawDelta0 := by
    dsimp only [finalRawDelta0]
    exact lt_min hRawDelta0
      (allFrostmanFixedNuThreshold_pos P)
  refine ⟨selectedTrueSplitOutputEta P thirdEta, finalRawDelta0,
    hOutputEtaPos, hFinalRawDelta0, ?_⟩
  intro delta index _ _ D hD hdelta hFOutput _hmass
  have hdeltaRaw : delta <= rawDelta0 :=
    hdelta.trans (min_le_left _ _)
  have hdeltaAll : delta <=
      allFrostmanFixedNuThreshold P targetEpsilon :=
    hdelta.trans (min_le_right _ _)
  have hRequested : DividingScaleOutput D P targetEpsilon :=
    hDatum delta index D hD hdeltaRaw hFOutput
  rcases hRequested with hUnion | ⟨j, outerLoss, hStage,
      hOuterLoss, hAverage⟩
  · exact averageMultiplicity_le_fixedNuRHS_of_allFrostman
      P hTargetPos.le (by linarith) (by linarith) D hD hdeltaAll
        hTargetEpsilon hUnion
  · exact Family8OuterMiddleFixedNuEndpointOrchestrationV1.averageMultiplicity_le_fixedNuRHS_of_outerThree_middleTen
      P j hStage hTargetPos.le hSourceOne D hD hOutputEtaCap
        hFOutput hTargetEpsilon outerLoss hOuterLoss hAverage

#print axioms SelectedTrueSplitEtaCorrelatedDatumDSOAt
#print axioms SelectedTrueSplitEtaCorrelatedHDatumDSO
#print axioms selectedTrueSplitEtaCorrelatedDatumDSOAt_of_datumDSOAt
#print axioms selectedTrueSplitEtaCorrelatedHDatumDSO_of_hDatumDSO
#print axioms
  mainLemmaOne_of_selectedTrueSplitEtaCorrelatedHDatumDSOProvider

end
end Family8AllGammaSelectedTrueSplitEtaLongGeometryCommonV3
