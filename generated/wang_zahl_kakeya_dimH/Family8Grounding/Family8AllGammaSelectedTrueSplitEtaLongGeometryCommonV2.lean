import Family8Grounding.Family8AllGammaSelectedTrueSplitEtaLongGeometryCommonV1
import Family8Grounding.Family8ParameterSelectedTrueSplitEtaStrongFrostmanLongCoreOnlyMainLemmaV4

/-!
# Datum-level selected-output interface for the all-gamma merge, V2

The V1 common interface retained an external normalized LongCore witness and
asked for a DSO at the smaller bookkeeping loss
`4 * sectionEightSourceLoss P targetEpsilon`.  Neither feature is present at
the actual datum consumer: both gamma branches choose their own witness, and
the final endpoint consumes a DSO at `targetEpsilon`.

This successor therefore exposes the literal datum-level target-loss
callback.  The proof below performs the same selected exponent and final
Frostman orchestration as the older LongCore connector, but contains no
external witness and no reverse target-loss strengthening.
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal NNReal

namespace Family8AllGammaSelectedTrueSplitEtaLongGeometryCommonV2

open Submission.Kakeya.ConvexGeometry
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

noncomputable section

/-- The selected-output callback at the actual datum boundary.  Its output
is the target-loss DSO itself; no independently supplied LongCore witness is
quantified and no smaller effective loss is demanded. -/
def SelectedTrueSplitEtaDatumDSOAt
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
      exists rawDelta0 : NNReal, 0 < rawDelta0 /\
        forall (delta : NNReal) (index : Type)
          [Fintype index] [DecidableEq index]
          (D : ActualTubeDatum delta index) (_hD : D.IsAdmissible),
            delta <= rawDelta0 ->
            FrostmanHypotheses D
              (selectedTrueSplitOutputEta P thirdEta) ->
            DividingScaleOutput D P targetEpsilon

/-- Existential branch-local ladder form of the datum-level callback. -/
abbrev SelectedTrueSplitEtaHDatumDSO (beta gamma : Real) : Prop :=
  exists epsilon0 : Real,
  exists P : ParameterLadder epsilon0 beta gamma,
    SelectedTrueSplitEtaDatumDSOAt P

/-- Main Lemma 1 from the literal datum-level selected-output callback.

This is the target-loss counterpart of the V4 datum connector.  The final
Frostman branches consume `DividingScaleOutput D P targetEpsilon` directly,
so no proof at `4 * sectionEightSourceLoss P targetEpsilon` is requested and
then weakened. -/
theorem mainLemmaOne_of_selectedTrueSplitEtaHDatumDSOProvider
    (hProvider : forall (beta gamma : Real)
      (_hbeta : 0 < beta) (_hgap : beta < gamma) (_hgamma : gamma <= 1),
        SelectedTrueSplitEtaHDatumDSO beta gamma)
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
  let thirdEta : Real := min etaThirdRaw (P.eta 0)
  have hThirdEtaPos : 0 < thirdEta := by
    dsimp only [thirdEta]
    exact lt_min hetaThirdRaw (P.eta_pos 0)
  have hThirdEtaLeRaw : thirdEta <= etaThirdRaw := by
    dsimp only [thirdEta]
    exact min_le_left _ _
  have hThirdEtaCap : thirdEta <= P.eta 0 := by
    dsimp only [thirdEta]
    exact min_le_right _ _
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
      hKTExact hKTRelative hFExactThird hFRelativeThird
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

#print axioms SelectedTrueSplitEtaDatumDSOAt
#print axioms SelectedTrueSplitEtaHDatumDSO
#print axioms mainLemmaOne_of_selectedTrueSplitEtaHDatumDSOProvider

end
end Family8AllGammaSelectedTrueSplitEtaLongGeometryCommonV2
