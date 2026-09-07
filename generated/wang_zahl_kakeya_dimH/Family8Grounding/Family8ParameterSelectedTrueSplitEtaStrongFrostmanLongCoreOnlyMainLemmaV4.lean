import Family8Grounding.Family8ParameterSelectedTrueSplitEtaStrongFrostmanLongCoreOnlyMainLemmaV3
import Mathlib.Tactic

/-!
# Datum-level selected split-eta top connector

The V3 top checkpoint quantified over a normalized LongCore witness even
though the high-gamma provider chooses its canonical witness internally.
This successor removes that unused callback parameter.  It changes no
exponent, threshold, datum, or geometric object.
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal NNReal

namespace Family8ParameterSelectedTrueSplitEtaStrongFrostmanLongCoreOnlyMainLemmaV4

open Submission.Kakeya.ConvexGeometry
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8FullRefinementActualDatumV1
open Family8GeneralizedScaleTrivialBranchV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParameterLadderV1
open Family8ParameterSelectedTrueSplitEtaStrongFrostmanLongCoreOnlyMainLemmaV3
open Family8RelativeScaleFixedNuEndpointOrchestrationV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3

noncomputable section

/-- Main Lemma 1 from a datum-level DSO provider.  The provider receives no
external witness; an automatic high-gamma implementation may construct its
single canonical witness internally. -/
theorem mainLemmaOne_of_parameter_selectedTrueSplitEta_strongFrostman_datumDSO
    (hLongGeometry : forall (beta gamma : Real)
      (_hBeta : 0 < beta) (_hGap : beta < gamma) (_hGamma : gamma <= 1),
      exists epsilon0 : Real,
      exists P : ParameterLadder epsilon0 beta gamma,
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
              (D : ActualTubeDatum delta index)
              (_hD : D.IsAdmissible),
                delta <= rawDelta0 ->
                FrostmanHypotheses D
                  (selectedTrueSplitOutputEta P thirdEta) ->
                DividingScaleOutput D P
                  (4 * sectionEightSourceLoss P targetEpsilon))
    (beta : Real) :
    KatzTaoProperty beta -> FrostmanProperty beta := by
  apply
    mainLemmaOne_of_parameter_selectedTrueSplitEta_strongFrostman_longCoreOnlyDSO
  intro beta' gamma hBeta hGap hGamma
  obtain ⟨epsilon0, P, hDatum⟩ :=
    hLongGeometry beta' gamma hBeta hGap hGamma
  refine ⟨epsilon0, P, ?_⟩
  intro targetEpsilon hTarget etaKT thirdEta delta0
    hEtaKT hEtaKTCap hThirdEta hThirdCap hDelta0 hDelta0Half
    hKT hKTRelative hFExact hFRelative
  obtain ⟨rawDelta0, hRawPos, hRun⟩ :=
    hDatum targetEpsilon hTarget etaKT thirdEta delta0
      hEtaKT hEtaKTCap hThirdEta hThirdCap hDelta0 hDelta0Half
      hKT hKTRelative hFExact hFRelative
  refine ⟨rawDelta0, hRawPos, ?_⟩
  intro delta index _ _ D hD hDelta hFOutput _W
  exact hRun delta index D hD hDelta hFOutput

#print axioms
  mainLemmaOne_of_parameter_selectedTrueSplitEta_strongFrostman_datumDSO

end
end Family8ParameterSelectedTrueSplitEtaStrongFrostmanLongCoreOnlyMainLemmaV4
