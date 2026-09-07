import Family8Grounding.Family8ParameterSelectedTrueSplitEtaStrongFrostmanLongCoreOnlyMainLemmaV3

/-!
# Common selected-output LongGeometry interface for the all-gamma merge

This module names the literal callback consumed by the selected true-split
top orchestration.  It chooses no parameter ladder, exponent, endpoint
witness, cover, or assembly.  Those choices remain branch-local in the
all-gamma case split.
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal NNReal

namespace Family8AllGammaSelectedTrueSplitEtaLongGeometryCommonV1

open Submission.Kakeya.ConvexGeometry
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8FullRefinementActualDatumV1
open Family8GeneralizedScaleTrivialBranchV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8ParameterSelectedTrueSplitEtaStrongFrostmanLongCoreOnlyMainLemmaV3
open Family8RelativeScaleFixedNuEndpointOrchestrationV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

/-- The weakest common selected-output callback for one already chosen
branch-local parameter ladder.  The datum Frostman exponent is the literal
selected exponent fixed by the top wrapper. -/
def SelectedTrueSplitEtaLongGeometryAt
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
          (D : ActualTubeDatum delta index) (hD : D.IsAdmissible),
            delta <= rawDelta0 ->
            FrostmanHypotheses D
              (selectedTrueSplitOutputEta P thirdEta) ->
              forall _W : NormalizedLongIntervalCoreWitness
                (fullRefinementDatum D).family
                  (identityRadiusCoherentCover
                    (fullRefinementDatum D).family)
                  P.N P.epsilon P.eta
                    (endpointScaleSequence delta
                      (hD.delta_le_half.trans (by norm_num))),
                DividingScaleOutput D P
                  (4 * sectionEightSourceLoss P targetEpsilon)

/-- Existential branch-local ladder form used after the gamma split. -/
abbrev SelectedTrueSplitEtaHLongGeometry (beta gamma : Real) : Prop :=
  exists epsilon0 : Real,
  exists P : ParameterLadder epsilon0 beta gamma,
    SelectedTrueSplitEtaLongGeometryAt P

/-- Feed an all-parameter provider of the exact common interface into the
selected top orchestration. -/
theorem mainLemmaOne_of_selectedTrueSplitEtaHLongGeometryProvider
    (hProvider : forall (beta gamma : Real)
      (_hbeta : 0 < beta) (_hgap : beta < gamma) (_hgamma : gamma <= 1),
        SelectedTrueSplitEtaHLongGeometry beta gamma)
    (beta : Real) :
    KatzTaoProperty beta -> FrostmanProperty beta := by
  apply
    mainLemmaOne_of_parameter_selectedTrueSplitEta_strongFrostman_longCoreOnlyDSO
  intro target source hTarget hGap hSource
  simpa only [SelectedTrueSplitEtaHLongGeometry,
    SelectedTrueSplitEtaLongGeometryAt] using
      (hProvider target source hTarget hGap hSource)

#print axioms SelectedTrueSplitEtaLongGeometryAt
#print axioms SelectedTrueSplitEtaHLongGeometry
#print axioms mainLemmaOne_of_selectedTrueSplitEtaHLongGeometryProvider

end
end Family8AllGammaSelectedTrueSplitEtaLongGeometryCommonV1
