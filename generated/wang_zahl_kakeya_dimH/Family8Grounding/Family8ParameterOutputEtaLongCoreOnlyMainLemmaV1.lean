import Family8Grounding.Family8AllFrostmanFixedNuBranchOrchestrationV2
import Family8Grounding.Family8EndpointIdentityFirstCrossingImpossibleV1
import Family8Grounding.Family8EndpointIdentityFullRefinementDividingScaleOutputOrchestrationV1
import Family8Grounding.Family8SectionEightOutputEtaV1

/-!
# Arbitrary-parameter output-eta main-lemma orchestration from LongCore only

The parameter ladder is supplied existentially by the geometric endpoint;
it is not identified with the canonical endpoint ladder.  For that same
ladder, the raw terminal scale is intersected with the explicit endpoint
FirstCrossing-impossibility threshold.  Thus the only geometric callback
left at the actual-datum boundary is the canonical endpoint-identity
LongCore witness.

This file does not manufacture the LongCore estimate and does not connect a
specialized high-gamma ladder to the general endpoint.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8ParameterOutputEtaLongCoreOnlyMainLemmaV1

open Family8AllFrostmanFixedNuBranchOrchestrationV2
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointIdentityFirstCrossingImpossibleV1
open Family8EndpointIdentityFullRefinementDividingScaleOutputOrchestrationV1
open Family8FullRefinementActualDatumV1
open Family8GeneralizedScaleTrivialBranchV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open Family8SectionEightOutputEtaV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

/-- Main Lemma 1 from a LongCore-only direct DSO producer on an arbitrary
existentially supplied parameter ladder.  The FirstCrossing callback is
discharged on the same ladder by the endpoint impossibility theorem. -/
theorem mainLemmaOne_of_parameter_outputEta_longCoreOnlyDSO
    (hLongGeometry : forall (beta gamma : Real)
      (hBeta : 0 < beta) (hGap : beta < gamma) (hGamma : gamma ≤ 1),
      exists epsilon0 : Real,
      exists P : ParameterLadder epsilon0 beta gamma,
      forall targetEpsilon : Real, 0 < targetEpsilon ->
      forall sourceEta : Real, forall delta0 : NNReal,
        0 < sourceEta -> 0 < delta0 -> delta0 ≤ (2 : NNReal)⁻¹ ->
        KatzTaoAtParameters
          beta (sectionEightFixedNu P) sourceEta delta0 ->
        FrostmanAtParameters gamma (targetEpsilon / 4) sourceEta delta0 ->
        KatzTaoAtRelativeScaleParameters
          beta (sectionEightFixedNu P) sourceEta delta0 ->
        FrostmanAtRelativeScaleParameters
          gamma (targetEpsilon / 4) sourceEta delta0 ->
          exists rawDelta0 : NNReal, 0 < rawDelta0 /\
            forall (delta : NNReal) (index : Type)
              [Fintype index] [DecidableEq index]
              (D : ActualTubeDatum delta index)
              (hD : D.IsAdmissible),
                delta ≤ rawDelta0 ->
                FrostmanHypotheses D
                  (sectionEightOutputEta P sourceEta) ->
                D.shading.shadingMass ≠ 0 ->
                  forall _W : NormalizedLongIntervalCoreWitness
                    (fullRefinementDatum D).family
                      (identityRadiusCoherentCover
                        (fullRefinementDatum D).family)
                      P.N P.epsilon P.eta
                        (endpointScaleSequence delta
                          (hD.delta_le_half.trans (by norm_num))),
                    DividingScaleOutput D P targetEpsilon)
    (beta : Real) :
    KatzTaoProperty beta -> FrostmanProperty beta := by
  apply mainLemmaOne_of_allFrostman_or_outerThree_middleTen
  intro target source hTargetPos hTargetSource hSourceOne
  obtain ⟨epsilon0, P, hEndpoint⟩ :=
    hLongGeometry target source hTargetPos hTargetSource hSourceOne
  refine ⟨epsilon0, P, ?_⟩
  intro targetEpsilon hTargetEpsilon sourceEta delta0
    hSourceEta hDelta0 hDelta0Half hKTExact hFExact
      hKTRelative hFRelative
  obtain ⟨rawDelta0, hRawDelta0, hLongDatum⟩ :=
    hEndpoint targetEpsilon hTargetEpsilon sourceEta delta0
      hSourceEta hDelta0 hDelta0Half hKTExact hFExact
        hKTRelative hFRelative
  let finalRawDelta0 : NNReal :=
    min rawDelta0 (endpointIdentityFirstCrossingImpossibleThreshold P)
  have hFinalRawDelta0 : 0 < finalRawDelta0 := by
    dsimp only [finalRawDelta0]
    exact lt_min hRawDelta0
      (endpointIdentityFirstCrossingImpossibleThreshold_pos P)
  refine ⟨sectionEightOutputEta P sourceEta, finalRawDelta0,
    sectionEightOutputEta_pos P hSourceEta,
    sectionEightOutputEta_le_fixedNu P sourceEta,
    hFinalRawDelta0, ?_⟩
  intro delta index _ _ D hD hdelta hFOutput hmass
  have hdeltaRaw : delta ≤ rawDelta0 :=
    hdelta.trans (min_le_left _ _)
  have hdeltaFirst : delta ≤
      endpointIdentityFirstCrossingImpossibleThreshold P :=
    hdelta.trans (min_le_right _ _)
  have hLong :=
    hLongDatum delta index D hD hdeltaRaw hFOutput hmass
  have hFirst : forall _W : FirstActualNormalizedCrossingWitness
      (fullRefinementDatum D)
        (fullRefinementDatum_isAdmissible hD)
        (identityRadiusCoherentCover (fullRefinementDatum D).family)
        (endpointScaleSequence delta
          (hD.delta_le_half.trans (by norm_num)))
        P.epsilon P.epsilon_pos.le P.eta P.N,
      DividingScaleOutput D P targetEpsilon := by
    intro W
    exact False.elim
      ((endpointIdentity_fullRefinement_not_firstCrossing
        D hD P hTargetPos hSourceOne hmass hdeltaFirst) ⟨W⟩)
  have hOutput : DividingScaleOutput D P targetEpsilon :=
    dividingScaleOutput_of_endpointIdentity_fullRefinement_branches
      D hD P hTargetPos hSourceOne hLong hFirst
  simpa only [DividingScaleOutput] using hOutput

#print axioms
  mainLemmaOne_of_parameter_outputEta_longCoreOnlyDSO

end
end Family8ParameterOutputEtaLongCoreOnlyMainLemmaV1
