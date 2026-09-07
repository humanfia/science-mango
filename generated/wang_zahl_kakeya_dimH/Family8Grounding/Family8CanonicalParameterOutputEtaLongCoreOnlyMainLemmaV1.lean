import Family8Grounding.Family8CanonicalParameterFullRefinementOutputEtaDirectDSOMainLemmaOrchestrationV2
import Family8Grounding.Family8EndpointIdentityFirstCrossingImpossibleV1

/-!
# Canonical output-eta main-lemma orchestration from LongCore only

At the endpoint identity cover, sufficiently small nonzero-mass data cannot
produce a `FirstCrossing` witness.  Consequently a main-lemma geometry
producer should only have to discharge the `LongCore` branch.  This module
shrinks the existing two-callback orchestration to that single honest
mathematical input by taking the minimum with the explicit FirstCrossing
impossibility threshold.

No LongCore estimate is manufactured here: the remaining callback still has
to return the genuine `DividingScaleOutput` for every selected LongCore
witness.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8CanonicalParameterOutputEtaLongCoreOnlyMainLemmaV1

open Family8CanonicalParameterFullRefinementOutputEtaDirectDSOMainLemmaOrchestrationV2
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointIdentityFirstCrossingImpossibleV1
open Family8EndpointIdentityParameterLadderProducerV2
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

/-- Main Lemma 1 from a LongCore-only direct DSO producer.  The endpoint
FirstCrossing callback required by the older orchestration is discharged by
the already-proved impossibility theorem. -/
theorem mainLemmaOne_of_canonicalParameter_outputEta_longCoreOnlyDSO
    (hLongGeometry : forall (beta gamma : Real)
      (hBeta : 0 < beta) (hGap : beta < gamma) (hGamma : gamma <= 1),
      let P := endpointIdentityParameterLadder hBeta hGap
      forall targetEpsilon : Real, 0 < targetEpsilon ->
      forall sourceEta : Real, forall delta0 : NNReal,
        0 < sourceEta -> 0 < delta0 -> delta0 <= (2 : NNReal)⁻¹ ->
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
                delta <= rawDelta0 ->
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
  apply mainLemmaOne_of_canonicalParameter_outputEta_directDSO
  intro target source hTargetPos hTargetSource hSourceOne
  dsimp only
  let P := endpointIdentityParameterLadder hTargetPos hTargetSource
  intro targetEpsilon hTargetEpsilon sourceEta delta0
    hSourceEta hDelta0 hDelta0Half hKTExact hFExact
      hKTRelative hFRelative
  obtain ⟨rawDelta0, hRawDelta0, hLong⟩ :=
    hLongGeometry target source hTargetPos hTargetSource hSourceOne
      targetEpsilon hTargetEpsilon sourceEta delta0
      hSourceEta hDelta0 hDelta0Half hKTExact hFExact
        hKTRelative hFRelative
  refine ⟨min rawDelta0
      (endpointIdentityFirstCrossingImpossibleThreshold P), ?_, ?_⟩
  · exact lt_min hRawDelta0
      (endpointIdentityFirstCrossingImpossibleThreshold_pos P)
  · intro delta index _ _ D hD hdelta hFOutput hmass
    have hdeltaRaw : delta <= rawDelta0 :=
      hdelta.trans (min_le_left _ _)
    have hdeltaFirst : delta <=
        endpointIdentityFirstCrossingImpossibleThreshold P :=
      hdelta.trans (min_le_right _ _)
    refine ⟨hLong delta index D hD hdeltaRaw hFOutput hmass, ?_⟩
    intro W
    exact False.elim
      ((endpointIdentity_fullRefinement_not_firstCrossing
        D hD P hTargetPos hSourceOne hmass hdeltaFirst) ⟨W⟩)

#print axioms
  mainLemmaOne_of_canonicalParameter_outputEta_longCoreOnlyDSO

end
end Family8CanonicalParameterOutputEtaLongCoreOnlyMainLemmaV1
