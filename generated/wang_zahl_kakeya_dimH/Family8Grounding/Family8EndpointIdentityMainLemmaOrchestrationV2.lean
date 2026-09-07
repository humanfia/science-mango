import Family8Grounding.Family8EndpointIdentityDividingScaleOutputOrchestrationV4
import Family8Grounding.Family8SectionEightOutputEtaV1
import Family8Grounding.Family8AllFrostmanFixedNuBranchOrchestrationV2

/-!
# Main Lemma 1 from the two concrete endpoint-identity branches

This is the final quantifier-level handoff for the current proof path.  It
chooses the canonical output hypothesis exponent, transports it back to the
source exponent, invokes the concrete endpoint identity selector, and feeds
its long-core/first-crossing output to the already proved fixed-nu
orchestration.  The only remaining theorem input consists of the two honest
geometric branch producers on their literal selected witnesses.

V1 was a dependent-binder draft and is not imported.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8EndpointIdentityMainLemmaOrchestrationV2

open Submission.Kakeya.ConvexGeometry
open Family8AllFrostmanFixedNuBranchOrchestrationV2
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
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

/-- Main Lemma 1 follows once the two actual endpoint-sequence branches
produce the literal dividing-scale output.  Parameter extraction, output
loss selection, all-large elimination, zero mass, the union alternative,
fixed-nu absorption, self-improvement iteration, and all-real boundary
closure are internal to this theorem and its imported orchestration stack. -/
theorem mainLemmaOne_of_endpointIdentity_longCore_firstCrossing
    (hGeometry : forall beta gamma : Real,
      0 < beta -> beta < gamma -> gamma <= 1 ->
        exists epsilon0 : Real, exists P : ParameterLadder epsilon0 beta gamma,
          forall targetEpsilon : Real, 0 < targetEpsilon ->
          forall eta : Real, forall delta0 : NNReal,
            0 < eta -> 0 < delta0 -> delta0 <= (2 : NNReal)⁻¹ ->
            KatzTaoAtParameters
              beta (sectionEightFixedNu P) eta delta0 ->
            FrostmanAtParameters gamma (targetEpsilon / 4) eta delta0 ->
            KatzTaoAtRelativeScaleParameters
              beta (sectionEightFixedNu P) eta delta0 ->
            FrostmanAtRelativeScaleParameters
              gamma (targetEpsilon / 4) eta delta0 ->
              exists rawDelta0 : NNReal, 0 < rawDelta0 /\
                forall (delta : NNReal) (index : Type)
                  [Fintype index] [DecidableEq index]
                  (D : ActualTubeDatum delta index)
                  (hD : D.IsAdmissible),
                    delta <= rawDelta0 ->
                    FrostmanHypotheses D eta ->
                    D.shading.shadingMass ≠ 0 ->
                      (forall _W : NormalizedLongIntervalCoreWitness
                        D.family (identityRadiusCoherentCover D.family)
                          P.N P.epsilon P.eta
                            (endpointScaleSequence delta
                              (hD.delta_le_half.trans (by norm_num))),
                          DividingScaleOutput D P targetEpsilon) /\
                      (forall _W : FirstActualNormalizedCrossingWitness
                        D hD (identityRadiusCoherentCover D.family)
                          (endpointScaleSequence delta
                            (hD.delta_le_half.trans (by norm_num)))
                          P.epsilon P.epsilon_pos.le P.eta P.N,
                          DividingScaleOutput D P targetEpsilon))
    (beta : Real) :
    KatzTaoProperty beta -> FrostmanProperty beta := by
  apply mainLemmaOne_of_allFrostman_or_outerThree_middleTen
  intro target source hTargetPos hTargetSource hSourceOne
  obtain ⟨epsilon0, P, hEndpoint⟩ :=
    hGeometry target source hTargetPos hTargetSource hSourceOne
  refine ⟨epsilon0, P, ?_⟩
  intro targetEpsilon hTargetEpsilon eta delta0
    hEta hDelta0 hDelta0Half hKTExact hFExact hKTRelative hFRelative
  obtain ⟨rawDelta0, hRawDelta0, hDatum⟩ :=
    hEndpoint targetEpsilon hTargetEpsilon eta delta0
      hEta hDelta0 hDelta0Half hKTExact hFExact hKTRelative hFRelative
  refine ⟨sectionEightOutputEta P eta, rawDelta0,
    sectionEightOutputEta_pos P hEta,
    sectionEightOutputEta_le_fixedNu P eta,
    hRawDelta0, ?_⟩
  intro delta index _ _ D hD hdelta hFOutput hmass
  have hFSource : FrostmanHypotheses D eta :=
    sourceFrostmanHypotheses_of_sectionEightOutputEta D hD P hFOutput
  obtain ⟨hLong, hFirst⟩ :=
    hDatum delta index D hD hdelta hFSource hmass
  have hOutput : DividingScaleOutput D P targetEpsilon :=
    dividingScaleOutput_of_endpointIdentity_branches
      D hD P hTargetPos hSourceOne hLong hFirst
  simpa only [DividingScaleOutput] using hOutput

#print axioms mainLemmaOne_of_endpointIdentity_longCore_firstCrossing

end
end Family8EndpointIdentityMainLemmaOrchestrationV2
