import Family8Grounding.Family8EndpointIdentityFullRefinementMainLemmaOrchestrationV1
import Family8Grounding.Family8EndpointIdentityParameterLadderProducerV2

/-!
# Main Lemma 1 with the canonical endpoint parameter ladder, V2

The endpoint-identity parameter ladder was already constructed from the
strict exponent gap.  This module consumes that construction in the literal
full-refinement orchestration, so the remaining geometric producer is stated
for one fixed `epsilon0/P` rather than being asked to manufacture an
existential ladder itself.

V1 omitted the relative-scale namespace from its public signature and is not
imported.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8EndpointIdentityCanonicalParameterFullRefinementMainLemmaOrchestrationV2

open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointIdentityFullRefinementMainLemmaOrchestrationV1
open Family8EndpointIdentityParameterLadderProducerV2
open Family8FullRefinementActualDatumV1
open Family8GeneralizedScaleTrivialBranchV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

/-- Main Lemma 1 from a geometric producer on the already fixed canonical
endpoint ladder. -/
theorem mainLemmaOne_of_canonicalParameter_endpointIdentity_fullRefinement_branches
    (hGeometry : forall (beta gamma : Real)
      (hBeta : 0 < beta) (hGap : beta < gamma) (_hGamma : gamma ≤ 1),
      let P := endpointIdentityParameterLadder hBeta hGap
      forall targetEpsilon : Real, 0 < targetEpsilon ->
      forall eta : Real, forall delta0 : NNReal,
        0 < eta -> 0 < delta0 -> delta0 ≤ (2 : NNReal)⁻¹ ->
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
                delta ≤ rawDelta0 ->
                FrostmanHypotheses D eta ->
                D.shading.shadingMass ≠ 0 ->
                  (forall _W : NormalizedLongIntervalCoreWitness
                    (fullRefinementDatum D).family
                      (identityRadiusCoherentCover
                        (fullRefinementDatum D).family)
                      P.N P.epsilon P.eta
                        (endpointScaleSequence delta
                          (hD.delta_le_half.trans (by norm_num))),
                      DividingScaleOutput D P targetEpsilon) /\
                  (forall _W : FirstActualNormalizedCrossingWitness
                    (fullRefinementDatum D)
                      (fullRefinementDatum_isAdmissible hD)
                      (identityRadiusCoherentCover
                        (fullRefinementDatum D).family)
                      (endpointScaleSequence delta
                        (hD.delta_le_half.trans (by norm_num)))
                      P.epsilon P.epsilon_pos.le P.eta P.N,
                      DividingScaleOutput D P targetEpsilon))
    (beta : Real) :
    KatzTaoProperty beta -> FrostmanProperty beta := by
  apply mainLemmaOne_of_endpointIdentity_fullRefinement_branches
  intro target source hTargetPos hTargetSource hSourceOne
  let P := endpointIdentityParameterLadder hTargetPos hTargetSource
  refine ⟨endpointIdentityEpsilon0 target source, P, ?_⟩
  simpa only [P] using
    hGeometry target source hTargetPos hTargetSource hSourceOne

#print axioms
  mainLemmaOne_of_canonicalParameter_endpointIdentity_fullRefinement_branches

end
end Family8EndpointIdentityCanonicalParameterFullRefinementMainLemmaOrchestrationV2
