import Family8Grounding.Family8EndpointIdentityCanonicalParameterFullRefinementMainLemmaOrchestrationV2
import Family8Grounding.Family8FullRefinementThreeScaleLiteralDSODataV2

/-!
# Main Lemma 1 from literal three-scale data on the canonical endpoint ladder, V2

This is the final lossless interface before the two geometric producers.  A
producer supplies a nonempty stable numerical-data record for each literal
long-core or first-crossing witness.  V1 incorrectly placed Type-valued
records directly under propositional conjunction and is not imported.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8CanonicalParameterFullRefinementThreeScaleDataMainLemmaOrchestrationV2

open Family8EndpointIdentityCanonicalParameterFullRefinementMainLemmaOrchestrationV2
open Family8EndpointIdentityParameterLadderProducerV2
open Family8FullRefinementActualDatumV1
open Family8FullRefinementThreeScaleLiteralDSODataV2
open Family8GeneralizedScaleTrivialBranchV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

/-- Main Lemma 1 from same-object three-scale data producers on the fixed
canonical endpoint parameter ladder. -/
theorem mainLemmaOne_of_canonicalParameter_literalThreeScaleData
    (hGeometry : forall (beta gamma : Real)
      (hBeta : 0 < beta) (hGap : beta < gamma) (hGamma : gamma ≤ 1),
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
                  (forall W : NormalizedLongIntervalCoreWitness
                    (fullRefinementDatum D).family
                      (identityRadiusCoherentCover
                        (fullRefinementDatum D).family)
                      P.N P.epsilon P.eta
                        (endpointScaleSequence delta
                          (hD.delta_le_half.trans (by norm_num))),
                    Nonempty (LongCoreThreeScaleDSOData D hD
                      (identityRadiusCoherentCover
                        (fullRefinementDatum D).family)
                      (endpointScaleSequence delta
                        (hD.delta_le_half.trans (by norm_num)))
                      P W targetEpsilon)) /\
                  (forall W : FirstActualNormalizedCrossingWitness
                    (fullRefinementDatum D)
                      (fullRefinementDatum_isAdmissible hD)
                      (identityRadiusCoherentCover
                        (fullRefinementDatum D).family)
                      (endpointScaleSequence delta
                        (hD.delta_le_half.trans (by norm_num)))
                      P.epsilon P.epsilon_pos.le P.eta P.N,
                    Nonempty (FirstCrossingThreeScaleDSOData D hD
                      (identityRadiusCoherentCover
                        (fullRefinementDatum D).family)
                      (endpointScaleSequence delta
                        (hD.delta_le_half.trans (by norm_num)))
                      P W targetEpsilon)))
    (beta : Real) :
    KatzTaoProperty beta -> FrostmanProperty beta := by
  apply
    mainLemmaOne_of_canonicalParameter_endpointIdentity_fullRefinement_branches
  intro target source hTargetPos hTargetSource hSourceOne
  dsimp only
  intro targetEpsilon hTargetEpsilon eta delta0
    hEta hDelta0 hDelta0Half hKTExact hFExact hKTRelative hFRelative
  obtain ⟨rawDelta0, hRawDelta0, hDatum⟩ :=
    hGeometry target source hTargetPos hTargetSource hSourceOne
      targetEpsilon hTargetEpsilon eta delta0
      hEta hDelta0 hDelta0Half hKTExact hFExact hKTRelative hFRelative
  refine ⟨rawDelta0, hRawDelta0, ?_⟩
  intro delta index _ _ D hD hdelta hF hmass
  obtain ⟨hLongData, hFirstData⟩ :=
    hDatum delta index D hD hdelta hF hmass
  constructor
  · intro W
    exact Nonempty.elim (hLongData W) fun X =>
      X.toDividingScaleOutput hTargetEpsilon hSourceOne
  · intro W
    exact Nonempty.elim (hFirstData W) fun X =>
      X.toDividingScaleOutput hTargetEpsilon hSourceOne

#print axioms mainLemmaOne_of_canonicalParameter_literalThreeScaleData

end
end Family8CanonicalParameterFullRefinementThreeScaleDataMainLemmaOrchestrationV2
