import Family8Grounding.Family8AllFrostmanFixedNuBranchOrchestrationV2
import Family8Grounding.Family8EndpointIdentityFullRefinementDividingScaleOutputOrchestrationV1
import Family8Grounding.Family8EndpointIdentityParameterLadderProducerV2
import Family8Grounding.Family8FullRefinementThreeScaleLiteralDSODataV2
import Family8Grounding.Family8SectionEightOutputEtaV1

/-!
# Main Lemma 1 from literal three-scale data retaining the output eta, V2

V1 is a failed syntax draft and is not imported.  The older canonical data
interface transported the stronger hypotheses at `min sourceEta fixedNu` to
`sourceEta` before calling the geometric producer.  This successor passes
the canonical output exponent to the datum producer while retaining all four
source-parameter estimates for calls to the assumed properties.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8CanonicalParameterFullRefinementOutputEtaThreeScaleDataMainLemmaOrchestrationV2

open Family8AllFrostmanFixedNuBranchOrchestrationV2
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointIdentityFullRefinementDividingScaleOutputOrchestrationV1
open Family8EndpointIdentityParameterLadderProducerV2
open Family8FullRefinementActualDatumV1
open Family8FullRefinementThreeScaleLiteralDSODataV2
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

/-- Main Lemma 1 from same-object three-scale producers which retain the
canonical small output hypothesis exponent. -/
theorem mainLemmaOne_of_canonicalParameter_outputEta_literalThreeScaleData
    (hGeometry : forall (beta gamma : Real)
      (hBeta : 0 < beta) (hGap : beta < gamma) (hGamma : gamma ≤ 1),
      let P := endpointIdentityParameterLadder hBeta hGap
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
  apply mainLemmaOne_of_allFrostman_or_outerThree_middleTen
  intro target source hTargetPos hTargetSource hSourceOne
  let P := endpointIdentityParameterLadder hTargetPos hTargetSource
  refine Exists.intro (endpointIdentityEpsilon0 target source) ?_
  refine Exists.intro P ?_
  intro targetEpsilon hTargetEpsilon sourceEta delta0
    hSourceEta hDelta0 hDelta0Half hKTExact hFExact
      hKTRelative hFRelative
  obtain ⟨rawDelta0, hRawDelta0, hDatum⟩ :=
    hGeometry target source hTargetPos hTargetSource hSourceOne
      targetEpsilon hTargetEpsilon sourceEta delta0
      hSourceEta hDelta0 hDelta0Half hKTExact hFExact
        hKTRelative hFRelative
  refine Exists.intro (sectionEightOutputEta P sourceEta) ?_
  refine Exists.intro rawDelta0 ?_
  refine ⟨sectionEightOutputEta_pos P hSourceEta,
    sectionEightOutputEta_le_fixedNu P sourceEta,
    hRawDelta0, ?_⟩
  intro delta index _ _ D hD hdelta hFOutput hmass
  obtain ⟨hLongData, hFirstData⟩ :=
    hDatum delta index D hD hdelta hFOutput hmass
  have hLong : forall W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
        (identityRadiusCoherentCover (fullRefinementDatum D).family)
        P.N P.epsilon P.eta
          (endpointScaleSequence delta
            (hD.delta_le_half.trans (by norm_num))),
      DividingScaleOutput D P targetEpsilon := by
    intro W
    exact Nonempty.elim (hLongData W) fun X =>
      X.toDividingScaleOutput hTargetEpsilon hSourceOne
  have hFirst : forall W : FirstActualNormalizedCrossingWitness
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
        (identityRadiusCoherentCover (fullRefinementDatum D).family)
        (endpointScaleSequence delta
          (hD.delta_le_half.trans (by norm_num)))
        P.epsilon P.epsilon_pos.le P.eta P.N,
      DividingScaleOutput D P targetEpsilon := by
    intro W
    exact Nonempty.elim (hFirstData W) fun X =>
      X.toDividingScaleOutput hTargetEpsilon hSourceOne
  have hOutput : DividingScaleOutput D P targetEpsilon :=
    dividingScaleOutput_of_endpointIdentity_fullRefinement_branches
      D hD P hTargetPos hSourceOne hLong hFirst
  simpa only [DividingScaleOutput] using hOutput

#print axioms
  mainLemmaOne_of_canonicalParameter_outputEta_literalThreeScaleData

end
end Family8CanonicalParameterFullRefinementOutputEtaThreeScaleDataMainLemmaOrchestrationV2
