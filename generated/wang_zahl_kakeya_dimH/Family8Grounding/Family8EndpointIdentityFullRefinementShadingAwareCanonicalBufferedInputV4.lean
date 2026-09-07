import Family8Grounding.Family8EndpointFullRefinementShadingAwareCanonicalBufferedInputV4
import Family8Grounding.Family8IdentityCoherentCoreSelectorV1
import FamilyStickyGrounding.FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
import Mathlib.Tactic

/-!
# Identity-cover specialization of the endpoint shading-aware input, V4

This thin specialization packages the exact coherent cover and endpoint
sequence used by the final Main Lemma orchestration.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8EndpointIdentityFullRefinementShadingAwareCanonicalBufferedInputV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8EndpointFullRefinementShadingAwareCanonicalBufferedInputV3
open Family8EndpointLongCoreHalfRadiusThresholdV2
open Family8FullRefinementActualDatumV1
open Family8IdentityCoherentCoreSelectorV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma etaF : Real}

/-- Produce the callback-free side-condition package at exactly the identity
cover and endpoint sequence used by Main Lemma 1. -/
theorem endpointIdentityFullRefinementShadingAwareBufferedInputData
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma ≤ 1)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
        (identityRadiusCoherentCover (fullRefinementDatum D).family)
        P.N P.epsilon P.eta
        (endpointScaleSequence delta
          (hD.delta_le_half.trans (by norm_num))))
    (hF : FrostmanHypotheses D etaF)
    (hsmall : delta ≤ endpointLongCoreHalfRadiusThreshold P) :
    EndpointFullRefinementShadingAwareBufferedInputData
      D hD P
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      (hD.delta_le_half.trans (by norm_num)) W :=
  endpointFullRefinementShadingAwareBufferedInputData
    D hD P hbeta hgamma
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      (hD.delta_le_half.trans (by norm_num)) W hF hsmall

/-- Construct the literal identity-cover canonical buffered input from the
specialized stable package and an arbitrary positive paper source constant. -/
noncomputable def identityEndpointCanonicalBufferedInput
    {D : ActualTubeDatum delta index} {hD : D.IsAdmissible}
    {P : ParameterLadder epsilon0 beta gamma}
    {W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
        (identityRadiusCoherentCover (fullRefinementDatum D).family)
        P.N P.epsilon P.eta
        (endpointScaleSequence delta
          (hD.delta_le_half.trans (by norm_num)))}
    (X : EndpointFullRefinementShadingAwareBufferedInputData
      D hD P
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      (hD.delta_le_half.trans (by norm_num)) W)
    (sourceA : NNReal) (hsourceA : 0 < sourceA) :=
  Family8EndpointFullRefinementShadingAwareCanonicalBufferedInputV4.EndpointFullRefinementShadingAwareBufferedInputData.toCanonicalBufferedInput X sourceA hsourceA

#print axioms endpointIdentityFullRefinementShadingAwareBufferedInputData
#print axioms identityEndpointCanonicalBufferedInput

end

end Family8EndpointIdentityFullRefinementShadingAwareCanonicalBufferedInputV4
