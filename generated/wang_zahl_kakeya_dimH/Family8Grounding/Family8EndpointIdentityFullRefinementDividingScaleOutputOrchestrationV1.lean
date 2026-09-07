import Family8Grounding.Family8EndpointIdentityFullRefinementCoreSelectorV1
import Family8Grounding.Family8EndpointIdentityDividingScaleOutputOrchestrationV4

/-!
# Full-refinement two-branch handoff to the dividing-scale output

The quantitative output remains a proposition about the original actual
datum.  Only the stopping witnesses are selected on its definitionally
equivalent full-refinement copy, matching the frozen-assembly and
source-to-tau pipelines without any transport callback.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8EndpointIdentityFullRefinementDividingScaleOutputOrchestrationV1

open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointIdentityFullRefinementCoreSelectorV1
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

/-- Literal DSO handoff from the endpoint selector on the source's full
refinement. -/
theorem dividingScaleOutput_of_endpointIdentity_fullRefinement_branches
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    {epsilon0 beta gamma targetEpsilon : Real}
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hLong : forall _W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
        (identityRadiusCoherentCover (fullRefinementDatum D).family)
        P.N P.epsilon P.eta
          (endpointScaleSequence delta
            (hD.delta_le_half.trans (by norm_num))),
        DividingScaleOutput D P targetEpsilon)
    (hFirst : forall _W : FirstActualNormalizedCrossingWitness
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
        (identityRadiusCoherentCover (fullRefinementDatum D).family)
        (endpointScaleSequence delta
          (hD.delta_le_half.trans (by norm_num)))
        P.epsilon P.epsilon_pos.le P.eta P.N,
        DividingScaleOutput D P targetEpsilon) :
    DividingScaleOutput D P targetEpsilon := by
  rcases endpointIdentity_fullRefinement_longCore_or_firstCrossing
      D hD P hbeta hgamma with hlong | hfirst
  · exact Nonempty.elim hlong hLong
  · exact Nonempty.elim hfirst hFirst

#print axioms
  dividingScaleOutput_of_endpointIdentity_fullRefinement_branches

end
end Family8EndpointIdentityFullRefinementDividingScaleOutputOrchestrationV1
