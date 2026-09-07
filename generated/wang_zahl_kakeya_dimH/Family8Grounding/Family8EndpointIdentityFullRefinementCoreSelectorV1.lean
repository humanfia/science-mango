import Family8Grounding.Family8EndpointIdentityCoreSelectorV2
import Family8Grounding.Family8FullRefinementActualDatumV1

/-!
# Endpoint identity selector on the literal full refinement

The later frozen-assembly analysis must retain every source tube.  Since the
full-refinement datum changes only refinement metadata, the endpoint
one-step stopping selector applies to it with the same scale sequence and
returns either a normalized long core or a first actual crossing on exactly
the object consumed by those downstream producers.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open scoped ENNReal NNReal

namespace Family8EndpointIdentityFullRefinementCoreSelectorV1

open Family8EndpointIdentityCoreSelectorV2
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

/-- The endpoint selector run on the full refinement, with the source datum
left unchanged in every quantitative field. -/
theorem endpointIdentity_fullRefinement_longCore_or_firstCrossing
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    {epsilon0 beta gamma : Real}
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1) :
    let E := fullRefinementDatum D
    let hE := fullRefinementDatum_isAdmissible hD
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    Nonempty (NormalizedLongIntervalCoreWitness
        E.family (identityRadiusCoherentCover E.family)
          P.N P.epsilon P.eta S) ∨
      Nonempty (FirstActualNormalizedCrossingWitness
        E hE (identityRadiusCoherentCover E.family) S
          P.epsilon P.epsilon_pos.le P.eta P.N) := by
  dsimp only
  exact endpointIdentity_longCore_or_firstCrossing
    (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
      P hbeta hgamma

#print axioms endpointIdentity_fullRefinement_longCore_or_firstCrossing

end
end Family8EndpointIdentityFullRefinementCoreSelectorV1
