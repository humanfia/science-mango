import Family8Grounding.Family8EndpointLongCoreTauActiveSourceMassIdentityV1
import Mathlib.Tactic

/-!
# Scalar bound transport from endpoint tau-active data to the source

These lemmas deliberately transport only the two scalar fields used by the
same-occurrence endpoint.  Keeping the dependent greedy witnesses outside
the transport avoids elaborating a second copy of their full payload.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8EndpointLongCoreTauActiveSourceScalarBoundTransportV1

open Submission.Kakeya.ConvexFactoring
open Family8EndpointLongCoreSourceTauIdentityTransportV5
open Family8EndpointLongCoreTauActiveSourceMassIdentityV1
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- Any upper bound for endpoint tau-active shading mass is the same upper
bound for the source shading mass. -/
theorem endpointLongCore_source_shadingMass_le_of_tauActive
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    {M : ENNReal}
    (hbound :
      (tauActiveCoarseDatum (fullRefinementDatum D)
        (identityRadiusCoherentCover (fullRefinementDatum D).family)
        (endpointScaleSequence delta
          (hD.delta_le_half.trans (by norm_num))) W).shading.shadingMass <= M) :
    D.shading.shadingMass <= M := by
  rw [endpointLongCore_tauActive_shadingMass_eq_source D hD P W] at hbound
  exact hbound

/-- Any upper bound for endpoint tau-active average multiplicity is the same
upper bound for the source average multiplicity. -/
theorem endpointLongCore_source_averageMultiplicity_le_of_tauActive
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    {M : ENNReal}
    (hbound :
      (tauActiveCoarseDatum (fullRefinementDatum D)
        (identityRadiusCoherentCover (fullRefinementDatum D).family)
        (endpointScaleSequence delta
          (hD.delta_le_half.trans (by norm_num))) W).shading.averageMultiplicity <= M) :
    D.shading.averageMultiplicity <= M := by
  rw [endpointLongCore_tauActive_averageMultiplicity_eq_source D hD P W]
    at hbound
  exact hbound

#print axioms endpointLongCore_source_shadingMass_le_of_tauActive
#print axioms endpointLongCore_source_averageMultiplicity_le_of_tauActive

end
end Family8EndpointLongCoreTauActiveSourceScalarBoundTransportV1
