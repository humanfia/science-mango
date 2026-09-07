import Family8Grounding.Family8EndpointLongCoreIdentityFirstFieldsV3
import Family8Grounding.Family8IdentifiedDividingWitnessFirstOuterParentTransportV1
import Family8Grounding.Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
import Family8Grounding.Family8ParentInjectiveAggregatedAverageIdentityV2
import Mathlib.Tactic

/-!
# Endpoint source-to-tau identity transport, V5

On the endpoint identity coherent cover the source-to-tau parent map is the
finite enumeration equivalence.  Parent aggregation is therefore lossless,
and the tau-active coarse average is exactly the original datum average.  V1
through V4 are failed namespace or predecessor drafts and are not imported.
-/

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal

namespace Family8EndpointLongCoreSourceTauIdentityTransportV5

open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8FullRefinementActualDatumV1
open Family8IdentifiedDividingWitnessFirstOuterParentTransportV1.Witness
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCrossingSourceTauShadingV2
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8ParentInjectiveAggregatedAverageIdentityV2
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

/-- The endpoint tau-active datum has exactly the source average
multiplicity. -/
theorem endpointLongCore_tauActive_averageMultiplicity_eq_source
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num)))) :
    (tauActiveCoarseDatum (fullRefinementDatum D)
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))) W).shading.averageMultiplicity =
      D.shading.averageMultiplicity := by
  let E := fullRefinementDatum D
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let C := identityRadiusCoherentCover E.family
  let S0 := sourceTauCover E C S W.m
  have hcover : S0 = tauScaleCover E C S W := rfl
  have hinjective : Set.InjOn S0.parent (S0.activeFine : Set _) := by
    intro i _hi j _hj hij
    change Fintype.equivFin _ i = Fintype.equivFin _ j at hij
    exact (Fintype.equivFin _).injective hij
  change (parentAggregatedShading (tauScaleCover E C S W)
    E.shading).averageMultiplicity = D.shading.averageMultiplicity
  rw [<- hcover]
  calc
    (parentAggregatedShading S0 E.shading).averageMultiplicity =
        (activeFineShading S0 E.shading).averageMultiplicity :=
      parentAggregatedShading_averageMultiplicity_eq_activeFineShading
        S0 E.shading hinjective
    _ = D.shading.averageMultiplicity :=
      fullRefinement_sourceTau_activeFine_averageMultiplicity D C S W.m

#print axioms endpointLongCore_tauActive_averageMultiplicity_eq_source

end
end Family8EndpointLongCoreSourceTauIdentityTransportV5
