import Family8Grounding.Family8EndpointLongCoreIdentityFirstFieldsV3
import Family8Grounding.Family8IdentifiedDividingWitnessFirstOuterParentTransportV1
import Family8Grounding.Family8NormalizedFirstCrossingFullRefinementAssemblyV1
import Family8Grounding.Family8NormalizedCrossingSourceTauShadingV2
import Family8Grounding.Family8ParentInjectiveAggregatedAverageIdentityV2
import FamilyStickyGrounding.FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
import Mathlib.Tactic

/-!
# Identity first fields and source-average transport for FirstCrossing, V3

V2 omitted the direct import that owns the active-fine source-average theorem.
This clean successor keeps the endpoint mathematics unchanged and resolves that
theorem through its authoritative namespace.
-/

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal

namespace Family8EndpointFirstCrossingIdentityFirstTransportV3

open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8EndpointLongCoreIdentityFirstFieldsV3
open Family8FullRefinementActualDatumV1
open Family8IdentifiedDividingWitnessFirstOuterParentTransportV1.Witness
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedCrossingSourceTauShadingV2
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8ParentInjectiveAggregatedAverageIdentityV2
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- Every FirstCrossing witness on the endpoint sequence has lower scale
exactly `delta`. -/
theorem endpointFirstCrossing_tau_eq_delta
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (eta : Nat → Real) (N : Nat)
    (W : FirstActualNormalizedCrossingWitness
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num)))
      epsilon hepsilon eta N) :
    (endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))).tau W.m = delta := by
  rw [show W.m = (0 : Fin 1) from Subsingleton.elim _ _,
    endpointScaleSequence_tau_zero]

/-- Endpoint source-to-tau parent aggregation preserves the original datum
average exactly. -/
theorem endpoint_sourceTau_parentAggregated_averageMultiplicity_eq_source
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (m : Fin 1) :
    (parentAggregatedShading
      (sourceTauCover (fullRefinementDatum D)
        (identityRadiusCoherentCover (fullRefinementDatum D).family)
        (endpointScaleSequence delta
          (hD.delta_le_half.trans (by norm_num))) m)
      (fullRefinementDatum D).shading).averageMultiplicity =
        D.shading.averageMultiplicity := by
  let E := fullRefinementDatum D
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let C := identityRadiusCoherentCover E.family
  let S0 := sourceTauCover E C S m
  have hinjective : Set.InjOn S0.parent (S0.activeFine : Set _) := by
    intro i _hi j _hj hij
    change Fintype.equivFin _ i = Fintype.equivFin _ j at hij
    exact (Fintype.equivFin _).injective hij
  calc
    (parentAggregatedShading S0 E.shading).averageMultiplicity =
        (activeFineShading S0 E.shading).averageMultiplicity :=
      parentAggregatedShading_averageMultiplicity_eq_activeFineShading
        S0 E.shading hinjective
    _ = D.shading.averageMultiplicity :=
      fullRefinement_sourceTau_activeFine_averageMultiplicity D C S m

/-- Exact first-factor fields consumed by the endpoint FirstCrossing DSO
record. -/
structure EndpointFirstCrossingIdentityFirstFields
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (eta : Nat → Real) (N : Nat)
    (W : FirstActualNormalizedCrossingWitness
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num)))
      epsilon hepsilon eta N)
    (gamma : Real) where
  firstCount : Nat
  firstAverage : ENNReal
  firstLoss : ENNReal
  firstCount_eq_one : firstCount = 1
  firstAverage_eq_one : firstAverage = 1
  firstLoss_eq_one : firstLoss = 1
  hFirst : firstAverage ≤ firstLoss *
    sectionEightScaleCountFrostmanFactor delta
      ((endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))).tau W.m)
      firstCount gamma

/-- Canonical callback-free first fields for an endpoint FirstCrossing
witness. -/
def endpointFirstCrossingIdentityFirstFields
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (eta : Nat → Real) (N : Nat)
    (W : FirstActualNormalizedCrossingWitness
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num)))
      epsilon hepsilon eta N)
    (gamma : Real) :
    EndpointFirstCrossingIdentityFirstFields
      D hD epsilon hepsilon eta N W gamma where
  firstCount := 1
  firstAverage := 1
  firstLoss := 1
  firstCount_eq_one := rfl
  firstAverage_eq_one := rfl
  firstLoss_eq_one := rfl
  hFirst := by
    rw [endpointFirstCrossing_tau_eq_delta
      D hD epsilon hepsilon eta N W,
      sectionEightScaleCountFrostmanFactor_self_one hD.delta_pos gamma]
    norm_num

theorem EndpointFirstCrossingIdentityFirstFields.firstLoss_le_zeroPower
    {D : ActualTubeDatum delta index} {hD : D.IsAdmissible}
    {epsilon : Real} {hepsilon : 0 ≤ epsilon}
    {eta : Nat → Real} {N : Nat}
    {W : FirstActualNormalizedCrossingWitness
      (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num)))
      epsilon hepsilon eta N}
    {gamma : Real}
    (X : EndpointFirstCrossingIdentityFirstFields
      D hD epsilon hepsilon eta N W gamma) :
    X.firstLoss ≤ (delta : ENNReal) ^ (0 : Real) := by
  rw [X.firstLoss_eq_one]
  simp

#print axioms endpointFirstCrossing_tau_eq_delta
#print axioms endpoint_sourceTau_parentAggregated_averageMultiplicity_eq_source
#print axioms EndpointFirstCrossingIdentityFirstFields
#print axioms endpointFirstCrossingIdentityFirstFields
#print axioms EndpointFirstCrossingIdentityFirstFields.firstLoss_le_zeroPower

end
end Family8EndpointFirstCrossingIdentityFirstTransportV3
