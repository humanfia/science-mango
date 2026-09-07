import Family8Grounding.Family8EndpointLongCoreIdentityFirstFieldsV3
import Family8Grounding.Family8FullRefinementActualDatumV1
import Family8Grounding.Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
import Family8Grounding.Family8ParameterLadderV1
import Family8Grounding.Family8SameScaleActiveParentActualDatumAdmissibilityV1
import Mathlib.Tactic

/-!
# Endpoint identity tau-parent admissibility

On the one-step endpoint scale sequence the selected lower scale is
definitionally equal to the source radius.  The literal identity-cover tau
parents are therefore same-scale parents, so the existing carrier-rigidity
theorem transfers source admissibility without a parent selection or a new
geometric assumption.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8EndpointIdentityTauActiveParentAdmissibilityV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8EndpointLongCoreIdentityFirstFieldsV3
open Family8FullRefinementActualDatumV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8SameScaleActiveParentActualDatumAdmissibilityV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- Equality of radii is enough to invoke the same-scale parent theorem;
this wrapper keeps the equality eliminator outside the dependent
`ActiveParentIndex` expression. -/
theorem activeParentActualTubeDatum_isAdmissible_of_scale_eq
    {rho : NNReal}
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (Y : Shading D.family.bodyFamily)
    (hrho : rho = delta) :
    (activeParentActualTubeDatum S Y).IsAdmissible := by
  subst rho
  exact activeParentActualTubeDatum_isAdmissible_of_sameScale D hD S Y

/-- The exact active-parent datum used by the greedy split is admissible on
the endpoint identity LongCore because its parent radius equals `delta`. -/
theorem endpointIdentity_tauActiveParent_isAdmissible
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num)))) :
    (activeParentActualTubeDatum
      (tauScaleCover (fullRefinementDatum D)
        (identityRadiusCoherentCover (fullRefinementDatum D).family)
        (endpointScaleSequence delta
          (hD.delta_le_half.trans (by norm_num))) W)
      (fullRefinementDatum D).shading).IsAdmissible := by
  let E := fullRefinementDatum D
  let C := identityRadiusCoherentCover E.family
  let hdeltaOne : delta <= 1 := hD.delta_le_half.trans (by norm_num)
  let S := endpointScaleSequence delta hdeltaOne
  have htau : S.tau W.m = delta :=
    endpointLongCore_tau_eq_delta hdeltaOne C W
  change (activeParentActualTubeDatum
    (tauScaleCover E C S W) E.shading).IsAdmissible
  exact activeParentActualTubeDatum_isAdmissible_of_scale_eq
    E (fullRefinementDatum_isAdmissible hD)
      (tauScaleCover E C S W) E.shading htau

/-- Compatibility certificate for consumers still phrased through
`TauActiveCoarseAdmissibility`; both fields come from the same exact
same-scale parent datum above. -/
theorem endpointIdentity_tauActiveCoarseAdmissibility
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num)))) :
    TauActiveCoarseAdmissibility
      (fullRefinementDatum D)
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))) W := by
  have hparent := endpointIdentity_tauActiveParent_isAdmissible D hD P W
  exact
    { contained_in_unit_ball := hparent.contained_in_unit_ball
      pairwise_essentiallyDistinct := hparent.pairwise_essentiallyDistinct }

#print axioms activeParentActualTubeDatum_isAdmissible_of_scale_eq
#print axioms endpointIdentity_tauActiveParent_isAdmissible
#print axioms endpointIdentity_tauActiveCoarseAdmissibility

end
end Family8EndpointIdentityTauActiveParentAdmissibilityV1
