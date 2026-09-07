import Family8Grounding.Family8EndpointIdentityTauActiveParentAdmissibilityV1
import Family8Grounding.Family8GreedyFactorTwoLowFreshRetainedV2
import Mathlib.Tactic

/-!
# Endpoint identity form of the retained fresh card-scale budget

The retained factor-two low theorem works at the radius of its literal
tau-active parent datum.  On the endpoint LongCore that radius is definitionally
identified by the existing theorem `tau = delta`.  This file performs only
that scalar rewrite; it neither reruns the greedy selection nor asks for a
new geometry or Katz--Tao certificate.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8EndpointIdentityTauActiveFreshRetainedCardScaleV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8EndpointLongCoreIdentityFirstFieldsV3
open Family8FullRefinementActualDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GreedyFactorTwoLowFreshRetainedV2
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- The sharp same-choice estimate on the endpoint source scale.  The
factor-two low restriction and the fresh child are passed literally; the
only new step is rewriting the tau radius to `delta`. -/
theorem endpointIdentity_tauActive_eight_mul_freshCardScale_le
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (A : ENNReal) {eta : Real}
    (hcoefficient :
      128 * A <= ((delta / 8 : NNReal) : ENNReal) ^ (-eta)) :
    let E := fullRefinementDatum D
    let C := identityRadiusCoherentCover E.family
    let hdeltaOne : delta <= 1 := hD.delta_le_half.trans (by norm_num)
    let S := endpointScaleSequence delta hdeltaOne
    let T := tauScaleCover E C S W
    let Dtau := activeParentActualTubeDatum T E.shading
    forall selectedLow : Finset {k // k ∈ T.activeCoarse},
      (restrictActualTubeDatum Dtau selectedLow).IsAdmissible ->
      IsKatzTao A
        (restrictActualTubeDatum Dtau selectedLow).family.bodyFamily ->
      forall selectedFresh : Finset {k // k ∈ selectedLow},
        selectedFresh.card <= selectedLow.card ->
        8 * proposition66ACardScaleVolume delta selectedFresh.card <=
          ((delta / 8 : NNReal) : ENNReal) ^ (-eta) := by
  dsimp only
  intro selectedLow hDlow hKTlow selectedFresh hcard
  let E := fullRefinementDatum D
  let C := identityRadiusCoherentCover E.family
  let hdeltaOne : delta <= 1 := hD.delta_le_half.trans (by norm_num)
  let S := endpointScaleSequence delta hdeltaOne
  let T := tauScaleCover E C S W
  let Dtau := activeParentActualTubeDatum T E.shading
  have htau : S.tau W.m = delta :=
    endpointLongCore_tau_eq_delta hdeltaOne C W
  have hcoefficientTau :
      128 * A <= (((S.tau W.m / 8 : NNReal) : ENNReal) ^ (-eta)) := by
    simpa only [htau] using hcoefficient
  have hsharp :=
    eight_mul_fresh_cardScale_le_divEight_negativePower_of_retained_low
      Dtau A selectedLow hDlow hKTlow selectedFresh hcard hcoefficientTau
  simpa only [htau] using hsharp

#print axioms endpointIdentity_tauActive_eight_mul_freshCardScale_le

end
end Family8EndpointIdentityTauActiveFreshRetainedCardScaleV1
