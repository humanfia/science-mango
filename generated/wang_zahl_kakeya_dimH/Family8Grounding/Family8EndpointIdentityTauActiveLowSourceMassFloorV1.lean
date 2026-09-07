import Family8Grounding.Family8AllFrostmanStickyUnionProducerV1
import Family8Grounding.Family8EndpointLongCoreTauActiveSourceMassIdentityV1
import Family8Grounding.Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
import Mathlib.Tactic

/-!
# Lossless endpoint source-mass transport to the tau-active low datum

The low fresh-card lower endpoint needs a mass floor on the literal
tau-active datum on which selectedLow and selectedFresh live. At the
identity endpoint, parent aggregation preserves shading mass exactly.
Therefore every source mass floor transports to that same datum with no
new scale power, constant, selection, or geometric hypothesis.

In particular the existing source Frostman theorem gives

    delta ^ (2 * etaSource) <= tauActiveMass.

This is intentionally the identity route, not the density-times-half-square
route: the latter would spend an unusable additional exponent two.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8EndpointIdentityTauActiveLowSourceMassFloorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8AllFrostmanStickyUnionProducerV1
open Family8EndpointLongCoreTauActiveSourceMassIdentityV1
open Family8FullRefinementActualDatumV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- Weakest exact interface: an arbitrary source-mass power floor is
transported to the definitionally same tau-active datum used by the greedy
low split. No exponent arithmetic is performed here. -/
theorem endpointIdentity_sourceMass_powerFloor_to_tauActive
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    {sourceExponent : Real}
    (hsourceMass :
      (delta : ENNReal) ^ sourceExponent <= D.shading.shadingMass) :
    let E := fullRefinementDatum D
    let C := identityRadiusCoherentCover E.family
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    let T := tauScaleCover E C S W
    let Dtau := activeParentActualTubeDatum T E.shading
    (delta : ENNReal) ^ sourceExponent <=
      Dtau.shading.shadingMass := by
  dsimp only
  let E := fullRefinementDatum D
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let T := tauScaleCover E C S W
  let Dtau := activeParentActualTubeDatum T E.shading
  have hmassEq : Dtau.shading.shadingMass = D.shading.shadingMass := by
    change (tauActiveCoarseDatum E C S W).shading.shadingMass =
      D.shading.shadingMass
    simpa only [E, C, S] using
      (endpointLongCore_tauActive_shadingMass_eq_source D hD P W)
  exact hsourceMass.trans_eq hmassEq.symm

/-- The existing genuine Frostman source floor, transported losslessly to
the same tau-active datum used by the retained fresh low theorem.
The exponent is exactly 2 * etaSource; there is no extra +2. -/
theorem endpointIdentity_frostman_sourceMass_powerFloor_to_tauActive
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    {etaSource : Real}
    (hF : FrostmanHypotheses D etaSource) :
    let E := fullRefinementDatum D
    let C := identityRadiusCoherentCover E.family
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    let T := tauScaleCover E C S W
    let Dtau := activeParentActualTubeDatum T E.shading
    (delta : ENNReal) ^ (2 * etaSource) <=
      Dtau.shading.shadingMass := by
  apply endpointIdentity_sourceMass_powerFloor_to_tauActive D hD P W
  exact delta_rpow_two_eta_le_shadingMass_of_frostman D hD hF

#print axioms endpointIdentity_sourceMass_powerFloor_to_tauActive
#print axioms
  endpointIdentity_frostman_sourceMass_powerFloor_to_tauActive

end
end Family8EndpointIdentityTauActiveLowSourceMassFloorV1
