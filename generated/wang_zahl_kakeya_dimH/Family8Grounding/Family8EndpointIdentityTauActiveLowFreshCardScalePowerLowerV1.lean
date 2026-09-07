import Family8Grounding.Family8EndpointIdentityTauActiveLowSourceMassFloorV1
import Family8Grounding.Family8GreedyFactorTwoLowFreshCardLowerRetainedV1
import Mathlib.Tactic

/-!
# Endpoint Frostman mass floor to the retained low fresh-card scale

This is the thin endpoint connector between the lossless Frostman source-mass
transport and the retained same-choice fresh-card lower bound.  It keeps the
literal tau-active datum, factor-two low restriction, and fresh child fixed.
No Katz--Tao constant is selected here and the fresh selector is not rerun.

All analytic expenditure remains visible: the fresh-loss envelope, absorption
of the fixed constant `16`, and the exponent ledger are explicit hypotheses.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8EndpointIdentityTauActiveLowFreshCardScalePowerLowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8B2NormalizedConflictKatzTaoCapV6
open Family8EndpointLongCoreIdentityFirstFieldsV3
open Family8EndpointIdentityTauActiveLowSourceMassFloorV1
open Family8FullRefinementActualDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GreedyFactorTwoLowFreshCardLowerRetainedV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8ScaleContainedB2NativeFreshKatzTaoEndpointV1
open Family8SharpKatzTaoOrGreedyHighConcentrationV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- On the identity endpoint, the genuine Frostman mass floor and the retained
card lower bound concern the definitionally same tau-active datum and the same
`selectedLow`/`selectedFresh`.  The conclusion is already expressed at the
source radius `delta`; the only scale operation in the proof is the existing
endpoint identity `tau = delta`. -/
theorem endpointIdentity_frostman_to_tauActive_freshCardScale_powerLower
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    {etaSource : Real} (hF : FrostmanHypotheses D etaSource)
    (A : ENNReal)
    {lossExponent absorbExponent etaPrime : Real}
    (hloss : (sourceKatzTaoFreshLoss A : ENNReal) <=
      (delta : ENNReal) ^ (-lossExponent))
    (hconstant : (16 : ENNReal) <=
      (delta : ENNReal) ^ (-absorbExponent))
    (hexponent :
      2 * etaSource + lossExponent + absorbExponent <= etaPrime) :
    let E := fullRefinementDatum D
    let C := identityRadiusCoherentCover E.family
    let hdeltaOne : delta <= 1 := hD.delta_le_half.trans (by norm_num)
    let S := endpointScaleSequence delta hdeltaOne
    let T := tauScaleCover E C S W
    let Dtau := activeParentActualTubeDatum T E.shading
    forall selectedLow : Finset {k // k ∈ T.activeCoarse},
      Dtau.shading.shadingMass <= 2 *
        (restrictActualTubeDatum Dtau selectedLow).shading.shadingMass ->
      (restrictActualTubeDatum Dtau selectedLow).IsAdmissible ->
      forall selectedFresh : Finset {k // k ∈ selectedLow},
        (selectedLow.card : ENNReal) <=
          (sourceKatzTaoFreshLoss A : ENNReal) *
            (selectedFresh.card : ENNReal) ->
        (delta : ENNReal) ^ etaPrime <=
          proposition66ACardScaleVolume delta selectedFresh.card := by
  dsimp only
  intro selectedLow hmass hDlow selectedFresh hcardLower
  let E := fullRefinementDatum D
  let C := identityRadiusCoherentCover E.family
  let hdeltaOne : delta <= 1 := hD.delta_le_half.trans (by norm_num)
  let S := endpointScaleSequence delta hdeltaOne
  let T := tauScaleCover E C S W
  let Dtau := activeParentActualTubeDatum T E.shading
  have htau : S.tau W.m = delta :=
    endpointLongCore_tau_eq_delta hdeltaOne C W
  have hsourceDelta :
      (delta : ENNReal) ^ (2 * etaSource) <=
        Dtau.shading.shadingMass := by
    simpa only [E, C, hdeltaOne, S, T, Dtau] using
      (endpointIdentity_frostman_sourceMass_powerFloor_to_tauActive
        D hD P W hF)
  have hsourceTau :
      ((S.tau W.m : NNReal) : ENNReal) ^ (2 * etaSource) <=
        Dtau.shading.shadingMass := by
    simpa only [htau] using hsourceDelta
  have hlossTau :
      (sourceKatzTaoFreshLoss A : ENNReal) <=
        ((S.tau W.m : NNReal) : ENNReal) ^ (-lossExponent) := by
    simpa only [htau] using hloss
  have hconstantTau :
      (16 : ENNReal) <=
        ((S.tau W.m : NNReal) : ENNReal) ^ (-absorbExponent) := by
    simpa only [htau] using hconstant
  have hpower :=
    freshCardScale_powerLower_of_sourceMass_and_freshLoss
      Dtau selectedLow hmass hDlow A selectedFresh hcardLower
      hsourceTau hlossTau hconstantTau hexponent
  simpa only [htau] using hpower

#print axioms
  endpointIdentity_frostman_to_tauActive_freshCardScale_powerLower

end
end Family8EndpointIdentityTauActiveLowFreshCardScalePowerLowerV1
