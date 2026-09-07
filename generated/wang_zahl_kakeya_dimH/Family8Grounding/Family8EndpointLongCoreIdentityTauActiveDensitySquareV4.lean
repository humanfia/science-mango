import Family8Grounding.Family8EndpointLongCoreIdentitySingletonAssemblySelectedFineSourcePowersV6
import FamilyStickyGrounding.FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
import Mathlib.Tactic

/-!
# Identity LongCore tau-active density square, V4

V1 omitted the identity-cover owner; V2 used a no-progress rewrite; V3 used
reflexivity across real-rpow and natural-power notation.  This clean
successor applies the exact `ENNReal.rpow_natCast` theorem as a term.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open scoped ENNReal NNReal

namespace Family8EndpointLongCoreIdentityTauActiveDensitySquareV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8EndpointLongCoreIdentitySingletonAssemblySelectedFineSourcePowersV6
open Family8FullRefinementActualDatumV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- The literal active-restricted tau shading on the identity endpoint has
the square of the original Frostman density floor. -/
theorem endpointLongCore_identity_canonicalBufferedTauActive_density_sq_lower
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hepsilonHalf : P.epsilon <= 1 / 2)
    {etaSource : Real}
    (hF : FrostmanHypotheses D etaSource) :
    let E := fullRefinementDatum D
    let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
    let C := identityRadiusCoherentCover E.family
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    let U0 := canonicalBufferedTauActiveCover E hE C S W
      P.epsilon_pos.le hepsilonHalf
    let Dtau := tauActiveCoarseDatum E C S W
    let Y := activeFineRestrictedShading U0 Dtau.shading
    (delta : ENNReal) ^ (2 * etaSource) <= Y.shadingDensity ^ 2 := by
  dsimp only
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let U0 := canonicalBufferedTauActiveCover E hE C S W
    P.epsilon_pos.le hepsilonHalf
  let Dtau := tauActiveCoarseDatum E C S W
  let Y := activeFineRestrictedShading U0 Dtau.shading
  have hactive : U0.activeFine = Finset.univ :=
    canonicalBufferedTauActiveCover_activeFine
      E hE C S W P.epsilon_pos.le hepsilonHalf
  have hYdensity : Y.shadingDensity = D.shading.shadingDensity := by
    calc
      Y.shadingDensity = Dtau.shading.shadingDensity :=
        activeFineRestrictedShading_density_eq_of_activeFine_eq_univ
          U0 Dtau.shading hactive
      _ = D.shading.shadingDensity :=
        endpointLongCore_identity_tauActive_shadingDensity_eq_source
          D hD P W
  calc
    (delta : ENNReal) ^ (2 * etaSource) =
        (delta : ENNReal) ^ (etaSource * 2) := by
      congr 1
      ring
    _ = ((delta : ENNReal) ^ etaSource) ^ (2 : Real) := by
      rw [ENNReal.rpow_mul]
    _ = ((delta : ENNReal) ^ etaSource) ^ 2 := by
      exact ENNReal.rpow_natCast _ 2
    _ <= D.shading.shadingDensity ^ 2 :=
      pow_le_pow_left' hF.1 2
    _ = Y.shadingDensity ^ 2 := by
      rw [hYdensity]

#print axioms
  endpointLongCore_identity_canonicalBufferedTauActive_density_sq_lower

end
end Family8EndpointLongCoreIdentityTauActiveDensitySquareV4
