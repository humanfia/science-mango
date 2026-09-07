import Family8Grounding.Family8EndpointLongCoreIdentitySingletonAssemblySelectedFineSourcePowersV6
import Family8Grounding.Family8StickyActiveIndexFrozenComparableAssemblyV5
import Family8Grounding.Family8StickyScaleCoverFrostmanInheritanceV1
import FamilyStickyGrounding.FamilyStickyScaleChainCappedSeedSequenceV2
import Mathlib.Tactic

/-!
# Identity endpoint source-active-fine density floor
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open scoped ENNReal NNReal

namespace Family8EndpointIdentitySourceActiveFineDensityFloorV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8EndpointLongCoreIdentitySingletonAssemblySelectedFineSourcePowersV6
open Family8FullRefinementActualDatumV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- The source-active-fine shading of the literal identity tau cover has the
original source Frostman density floor. -/
theorem endpointLongCore_identity_sourceActiveFineShading_density_lower
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    {etaSource : Real} (hF : FrostmanHypotheses D etaSource) :
    let E := fullRefinementDatum D
    let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
    let C := identityRadiusCoherentCover E.family
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    let U0 := canonicalBufferedTauActiveCover E hE C S W
      P.epsilon_pos.le hepsilonHalf
    let Dtau := tauActiveCoarseDatum E C S W
    let U := activeFineRestrictedScaleCover U0
    let Y := activeFineRestrictedShading U0 Dtau.shading
    (delta : ENNReal) ^ etaSource ≤
      (sourceActiveFineShading (toConvexFactorization U) Y).shadingDensity := by
  dsimp only
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let U0 := canonicalBufferedTauActiveCover E hE C S W
    P.epsilon_pos.le hepsilonHalf
  let Dtau := tauActiveCoarseDatum E C S W
  let U := activeFineRestrictedScaleCover U0
  let Y := activeFineRestrictedShading U0 Dtau.shading
  have hU : U.activeFine = Finset.univ :=
    activeFineRestrictedScaleCover_activeFine U0
  have hU0 : U0.activeFine = Finset.univ :=
    canonicalBufferedTauActiveCover_activeFine
      E hE C S W P.epsilon_pos.le hepsilonHalf
  have hsourceDensity :
      (sourceActiveFineShading
        (toConvexFactorization U) Y).shadingDensity =
        D.shading.shadingDensity := by
    calc
      (sourceActiveFineShading
          (toConvexFactorization U) Y).shadingDensity = Y.shadingDensity :=
        sourceActiveFineShading_density_eq_of_fine_eq_univ
          (toConvexFactorization U) Y (by
            simpa only [toConvexFactorization_fine] using hU)
      _ = Dtau.shading.shadingDensity :=
        activeFineRestrictedShading_density_eq_of_activeFine_eq_univ
          U0 Dtau.shading hU0
      _ = D.shading.shadingDensity :=
        endpointLongCore_identity_tauActive_shadingDensity_eq_source D hD P W
  exact hF.1.trans_eq hsourceDensity.symm

#print axioms
  endpointLongCore_identity_sourceActiveFineShading_density_lower

end
end Family8EndpointIdentitySourceActiveFineDensityFloorV2
