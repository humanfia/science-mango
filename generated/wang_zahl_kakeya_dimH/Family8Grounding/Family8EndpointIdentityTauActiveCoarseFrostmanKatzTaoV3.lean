import Family8Grounding.Family8IdentityCoreCanonicalBufferedLossOneAdapterV1
import Family8Grounding.Family8IdentitySourceFrostmanKatzTaoCardScaleCancellationV2
import Family8Grounding.Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
import Family8Grounding.Family8StickyActiveRestrictedCoarseKatzTaoV1
import FamilyStickyGrounding.FamilyStickyScaleChainCappedSeedSequenceV2
import Mathlib.Tactic

/-!
# Source-Frostman Katz--Tao control on the literal identity tau-active coarse family

Only active-coarse-family equality is transported; the interval and global
covers themselves are not identified.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8EndpointIdentityTauActiveCoarseFrostmanKatzTaoV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8FullRefinementActualDatumV1
open Family8IdentityCoreCanonicalBufferedLossOneAdapterV1
open Family8IdentitySourceFrostmanKatzTaoCardScaleCancellationV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8StickyActiveRestrictedCoarseKatzTaoV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- Source Frostman control reaches the exact reindexed coarse family used by
the endpoint singleton partition. -/
theorem endpointLongCore_identity_tauActiveRestrictedCoarse_isKatzTao
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hepsilonHalf : P.epsilon ≤ 1 / 2)
    (hbufferedSixteenth :
      canonicalBufferedRadius W ≤ (1 / 16 : NNReal))
    {etaSource : Real} (hF : FrostmanHypotheses D etaSource) :
    let E := fullRefinementDatum D
    let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
    let C := identityRadiusCoherentCover E.family
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    let U0 := canonicalBufferedTauActiveCover E hE C S W
      P.epsilon_pos.le hepsilonHalf
    let U := activeFineRestrictedScaleCover U0
    IsKatzTao (identitySourceFrostmanKatzTaoConstant D
      (canonicalBufferedRadius W) etaSource) U.coarse.bodyFamily := by
  dsimp only
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let rho := canonicalBufferedRadius W
  let U0 := canonicalBufferedTauActiveCover E hE C S W
    P.epsilon_pos.le hepsilonHalf
  let U := activeFineRestrictedScaleCover U0
  let G := canonicalBufferedGlobalCover W hE.delta_pos
    P.epsilon_pos.le hepsilonHalf
  have hdeltaRho : delta ≤ rho := by
    dsimp only [rho, S]
    exact (S.delta_le_tau W.m).trans
      (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
  have hsixteenHalf : (1 / 16 : NNReal) ≤ (2 : NNReal)⁻¹ := by
    change (1 : Real) / 16 ≤ (2 : Real)⁻¹
    norm_num
  have hrhoHalf : rho ≤ (2 : NNReal)⁻¹ :=
    hbufferedSixteenth.trans hsixteenHalf
  have hglobalIdentity : G =
      identityRadiusScaleCover E.family rho hdeltaRho := by
    simpa only [G, rho, C, S] using
      identityCore_canonicalBufferedGlobalCover_eq_identityRadiusScaleCover
        E hE S P W hepsilonHalf
  have hglobal : G.IsKatzTaoAtScale
      (identitySourceFrostmanKatzTaoConstant D rho etaSource) := by
    rw [hglobalIdentity]
    exact identityRadiusScaleCover_isKatzTaoAtScale_of_sourceFrostman
      D hD rho hdeltaRho hrhoHalf hF
  have hfamily : U0.activeCoarseFamily = G.activeCoarseFamily := by
    simpa only [U0, G, E, hE, C, S] using
      canonicalBufferedTauActiveCover_activeCoarseFamily_eq_global
        E hE C S W P.epsilon_pos.le hepsilonHalf
  have hU0 : U0.IsKatzTaoAtScale
      (identitySourceFrostmanKatzTaoConstant D rho etaSource) := by
    intro K
    rw [hfamily]
    exact hglobal K
  simpa only [U] using
    activeFineRestrictedScaleCover_coarse_isKatzTao U0 hU0

#print axioms endpointLongCore_identity_tauActiveRestrictedCoarse_isKatzTao

end
end Family8EndpointIdentityTauActiveCoarseFrostmanKatzTaoV3
