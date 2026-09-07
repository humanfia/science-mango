import Family8Grounding.Family8CoreHighPrefixPostFiberLogSameQPayloadV1
import Family8Grounding.Family8EndpointIdentityCorrelatedPreQHighPrefixDichotomyV1
import Mathlib.Tactic

/-!
# Correlated endpoint dichotomy after the fibre-log same-q selection

This is a thin wrapper around the pre-occurrence endpoint dichotomy.  Its low
branch is unchanged.  On the high branch, endpoint mass identity supplies the
nonzero tau-active source needed by the existing fibre-log weighted selector.
No additional hypothesis, side label, or container is introduced.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8EndpointIdentityCorrelatedPostFiberLogSameQDichotomyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CoreHighPrefixPostFiberLogSameQPayloadV1
open Family8EndpointIdentityCorrelatedPreQHighPrefixDichotomyV1
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointLongCoreTauActiveSourceMassIdentityV1
open Family8FullRefinementActualDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LowFreshCorrelatedPowerBudgetsV1
open Family8LowFreshLongIntervalBaseScaleBridgeV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma targetEpsilon : Real}

/-- Close the correlated low branch, or expose the post-fibre-log same-q
high payload on the same endpoint tau-active datum.

All inputs and local endpoint data are exactly those of the pre-`q`
dichotomy.  The only additional proof step is deriving nonzero tau-active
mass from the already supplied Frostman density lower bound. -/
theorem exists_endpointIdentity_correlated_dividingScaleOutput_or_coreHighPrefixPostFiberLogSameQPayload_of_gamma_le_one
    {etaKT outputEta : Real} {delta0 : NNReal}
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (hKTP : KatzTaoAtParameters
      beta (sectionEightFixedNu P) etaKT delta0)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (j : Nat) (hj : j <= P.N)
    (hbeta : 0 < beta)
    (hgammaOne : gamma <= 1)
    (hTargetEpsilon0 : 0 <= targetEpsilon)
    (hetaKTPos : 0 < etaKT)
    (hetaKTCap : etaKT <= P.epsilon ^ 2 * P.eta 0 / 32)
    (houtputCap : outputEta <= P.eta 0)
    (houtputShare : 16 * outputEta <= etaKT)
    (hdelta0 : delta / 8 <= delta0)
    (hsmallPower : delta <=
      lowFreshCorrelatedPowerThreshold etaKT (P.eta 0))
    (hsmallBase : delta <= lowFreshLongIntervalBaseScaleThreshold P)
    (hF : FrostmanHypotheses D outputEta) :
    let E := fullRefinementDatum D
    let C := identityRadiusCoherentCover E.family
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    let T := tauScaleCover E C S W
    let Dtau := activeParentActualTubeDatum T E.shading
    let A : ENNReal := (delta : ENNReal) ^ (-(etaKT / 8))
    DividingScaleOutput D P targetEpsilon \/
      CoreHighPrefixPostFiberLogSameQPayload Dtau A := by
  dsimp only
  let E := fullRefinementDatum D
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let T := tauScaleCover E C S W
  let Dtau := activeParentActualTubeDatum T E.shading
  let A : ENNReal := (delta : ENNReal) ^ (-(etaKT / 8))
  have hdensityPos : 0 < D.shading.shadingDensity := by
    exact (ENNReal.rpow_pos
      (ENNReal.coe_pos.mpr hD.delta_pos)
      ENNReal.coe_ne_top).trans_le hF.1
  have hsourceMass0 : D.shading.shadingMass ≠ 0 := by
    intro hzero
    have hdensityZero : D.shading.shadingDensity = 0 := by
      simp [Shading.shadingDensity, hzero]
    rw [hdensityZero] at hdensityPos
    exact (lt_irrefl 0) hdensityPos
  have hmassEq : Dtau.shading.shadingMass =
      D.shading.shadingMass := by
    change (tauActiveCoarseDatum E C S W).shading.shadingMass =
      D.shading.shadingMass
    simpa only [E, C, S] using
      (endpointLongCore_tauActive_shadingMass_eq_source D hD P W)
  have hDtauMass0 : Dtau.shading.shadingMass ≠ 0 := by
    rw [hmassEq]
    exact hsourceMass0
  have hsplit :=
    exists_endpointIdentity_correlated_dividingScaleOutput_or_coreHighPrefixWithFirstHitMass_of_gamma_le_one
      (etaKT := etaKT) (outputEta := outputEta) (delta0 := delta0)
      D hD P hKTP W j hj hbeta hgammaOne hTargetEpsilon0
        hetaKTPos hetaKTCap houtputCap houtputShare hdelta0
        hsmallPower hsmallBase hF
  dsimp only at hsplit
  rcases hsplit with hlow | hhigh
  · exact Or.inl hlow
  · exact Or.inr
      (coreHighPrefixWithFirstHitMass_to_postFiberLogSameQPayload
        Dtau A hDtauMass0 hhigh)

#print axioms
  exists_endpointIdentity_correlated_dividingScaleOutput_or_coreHighPrefixPostFiberLogSameQPayload_of_gamma_le_one

end
end Family8EndpointIdentityCorrelatedPostFiberLogSameQDichotomyV1
