import Family8Grounding.Family8EndpointIdentityLongCoreSourceKatzTaoBudgetV1
import Family8Grounding.Family8EndpointLongCoreHalfRadiusThresholdV2
import Family8Grounding.Family8SectionEightOutputEtaV1
import Family8Grounding.Family8StickyActiveCoarseKatzTaoCardScaleMassUpperV4
import Mathlib.Tactic

/-!
# Direct endpoint identity long-core numerical composer

This endpoint-only adapter replaces the canonical Frostman-constant route to
the lower bound for `X` by the source Frostman mass bound.  A source Katz--Tao
object remains an explicit conditional input.  The result stops at the raw
long-interval numerical comparison and makes no DSO claim.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8EndpointIdentityLongCoreDirectNumericsComposerV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalLowerBufferedScaleV4
open Family8CanonicalSourceKatzTaoNNRealV1
open Family8EndpointIdentityLongCoreSourceKatzTaoBudgetV1
open Family8EndpointLongCoreHalfRadiusThresholdV2
open Family8FullRefinementActualDatumV1
open Family8IdentityCoreSourceKatzTaoBootstrapV1
open Family8IdentityRadiusSourceKatzTaoTransportV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open Family8SectionEightOutputEtaV1
open Family8StickyActiveCoarseKatzTaoCardScaleMassUpperV4.StickyScaleCover
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma sourceEta etaKT : Real}

/-- The three independent endpoint small-scale requirements: half radius,
source Katz--Tao scalar absorption, and absorption of the fixed factor eight
in the direct source-mass lower bound. -/
def endpointIdentityLongCoreDirectNumericsThreshold
    (P : ParameterLadder epsilon0 beta gamma) (stage : Nat) : NNReal :=
  min (endpointLongCoreHalfRadiusThreshold P)
    (min (endpointIdentityLongCoreSourceKatzTaoBudgetThreshold P)
      (endpointIdentityLongCoreDirectXLowerThreshold (P.eta stage)))

theorem endpointIdentityLongCoreDirectNumericsThreshold_pos
    (P : ParameterLadder epsilon0 beta gamma) (stage : Nat)
    (hbeta : 0 < beta) (hgamma : gamma <= 1) :
    0 < endpointIdentityLongCoreDirectNumericsThreshold P stage := by
  rw [endpointIdentityLongCoreDirectNumericsThreshold, lt_min_iff,
    lt_min_iff]
  exact ⟨endpointLongCoreHalfRadiusThreshold_pos P hbeta hgamma,
    endpointIdentityLongCoreSourceKatzTaoBudgetThreshold_pos P,
    endpointIdentityLongCoreDirectXLowerThreshold_pos (P.eta stage)⟩

/-- Conditional source Katz--Tao plus source Frostman mass close the raw
endpoint long-interval numerical comparison without a canonical Frostman
constant.  The source Katz--Tao object is intentionally an explicit input. -/
theorem longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_endpointIdentity_direct
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hFOutput : FrostmanHypotheses D
      (sectionEightOutputEta P sourceEta))
    (hKTsource : IsKatzTao
      (canonicalSourceKatzTaoNNReal delta etaKT : ENNReal)
      (fullRefinementDatum D).family.bodyFamily)
    (hetaKT : etaKT <= P.epsilon +
      10 * P.eta W.stage / (P.epsilon * beta))
    (hsmall : delta <=
      endpointIdentityLongCoreDirectNumericsThreshold P W.stage) :
    longIntervalKatzTaoRHSENNReal
        ((endpointScaleSequence delta
          (hD.delta_le_half.trans (by norm_num))).tau W.m)
        (canonicalBufferedRadius W)
        (activeCoarseCardScaleMass
          (canonicalBufferedGlobalCover W hD.delta_pos P.epsilon_pos.le
            (by
              nlinarith [P.epsilon_gap] : P.epsilon <= 1 / 2)))
        P.epsilon (10 * P.eta W.stage / (P.epsilon * beta)) beta <=
      longIntervalFrostmanTargetENNReal
        ((endpointScaleSequence delta
          (hD.delta_le_half.trans (by norm_num))).tau W.m)
        (canonicalBufferedRadius W)
        (activeCoarseCardScaleMass
          (canonicalBufferedGlobalCover W hD.delta_pos P.epsilon_pos.le
            (by
              nlinarith [P.epsilon_gap] : P.epsilon <= 1 / 2)))
        (10 * P.eta W.stage / (P.epsilon * beta)) gamma := by
  let hdeltaOne : delta <= 1 := hD.delta_le_half.trans (by norm_num)
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let S := endpointScaleSequence delta hdeltaOne
  have hgapOne : gamma - beta <= 1 := by linarith
  have hepsilonHalf : P.epsilon <= 1 / 2 := by
    nlinarith [P.epsilon_gap]
  let U := canonicalBufferedGlobalCover W hD.delta_pos
    P.epsilon_pos.le hepsilonHalf
  let b := canonicalBufferedRadius W
  let X := activeCoarseCardScaleMass U
  let A := canonicalSourceKatzTaoNNReal delta etaKT
  let etaPrime := 10 * P.eta W.stage / (P.epsilon * beta)
  have hsmallHalf : delta <= endpointLongCoreHalfRadiusThreshold P := by
    exact hsmall.trans (min_le_left _ _)
  have hsmallRest : delta <=
      min (endpointIdentityLongCoreSourceKatzTaoBudgetThreshold P)
        (endpointIdentityLongCoreDirectXLowerThreshold (P.eta W.stage)) := by
    exact hsmall.trans (min_le_right _ _)
  have hsmallAKT : delta <=
      endpointIdentityLongCoreSourceKatzTaoBudgetThreshold P :=
    hsmallRest.trans (min_le_left _ _)
  have hsmallX : delta <=
      endpointIdentityLongCoreDirectXLowerThreshold (P.eta W.stage) :=
    hsmallRest.trans (min_le_right _ _)
  have hrhoHalf : b <= (2 : NNReal)⁻¹ := by
    dsimp only [b]
    exact canonicalBufferedRadius_le_half_of_endpointSmall P hbeta hgamma
      hdeltaOne W hsmallHalf
  have hKTcover : U.IsKatzTaoAtScale
      (identityRadiusKatzTaoVolumeRatio delta b * (A : ENNReal)) := by
    dsimp only [U, b, A, E, hE, S]
    exact
      identityCore_canonicalBufferedGlobalCover_isKatzTaoAtScale_of_source
        (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
        (endpointScaleSequence delta hdeltaOne) P W hepsilonHalf hrhoHalf
        hKTsource
  have hKTcoverNN : U.IsKatzTaoAtScale
      ((identityRadiusKatzTaoVolumeRatioNNReal delta b * A : NNReal) :
        ENNReal) := by
    simpa only [ENNReal.coe_mul,
      coe_identityRadiusKatzTaoVolumeRatioNNReal delta b hD.delta_pos]
      using hKTcover
  have hXUpperCore : X <=
      1024 * (identityRadiusKatzTaoVolumeRatioNNReal delta b * A) := by
    dsimp only [X]
    exact
      activeCoarseCardScaleMass_le_1024_mul_nnreal_of_isKatzTaoAtScale
        E hE U hrhoHalf
          (identityRadiusKatzTaoVolumeRatioNNReal delta b * A) hKTcoverNN
  have hAKT :
      1024 * (identityRadiusKatzTaoVolumeRatioNNReal delta b * A) <=
        S.tau W.m ^ (-longIntervalDeltaLoss P.epsilon etaPrime) := by
    dsimp only [S, b, A, etaPrime]
    exact endpointIdentityLongCore_sourceKatzTao_hAKT hD.delta_pos
      hdeltaOne P W hetaKT hsmallAKT
  have hXUpper : X <=
      S.tau W.m ^ (-longIntervalDeltaLoss P.epsilon etaPrime) :=
    hXUpperCore.trans hAKT
  have hetaOutputStage :
      sectionEightOutputEta P sourceEta <= P.eta W.stage := by
    exact (sectionEightOutputEta_le_fixedNu P sourceEta).trans
      (by
        simpa only [sectionEightFixedNu] using
          eta_zero_le_eta_of_stage_le P W.stage W.stage_le)
  have hbetaOne : beta <= 1 := by
    nlinarith [P.epsilon_gap, P.epsilon_pos]
  have hepsilonOne : P.epsilon <= 1 := by
    nlinarith [P.epsilon_gap]
  have hepsilonBetaOne : P.epsilon * beta <= 1 := by
    calc
      P.epsilon * beta <= 1 * 1 :=
        mul_le_mul hepsilonOne hbetaOne hbeta.le (by norm_num)
      _ = 1 := by norm_num
  have hexponent :
      2 * sectionEightOutputEta P sourceEta + P.eta W.stage <=
        etaPrime := by
    have hden : 0 < P.epsilon * beta :=
      mul_pos P.epsilon_pos hbeta
    apply (le_div_iff₀ hden).2
    calc
      (2 * sectionEightOutputEta P sourceEta + P.eta W.stage) *
          (P.epsilon * beta) <=
        (3 * P.eta W.stage) * (P.epsilon * beta) :=
          mul_le_mul_of_nonneg_right (by linarith) hden.le
      _ <= (3 * P.eta W.stage) * 1 :=
        mul_le_mul_of_nonneg_left hepsilonBetaOne
          (mul_nonneg (by norm_num) (P.eta_pos W.stage).le)
      _ <= 10 * P.eta W.stage := by
        nlinarith [P.eta_pos W.stage]
  have hXLowerDelta : delta ^ etaPrime <= X := by
    dsimp only [X, U]
    exact endpointIdentityLongCore_directXLower_of_frostman
      (etaF := sectionEightOutputEta P sourceEta)
      (absorbExponent := P.eta W.stage) (targetExponent := etaPrime)
      D hD P W hepsilonHalf hFOutput (P.eta_pos W.stage) hexponent hsmallX
  have hXLower : S.tau W.m ^ etaPrime <= X := by
    dsimp only [S]
    rw [show W.m = (0 : Fin 1) from Subsingleton.elim _ _,
      endpointScaleSequence_tau_zero]
    exact hXLowerDelta
  have hd : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have hdOne : S.tau W.m <= 1 :=
    (S.tau_le_theta W.m).trans (S.theta_le_one W.m)
  have hdb : S.tau W.m <= b := by
    dsimp only [b]
    exact tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le
  have hbUpper : b <= S.tau W.m ^ (1 - P.epsilon) := by
    dsimp only [b, canonicalBufferedRadius]
    exact canonicalLowerBufferedScale_le_tau_rpow_one_sub
      (S.theta_le_one W.m) P.epsilon_pos.le
  have hraw := longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal
    P W.stage hd hdOne hdb hbUpper hXLower hXUpper hbeta hgamma
  simpa only [S, b, X, U, etaPrime] using hraw

#print axioms endpointIdentityLongCoreDirectNumericsThreshold_pos
#print axioms
  longIntervalKatzTaoRHSENNReal_le_frostmanTargetENNReal_of_endpointIdentity_direct

end
end Family8EndpointIdentityLongCoreDirectNumericsComposerV1
