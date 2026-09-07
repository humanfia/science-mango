import Family8Grounding.Family8ContractedJohnNormalizedProxyScaleRatioV3
import Family8Grounding.Family8EndpointLongCoreTauActiveSourceMassIdentityV1
import Family8Grounding.Family8IdentityCoreTauActiveSingletonFiberV4
import Family8Grounding.Family8StickyActiveIndexFrozenComparableAssemblyV5
import Mathlib.Tactic

/-!
# Endpoint identity no-KT source and fibre power inputs, V3

V1 and V2 are failed drafts and are not imported.  V2 left only the coercion
of the elementary bound `3 / 64 ≤ 1` unresolved; this successor proves it via
`NNReal.coe_le_coe`.  The singleton endpoint fibre gives both card powers, and
the exact source-mass identity gives the selected source lower bound without a
source Katz--Tao hypothesis or doubled-fibre cap.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4200000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8EndpointIdentityNoKTSourceCardPowerV3

open Family8AllFrostmanStickyUnionProducerV1
open Family8ContractedJohnActualTubeProxyV1
open Family8ContractedJohnNormalizedProxyScaleRatioV3
open Family8EndpointLongCoreTauActiveSourceMassIdentityV1
open Family8FullRefinementActualDatumV1
open Family8IdentityCoreTauActiveSingletonFiberV4
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8StickyActiveIndexFrozenComparableAssemblyV5
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open Family8StickyShadingAwareLogBucketSelectionV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open Submission.Kakeya.Uniformity

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth N : Nat} {epsilon : Real} {eta : Nat -> Real}

/-- On an arbitrary normalized long witness over the identity coherent cover,
one active restricted fibre simultaneously satisfies the exact two power
shapes expected by the fresh low-CF producer, with coefficient `K = 1`. -/
theorem identityCore_canonicalBufferedTauActiveRestricted_dualPower
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    (W : NormalizedLongIntervalCoreWitness D.family
      (identityRadiusCoherentCover D.family) N epsilon eta S)
    (hepsilon : 0 <= epsilon) (hepsilonHalf : epsilon <= 1 / 2)
    {cardExp kappa : Real}
    (hcardExp : 0 <= cardExp) (hcountExp : 0 < 2 + kappa)
    (q : {q // q ∈
      (activeFineRestrictedScaleCover
        (canonicalBufferedTauActiveCover D hD
          (identityRadiusCoherentCover D.family) S W
            hepsilon hepsilonHalf)).activeCoarse}) :
    let tau := S.tau W.m
    let rho := canonicalBufferedRadius W
    let U0 := canonicalBufferedTauActiveCover D hD
      (identityRadiusCoherentCover D.family) S W
        hepsilon hepsilonHalf
    let U := activeFineRestrictedScaleCover U0
    (Fintype.card {i // i ∈ U.fiber q.1} : ENNReal) <=
        (((contractedJohnProxyRadius tau rho / 8 : NNReal) : ENNReal) ^
          (-cardExp)) /\
      (Fintype.card {i // i ∈ U.fiber q.1} : ENNReal) <=
        1 * (((tau : ENNReal) / (rho : ENNReal)) ^ (-(2 + kappa))) := by
  dsimp only
  let tau := S.tau W.m
  let rho := canonicalBufferedRadius W
  let U0 := canonicalBufferedTauActiveCover D hD
    (identityRadiusCoherentCover D.family) S W hepsilon hepsilonHalf
  let U := activeFineRestrictedScaleCover U0
  let scale : NNReal := contractedJohnProxyRadius tau rho / 8
  let ratio : ENNReal := (tau : ENNReal) / (rho : ENNReal)
  have htauPos : 0 < tau := by
    dsimp only [tau]
    exact hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have hrhoPos : 0 < rho := by
    dsimp only [rho]
    exact canonicalBufferedRadius_pos W hD.delta_pos hepsilon
  have htauRho : tau <= rho := by
    dsimp only [tau, rho]
    exact tau_le_canonicalBufferedRadius W hD.delta_pos hepsilon
  have hcardNat :
      Fintype.card {i // i ∈ U.fiber q.1} <= 1 := by
    simpa only [U, U0] using
      identityCore_canonicalBufferedTauActiveRestricted_fiber_card_le_one
        D hD S W hepsilon hepsilonHalf q.1
  have hcardOne :
      (Fintype.card {i // i ∈ U.fiber q.1} : ENNReal) <= 1 := by
    exact_mod_cast hcardNat
  have hratioOneNN : tau / rho <= 1 :=
    (div_le_one hrhoPos).2 htauRho
  have hscalePos : 0 < scale := by
    dsimp only [scale]
    exact div_pos (contractedJohnProxyRadius_pos htauPos hrhoPos) (by norm_num)
  have hfixedNN : (3 / 64 : NNReal) <= 1 := by
    rw [← NNReal.coe_le_coe]
    norm_num
  have hscaleOne : scale <= 1 := by
    calc
      scale = (3 / 64 : NNReal) * (tau / rho) := by
        dsimp only [scale]
        exact contractedJohnProxyRadius_div_eight_eq_fixed_mul_ratio hrhoPos
      _ <= 1 * (tau / rho) := mul_le_mul' hfixedNN le_rfl
      _ <= 1 * 1 := mul_le_mul' le_rfl hratioOneNN
      _ = 1 := by norm_num
  have hscalePower :
      (1 : ENNReal) <= (scale : ENNReal) ^ (-cardExp) := by
    by_cases hcardZero : cardExp = 0
    · simp only [hcardZero, neg_zero, ENNReal.rpow_zero, le_refl]
    · have hcardPos : 0 < cardExp :=
        lt_of_le_of_ne hcardExp (Ne.symm hcardZero)
      exact ENNReal.one_le_rpow_of_pos_of_le_one_of_neg
        (ENNReal.coe_pos.mpr hscalePos)
        (by exact_mod_cast hscaleOne) (by linarith)
  have hratioPos : 0 < ratio := by
    dsimp only [ratio]
    exact ENNReal.div_pos
      (ENNReal.coe_ne_zero.mpr htauPos.ne') ENNReal.coe_ne_top
  have hratioOne : ratio <= 1 := by
    dsimp only [ratio]
    apply (ENNReal.div_le_iff
      (ENNReal.coe_ne_zero.mpr hrhoPos.ne') ENNReal.coe_ne_top).2
    simpa using
      (show (tau : ENNReal) <= (rho : ENNReal) by exact_mod_cast htauRho)
  have hratioPower :
      (1 : ENNReal) <= ratio ^ (-(2 + kappa)) := by
    exact ENNReal.one_le_rpow_of_pos_of_le_one_of_neg
      hratioPos hratioOne (by linarith)
  constructor
  · simpa only [U, U0, scale, tau, rho] using hcardOne.trans hscalePower
  · simpa only [U, U0, tau, rho, ratio, one_mul] using
      hcardOne.trans hratioPower

variable {epsilon0 beta gamma : Real}

/-- Endpoint Frostman mass, transported to the exact active-restricted
shading consumed by the low-CF selector. -/
theorem endpointLongCore_identity_selected_sourceMassPower
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hepsilonHalf : P.epsilon <= 1 / 2)
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
    (delta : ENNReal) ^ (2 * etaSource) <=
      shadingMassOn Y U.activeFine := by
  dsimp only
  calc
    (delta : ENNReal) ^ (2 * etaSource) <= D.shading.shadingMass :=
      delta_rpow_two_eta_le_shadingMass_of_frostman D hD hF
    _ = shadingMassOn
        (activeFineRestrictedShading
          (canonicalBufferedTauActiveCover
            (fullRefinementDatum D)
            (fullRefinementDatum_isAdmissible hD)
            (identityRadiusCoherentCover (fullRefinementDatum D).family)
            (endpointScaleSequence delta
              (hD.delta_le_half.trans (by norm_num))) W
            P.epsilon_pos.le hepsilonHalf)
          (tauActiveCoarseDatum (fullRefinementDatum D)
            (identityRadiusCoherentCover (fullRefinementDatum D).family)
            (endpointScaleSequence delta
              (hD.delta_le_half.trans (by norm_num))) W).shading)
        (activeFineRestrictedScaleCover
          (canonicalBufferedTauActiveCover
            (fullRefinementDatum D)
            (fullRefinementDatum_isAdmissible hD)
            (identityRadiusCoherentCover (fullRefinementDatum D).family)
            (endpointScaleSequence delta
              (hD.delta_le_half.trans (by norm_num))) W
            P.epsilon_pos.le hepsilonHalf)).activeFine :=
      (endpointLongCore_canonicalBufferedTauActive_shadingMassOn_eq_source
        D hD P W hepsilonHalf).symm

#print axioms
  identityCore_canonicalBufferedTauActiveRestricted_dualPower
#print axioms endpointLongCore_identity_selected_sourceMassPower

end
end Family8EndpointIdentityNoKTSourceCardPowerV3
