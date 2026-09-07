import Family8Grounding.Family8CanonicalSourceKatzTaoNNRealV1
import Family8Grounding.Family8ActualFamilyVolumePackingV1
import Family8Grounding.Family8AllFrostmanStickyUnionProducerV1
import Family8Grounding.Family8EndpointLongCoreIdentityFirstFieldsV3
import Family8Grounding.Family8FullRefinementActualDatumV1
import Family8Grounding.Family8IdentityCoreSourceKatzTaoBootstrapV1
import Family8Grounding.Family8IdentityCoreCanonicalBufferedLossOneAdapterV1
import Family8Grounding.Family8IdentityRadiusKatzTaoPowerEnvelopeV1
import Mathlib.Tactic

/-!
# Endpoint identity long-core source Katz--Tao budget

On the one-step endpoint sequence the selected lower scale is `delta` and the
canonical buffered radius is exactly `delta^(1-epsilon)`.  Hence the apparent
identity-cover enlargement costs only `delta^(-2 epsilon)`, not two full
powers of `delta`.  The `4 epsilon + etaPrime` long-interval loss can absorb
this cost, the source Katz--Tao exponent, and the two fixed constants whenever
`etaKT <= epsilon + etaPrime`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8EndpointIdentityLongCoreSourceKatzTaoBudgetV1

open Submission.Kakeya.Uniformity
open Family8ActualFamilyVolumePackingV1
open Family8AllFrostmanStickyUnionProducerV1
open Family8CanonicalLowerBufferedScaleV4
open Family8CanonicalSourceKatzTaoNNRealV1
open Family8EndpointLongCoreIdentityFirstFieldsV3
open Family8FullRefinementActualDatumV1
open Family8IdentityCoreCanonicalBufferedLossOneAdapterV1
open Family8IdentityCoreSourceKatzTaoBootstrapV1
open Family8IdentityRadiusKatzTaoPowerEnvelopeV1
open Family8IdentityRadiusSourceKatzTaoTransportV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LongIntervalBootstrapNumericsV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8NormalizedLongIntervalCoreConsumerV1.NormalizedLongIntervalCoreWitness
open Family8ParameterLadderV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  {epsilon0 beta gamma etaKT etaPrime : Real}

/-- Spend half an epsilon on each of the two fixed coefficients `16` and
`1024`. -/
def endpointIdentityLongCoreSourceKatzTaoBudgetThreshold
    (P : ParameterLadder epsilon0 beta gamma) : NNReal :=
  min (identityRadiusKatzTaoPowerThreshold (P.epsilon / 2))
    (finiteConstantSmallDeltaThreshold 1024 (P.epsilon / 2))

theorem endpointIdentityLongCoreSourceKatzTaoBudgetThreshold_pos
    (P : ParameterLadder epsilon0 beta gamma) :
    0 < endpointIdentityLongCoreSourceKatzTaoBudgetThreshold P := by
  rw [endpointIdentityLongCoreSourceKatzTaoBudgetThreshold, lt_min_iff]
  exact ⟨identityRadiusKatzTaoPowerThreshold_pos _,
    finiteConstantSmallDeltaThreshold_pos _ _⟩

/-- The endpoint formula for the canonical buffered radius is exact. -/
theorem endpointLongCore_canonicalBufferedRadius_eq_delta_rpow_one_sub
    (hdeltaOne : delta <= 1)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      fine (identityRadiusCoherentCover fine)
      P.N P.epsilon P.eta (endpointScaleSequence delta hdeltaOne)) :
    canonicalBufferedRadius W = delta ^ (1 - P.epsilon) := by
  unfold canonicalBufferedRadius canonicalLowerBufferedScale
  rw [show W.m = (0 : Fin 1) from Subsingleton.elim _ _,
    endpointScaleSequence_tau_zero, endpointScaleSequence_theta_zero]
  simp

/-- Consequently the endpoint radius enlargement costs exactly the small
relative exponent epsilon. -/
theorem endpointLongCore_canonicalBufferedRadius_div_delta_le_negativePower
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      fine (identityRadiusCoherentCover fine)
      P.N P.epsilon P.eta (endpointScaleSequence delta hdeltaOne)) :
    canonicalBufferedRadius W / delta <= delta ^ (-P.epsilon) := by
  rw [endpointLongCore_canonicalBufferedRadius_eq_delta_rpow_one_sub
    hdeltaOne P W]
  apply (div_le_iff₀ hdelta).2
  rw [show delta ^ (1 - P.epsilon) =
      delta ^ (-P.epsilon) * delta by
    calc
      delta ^ (1 - P.epsilon) =
          delta ^ (-P.epsilon + 1) := by congr 1; ring
      _ = delta ^ (-P.epsilon) * delta ^ (1 : Real) :=
        NNReal.rpow_add hdelta.ne' (-P.epsilon) 1
      _ = delta ^ (-P.epsilon) * delta := by rw [NNReal.rpow_one]]

/-- ENNReal form of the exact square-volume ratio needed by the identity
Katz--Tao transport. -/
theorem endpointLongCore_canonicalBufferedRadius_scaleRatio
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      fine (identityRadiusCoherentCover fine)
      P.N P.epsilon P.eta (endpointScaleSequence delta hdeltaOne)) :
    (canonicalBufferedRadius W : ENNReal) ^ 2 /
        ((delta : ENNReal) ^ 2 / 2) <=
      2 * (delta : ENNReal) ^ (-2 * P.epsilon) := by
  have hratio :=
    endpointLongCore_canonicalBufferedRadius_div_delta_le_negativePower
      hdelta hdeltaOne P W
  have hratioSq :
      (canonicalBufferedRadius W / delta) ^ 2 <=
        (delta ^ (-P.epsilon)) ^ 2 :=
    pow_le_pow_left' hratio 2
  have hNN :
      canonicalBufferedRadius W ^ 2 / (delta ^ 2 / 2) <=
        2 * delta ^ (-2 * P.epsilon) := by
    rw [show canonicalBufferedRadius W ^ 2 / (delta ^ 2 / 2) =
        2 * (canonicalBufferedRadius W / delta) ^ 2 by
      field_simp [hdelta.ne']]
    calc
      2 * (canonicalBufferedRadius W / delta) ^ 2 <=
          2 * (delta ^ (-P.epsilon)) ^ 2 := by gcongr
      _ = 2 * delta ^ (-2 * P.epsilon) := by
        rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]
        congr 2
        ring
  have hcast := ENNReal.coe_le_coe.mpr hNN
  simpa only [
    ENNReal.coe_div (by positivity : delta ^ 2 / 2 ≠ 0),
    ENNReal.coe_div (by norm_num : (2 : NNReal) ≠ 0),
    ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_ofNat,
    ENNReal.coe_rpow_of_ne_zero hdelta.ne'] using hcast

/-- The full hAKT scalar premise for the endpoint identity core.  The only
non-geometric input is the transparent exponent condition
etaKT <= epsilon + etaPrime. -/
theorem endpointIdentityLongCore_sourceKatzTao_hAKT
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      fine (identityRadiusCoherentCover fine)
      P.N P.epsilon P.eta (endpointScaleSequence delta hdeltaOne))
    (hetaKT : etaKT <= P.epsilon + etaPrime)
    (hsmall : delta <=
      endpointIdentityLongCoreSourceKatzTaoBudgetThreshold P) :
    1024 *
        (identityRadiusKatzTaoVolumeRatioNNReal delta
          (canonicalBufferedRadius W) *
          canonicalSourceKatzTaoNNReal delta etaKT) <=
      (endpointScaleSequence delta hdeltaOne).tau W.m ^
        (-longIntervalDeltaLoss P.epsilon etaPrime) := by
  have hsmallRatio : delta <=
      identityRadiusKatzTaoPowerThreshold (P.epsilon / 2) :=
    hsmall.trans (min_le_left _ _)
  have hsmall1024 : delta <=
      finiteConstantSmallDeltaThreshold 1024 (P.epsilon / 2) :=
    hsmall.trans (min_le_right _ _)
  have hratioSource :=
    identityRadiusKatzTaoVolumeRatio_mul_sourcePower_le_delta_negativePower
      (etaKT := etaKT) (scaleLoss := P.epsilon)
      (absorbExponent := P.epsilon / 2)
      hdelta
      (endpointLongCore_canonicalBufferedRadius_scaleRatio
        hdelta hdeltaOne P W)
      (by linarith [P.epsilon_pos] : 0 < P.epsilon / 2) hsmallRatio
  have h1024 : (1024 : ENNReal) <=
      (delta : ENNReal) ^ (-(P.epsilon / 2)) :=
    finiteConstant_le_delta_negativePower (by norm_num)
      (by linarith [P.epsilon_pos] : 0 < P.epsilon / 2) hdelta hsmall1024
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hcombined :
      (1024 : ENNReal) *
          (identityRadiusKatzTaoVolumeRatio delta
            (canonicalBufferedRadius W) *
            (delta : ENNReal) ^ (-etaKT)) <=
        (delta : ENNReal) ^ (-(etaKT + 3 * P.epsilon)) := by
    calc
      (1024 : ENNReal) *
          (identityRadiusKatzTaoVolumeRatio delta
            (canonicalBufferedRadius W) *
            (delta : ENNReal) ^ (-etaKT)) <=
        (delta : ENNReal) ^ (-(P.epsilon / 2)) *
          (delta : ENNReal) ^
            (-(etaKT + 2 * P.epsilon + P.epsilon / 2)) :=
        mul_le_mul' h1024 hratioSource
      _ = (delta : ENNReal) ^ (-(etaKT + 3 * P.epsilon)) := by
        rw [← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
        congr 1
        ring
  have hdOne : (delta : ENNReal) <= 1 := by exact_mod_cast hdeltaOne
  have hexponent :
      -longIntervalDeltaLoss P.epsilon etaPrime <=
        -(etaKT + 3 * P.epsilon) := by
    unfold longIntervalDeltaLoss
    linarith
  have hENN :
      (1024 : ENNReal) *
          (identityRadiusKatzTaoVolumeRatio delta
            (canonicalBufferedRadius W) *
            (delta : ENNReal) ^ (-etaKT)) <=
        (delta : ENNReal) ^
          (-longIntervalDeltaLoss P.epsilon etaPrime) :=
    hcombined.trans
      (ENNReal.rpow_le_rpow_of_exponent_ge hdOne hexponent)
  rw [show W.m = (0 : Fin 1) from Subsingleton.elim _ _,
    endpointScaleSequence_tau_zero]
  apply ENNReal.coe_le_coe.mp
  simpa only [ENNReal.coe_mul, ENNReal.coe_ofNat,
    coe_identityRadiusKatzTaoVolumeRatioNNReal delta
      (canonicalBufferedRadius W) hdelta,
    coe_canonicalSourceKatzTaoNNReal hdelta etaKT,
    ENNReal.coe_rpow_of_ne_zero hdelta.ne'] using hENN

/-- One positive power absorbs the sole factor eight in the direct source
volume-to-card-scale lower bound. -/
def endpointIdentityLongCoreDirectXLowerThreshold
    (absorbExponent : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold 8 absorbExponent

theorem endpointIdentityLongCoreDirectXLowerThreshold_pos
    (absorbExponent : Real) :
    0 < endpointIdentityLongCoreDirectXLowerThreshold absorbExponent :=
  finiteConstantSmallDeltaThreshold_pos _ _

/-- On the full-refinement identity cover, the source Frostman mass directly
forces the long-bootstrap lower bound on X.  This bypasses the canonical
Frostman-constant premise entirely. -/
theorem endpointIdentityLongCore_directXLower_of_frostman
    (D : Family8KatzTaoFrostmanPropertiesV1.ActualTubeDatum delta index)
    (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (hepsilonHalf : P.epsilon <= 1 / 2)
    {etaF absorbExponent targetExponent : Real}
    (hF : FrostmanHypotheses D etaF)
    (habsorb : 0 < absorbExponent)
    (hexponent : 2 * etaF + absorbExponent <= targetExponent)
    (hsmall : delta <=
      endpointIdentityLongCoreDirectXLowerThreshold absorbExponent) :
    delta ^ targetExponent <=
      activeCoarseCardScaleMass
        (canonicalBufferedGlobalCover W hD.delta_pos
          P.epsilon_pos.le hepsilonHalf) := by
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let U := canonicalBufferedGlobalCover W hD.delta_pos
    P.epsilon_pos.le hepsilonHalf
  let b := canonicalBufferedRadius W
  have hactiveCard : U.activeCoarse.card = Fintype.card index := by
    dsimp only [U]
    have hU :=
      identityCore_canonicalBufferedGlobalCover_eq_identityRadiusScaleCover
        E hE S P W hepsilonHalf
    rw [hU]
    simp only [identityRadiusScaleCover, E, fullRefinementDatum_refined,
      Finset.card_map, Finset.card_univ]
  have hdeltaB : delta <= b := by
    dsimp only [b, S]
    exact
      ((endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))).delta_le_tau W.m).trans
        (tau_le_canonicalBufferedRadius W hD.delta_pos P.epsilon_pos.le)
  have hmass :
      (delta : ENNReal) ^ (2 * etaF) <= D.shading.shadingMass :=
    delta_rpow_two_eta_le_shadingMass_of_frostman D hD hF
  have hvolume :
      D.actualFamilyVolume <=
        (Fintype.card index : ENNReal) * (8 * (delta : ENNReal) ^ 2) :=
    actualFamilyVolume_le_card_mul_eight_sq D hD.delta_le_half
  have hfloorX :
      (delta : ENNReal) ^ (2 * etaF) <=
        8 * (activeCoarseCardScaleMass U : ENNReal) := by
    calc
      (delta : ENNReal) ^ (2 * etaF) <= D.shading.shadingMass := hmass
      _ <= D.actualFamilyVolume := D.shading.shadingMass_le_familyVolume
      _ <= (Fintype.card index : ENNReal) *
          (8 * (delta : ENNReal) ^ 2) := hvolume
      _ <= (Fintype.card index : ENNReal) *
          (8 * (b : ENNReal) ^ 2) := by
        gcongr
      _ = 8 * (activeCoarseCardScaleMass U : ENNReal) := by
        simp only [activeCoarseCardScaleMass, ENNReal.coe_mul,
          ENNReal.coe_natCast, ENNReal.coe_pow, hactiveCard, b]
        ring
  have hconstant : (8 : ENNReal) <=
      (delta : ENNReal) ^ (-absorbExponent) :=
    finiteConstant_le_delta_negativePower (by norm_num) habsorb hD.delta_pos
      (by simpa only [endpointIdentityLongCoreDirectXLowerThreshold] using hsmall)
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  have habsorbed :
      (delta : ENNReal) ^ absorbExponent * 8 <= 1 := by
    calc
      (delta : ENNReal) ^ absorbExponent * 8 <=
          (delta : ENNReal) ^ absorbExponent *
            (delta : ENNReal) ^ (-absorbExponent) :=
        by gcongr
      _ = (delta : ENNReal) ^
          (absorbExponent + (-absorbExponent)) := by
        rw [ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
      _ = 1 := by simp
  have hdOne : (delta : ENNReal) <= 1 := by
    exact_mod_cast hD.delta_le_half.trans (by norm_num)
  have hENN :
      (delta : ENNReal) ^ targetExponent <=
        (activeCoarseCardScaleMass U : ENNReal) := by
    calc
      (delta : ENNReal) ^ targetExponent <=
          (delta : ENNReal) ^ (2 * etaF + absorbExponent) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hdOne hexponent
      _ = (delta : ENNReal) ^ absorbExponent *
          (delta : ENNReal) ^ (2 * etaF) := by
        rw [ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
        ac_rfl
      _ <= (delta : ENNReal) ^ absorbExponent *
          (8 * (activeCoarseCardScaleMass U : ENNReal)) :=
        by gcongr
      _ = ((delta : ENNReal) ^ absorbExponent * 8) *
          (activeCoarseCardScaleMass U : ENNReal) := by ac_rfl
      _ <= 1 * (activeCoarseCardScaleMass U : ENNReal) :=
        by gcongr
      _ = (activeCoarseCardScaleMass U : ENNReal) := one_mul _
  apply ENNReal.coe_le_coe.mp
  rw [ENNReal.coe_rpow_of_ne_zero hD.delta_pos.ne']
  exact hENN

#print axioms endpointLongCore_canonicalBufferedRadius_eq_delta_rpow_one_sub
#print axioms
  endpointLongCore_canonicalBufferedRadius_div_delta_le_negativePower
#print axioms endpointLongCore_canonicalBufferedRadius_scaleRatio
#print axioms endpointIdentityLongCore_sourceKatzTao_hAKT
#print axioms endpointIdentityLongCoreDirectXLowerThreshold_pos
#print axioms endpointIdentityLongCore_directXLower_of_frostman

end
end Family8EndpointIdentityLongCoreSourceKatzTaoBudgetV1
