import Family8Grounding.Family8AllFrostmanStickyPopularParentPowerV4
import Family8Grounding.Family8ActiveCoarseCanonicalFrostmanXLowerV3
import Family8Grounding.Family8StickyActiveCoarseKatzTaoCardScaleMassUpperV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ActiveCoarseCanonicalFrostmanKatzTaoPowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8AllFrostmanStickyPopularParentPowerV4
open Family8KatzTaoFrostmanPropertiesV1
open Family8StickyParentHullVolumeBoundV1
open FamilyStickyAtEveryScaleCoreV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

namespace StickyScaleCover

theorem canonicalFrostmanConstant_mul_rho_sq_le_1024_mul_of_isKatzTaoAtScale
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (hrho : 0 < rho) (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (hcoarse : S.activeCoarse.Nonempty)
    {A : ENNReal} (hKT : S.IsKatzTaoAtScale A) :
    canonicalFrostmanConstant S.activeCoarseFamily closedBallFourBody *
        (rho : ENNReal) ^ 2 ≤
      1024 * A := by
  have hcontained : ∀ k,
      (S.activeCoarseFamily k : Set Space) ⊆
        (closedBallFourBody : Set Space) := by
    intro k
    simpa only [coe_closedBallFourBody] using
      Family8StickyParentHullVolumeBoundV1.activeCoarseFamily_body_subset_closedBall_four
        D hD S (hrhoHalf.trans (by norm_num)) k
  have hmass : containedMass S.activeCoarseFamily closedBallFourBody =
      familyVolume S.activeCoarseFamily :=
    containedMass_eq_familyVolume_of_contained
      S.activeCoarseFamily closedBallFourBody hcontained
  have hcard : (1 : ENNReal) ≤ S.activeCoarse.card := by
    exact_mod_cast Finset.one_le_card.mpr hcoarse
  have hden : (rho : ENNReal) ^ 2 / 2 ≤
      familyVolume S.activeCoarseFamily := by
    calc
      (rho : ENNReal) ^ 2 / 2 =
          1 * ((rho : ENNReal) ^ 2 / 2) := by rw [one_mul]
      _ ≤ (S.activeCoarse.card : ENNReal) *
          ((rho : ENNReal) ^ 2 / 2) := by gcongr
      _ ≤ familyVolume S.activeCoarseFamily :=
        Family8StickyActiveCoarseKatzTaoCardScaleMassUpperV4.StickyScaleCover.activeCoarse_card_mul_half_sq_le_familyVolume
          D S hrhoHalf
  have hmax : maximalConcentration S.activeCoarseFamily ≤ A :=
    (FamilyStickyAtEveryScaleCoreV1.StickyScaleCover.isKatzTaoAtScale_iff_maximalConcentration_le S A).mp hKT
  have hnum :
      maximalConcentration S.activeCoarseFamily *
          volume (closedBallFourBody : Set Space) ≤
        A * 512 := by
    exact mul_le_mul' hmax volume_closedBall_zero_four_le_512
  have hratio :
      canonicalFrostmanConstant S.activeCoarseFamily closedBallFourBody ≤
        (A * 512) / ((rho : ENNReal) ^ 2 / 2) := by
    unfold canonicalFrostmanConstant
    rw [hmass]
    exact ENNReal.div_le_div hnum hden
  calc
    canonicalFrostmanConstant S.activeCoarseFamily closedBallFourBody *
          (rho : ENNReal) ^ 2 ≤
        ((A * 512) / ((rho : ENNReal) ^ 2 / 2)) *
          (rho : ENNReal) ^ 2 := mul_le_mul' hratio le_rfl
    _ = (A * 512 * (rho : ENNReal) ^ 2) /
          ((rho : ENNReal) ^ 2 / 2) := by
      simp only [div_eq_mul_inv]
      ac_rfl
    _ ≤ 1024 * A := by
      have hrhoENN : 0 < (rho : ENNReal) := by exact_mod_cast hrho
      have hden0 : (rho : ENNReal) ^ 2 / 2 ≠ 0 :=
        ENNReal.div_ne_zero.mpr ⟨pow_ne_zero 2 hrhoENN.ne', by norm_num⟩
      have hdenTop : (rho : ENNReal) ^ 2 / 2 ≠ ∞ :=
        ENNReal.div_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) (by norm_num)
      apply (ENNReal.div_le_iff hden0 hdenTop).2
      have hhalf : ((rho : ENNReal) ^ 2 / 2) * 2 =
          (rho : ENNReal) ^ 2 := by
        rw [ENNReal.div_mul_cancel] <;> norm_num
      have hcross :
          A * 512 * (rho : ENNReal) ^ 2 =
            (1024 * A) * ((rho : ENNReal) ^ 2 / 2) := by
        calc
          A * 512 * (rho : ENNReal) ^ 2 =
              A * 512 * (((rho : ENNReal) ^ 2 / 2) * 2) := by rw [hhalf]
          _ = (1024 * A) * ((rho : ENNReal) ^ 2 / 2) := by ring
      exact hcross.le

theorem canonicalFrostmanConstant_le_delta_negativePower_of_isKatzTaoAtScale
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (hrho : 0 < rho) (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    (hcoarse : S.activeCoarse.Nonempty)
    {A : ENNReal} (hKT : S.IsKatzTaoAtScale A)
    {scaleExponent katzTaoExponent absorbExponent : Real}
    (habsorbExponent : 0 < absorbExponent)
    (hdeltaThreshold :
      delta ≤ stickyPopularParentPowerThreshold absorbExponent)
    (hscale : (delta : ENNReal) ^ scaleExponent ≤ (rho : ENNReal))
    (hA : A ≤ (delta : ENNReal) ^ (-katzTaoExponent)) :
    canonicalFrostmanConstant S.activeCoarseFamily closedBallFourBody ≤
      (delta : ENNReal) ^
        (-(katzTaoExponent + 2 * scaleExponent + absorbExponent)) := by
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  have hdTop : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hconstant : (1024 : ENNReal) ≤
      (delta : ENNReal) ^ (-absorbExponent) := by
    exact finiteConstant_le_delta_negativePower
      (K := (1024 : ENNReal)) (by norm_num) habsorbExponent hD.delta_pos
        (by simpa only [stickyPopularParentPowerThreshold] using
          hdeltaThreshold)
  have hscaleSq : ((delta : ENNReal) ^ scaleExponent) ^ 2 ≤
      (rho : ENNReal) ^ 2 := pow_le_pow_left' hscale 2
  have hCFScale :=
    canonicalFrostmanConstant_mul_rho_sq_le_1024_mul_of_isKatzTaoAtScale
      D hD S hrho hrhoHalf hcoarse hKT
  have hpowerIdentity :
      (delta : ENNReal) ^
          (-(katzTaoExponent + 2 * scaleExponent + absorbExponent)) *
          ((delta : ENNReal) ^ scaleExponent) ^ 2 =
        (delta : ENNReal) ^ (-absorbExponent) *
          (delta : ENNReal) ^ (-katzTaoExponent) := by
    rw [← ENNReal.rpow_natCast
        ((delta : ENNReal) ^ scaleExponent) 2,
      ← ENNReal.rpow_mul,
      ← ENNReal.rpow_add _ _ hd0 hdTop,
      ← ENNReal.rpow_add _ _ hd0 hdTop]
    congr 1
    ring
  have hscaled :
      canonicalFrostmanConstant S.activeCoarseFamily closedBallFourBody *
          ((delta : ENNReal) ^ scaleExponent) ^ 2 ≤
        (delta : ENNReal) ^
          (-(katzTaoExponent + 2 * scaleExponent + absorbExponent)) *
          ((delta : ENNReal) ^ scaleExponent) ^ 2 := by
    calc
      canonicalFrostmanConstant S.activeCoarseFamily closedBallFourBody *
          ((delta : ENNReal) ^ scaleExponent) ^ 2 ≤
        canonicalFrostmanConstant S.activeCoarseFamily closedBallFourBody *
          (rho : ENNReal) ^ 2 := mul_le_mul' le_rfl hscaleSq
      _ ≤ 1024 * A := hCFScale
      _ ≤ (delta : ENNReal) ^ (-absorbExponent) *
          (delta : ENNReal) ^ (-katzTaoExponent) :=
        mul_le_mul' hconstant hA
      _ = (delta : ENNReal) ^
          (-(katzTaoExponent + 2 * scaleExponent + absorbExponent)) *
          ((delta : ENNReal) ^ scaleExponent) ^ 2 :=
        hpowerIdentity.symm
  exact (ENNReal.mul_le_mul_iff_left
    (by positivity) (by finiteness)).mp hscaled

#print axioms canonicalFrostmanConstant_mul_rho_sq_le_1024_mul_of_isKatzTaoAtScale
#print axioms canonicalFrostmanConstant_le_delta_negativePower_of_isKatzTaoAtScale

end StickyScaleCover
end
end Family8ActiveCoarseCanonicalFrostmanKatzTaoPowerV1
