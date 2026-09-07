import Family8Grounding.Family8AllFrostmanStickyPopularComponentPowerV2
import Family8Grounding.Family8StickyActiveCoarseKatzTaoCardScaleMassUpperV4
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8AllFrostmanStickyPopularParentPowerV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-!
# An actual Sticky Katz--Tao producer for the popular-parent power

V1--V3 were failed elaboration drafts and are deliberately not imported.
The actual scale-cover Katz--Tao bound gives
`rho ^ 2 * |activeCoarse| <= 1024 * A`.  An honest scale lower bound
`delta ^ s <= rho` therefore yields the sharp parent exponent
`katzTaoExponent + 2 * s + absorbExponent`.
-/

def stickyPopularParentPowerThreshold (absorbExponent : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold 1024 absorbExponent

theorem stickyPopularParentPowerThreshold_pos (absorbExponent : Real) :
    0 < stickyPopularParentPowerThreshold absorbExponent :=
  finiteConstantSmallDeltaThreshold_pos 1024 absorbExponent

theorem activeCoarse_card_le_delta_negativePower_of_katzTaoAtScale
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    {A : ENNReal} (hKT : S.IsKatzTaoAtScale A)
    {scaleExponent katzTaoExponent absorbExponent : Real}
    (habsorbExponent : 0 < absorbExponent)
    (hdeltaThreshold :
      delta <= stickyPopularParentPowerThreshold absorbExponent)
    (hscale :
      (delta : ENNReal) ^ scaleExponent <= (rho : ENNReal))
    (hA : A <= (delta : ENNReal) ^ (-katzTaoExponent)) :
    (Fintype.card {k // k ∈ S.activeCoarse} : ENNReal) <=
      (delta : ENNReal) ^
        (-(katzTaoExponent + 2 * scaleExponent + absorbExponent)) := by
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  have hdTop : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hconstant : (1024 : ENNReal) <=
      (delta : ENNReal) ^ (-absorbExponent) := by
    exact finiteConstant_le_delta_negativePower
      (K := (1024 : ENNReal)) (by norm_num) habsorbExponent hD.delta_pos
        (by simpa only [stickyPopularParentPowerThreshold] using
          hdeltaThreshold)
  have hscaleSq : ((delta : ENNReal) ^ scaleExponent) ^ 2 <=
      (rho : ENNReal) ^ 2 :=
    pow_le_pow_left' hscale 2
  have hcardScale :=
    Family8StickyActiveCoarseKatzTaoCardScaleMassUpperV4.StickyScaleCover.activeCoarseCardScaleMass_le_1024_mul_of_isKatzTaoAtScale
      D hD S hrhoHalf hKT
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
      (Fintype.card {k // k ∈ S.activeCoarse} : ENNReal) *
          ((delta : ENNReal) ^ scaleExponent) ^ 2 <=
        (delta : ENNReal) ^
          (-(katzTaoExponent + 2 * scaleExponent + absorbExponent)) *
          ((delta : ENNReal) ^ scaleExponent) ^ 2 := by
    calc
      (Fintype.card {k // k ∈ S.activeCoarse} : ENNReal) *
          ((delta : ENNReal) ^ scaleExponent) ^ 2 <=
          (S.activeCoarse.card : ENNReal) * (rho : ENNReal) ^ 2 := by
        simpa only [Fintype.card_coe] using
          (mul_le_mul' (le_refl
            (Fintype.card {k // k ∈ S.activeCoarse} : ENNReal)) hscaleSq)
      _ = (activeCoarseCardScaleMass S : ENNReal) := by
        simp only [activeCoarseCardScaleMass, ENNReal.coe_mul,
          ENNReal.coe_natCast, ENNReal.coe_pow]
      _ <= 1024 * A := hcardScale
      _ <= (delta : ENNReal) ^ (-absorbExponent) *
          (delta : ENNReal) ^ (-katzTaoExponent) :=
        mul_le_mul' hconstant hA
      _ = (delta : ENNReal) ^
          (-(katzTaoExponent + 2 * scaleExponent + absorbExponent)) *
          ((delta : ENNReal) ^ scaleExponent) ^ 2 :=
        hpowerIdentity.symm
  exact (ENNReal.mul_le_mul_iff_left
    (by positivity) (by finiteness)).mp hscaled

/-- The sharp estimate with the scale Katz--Tao certificate obtained directly
from an actual Sticky-at-every-scale object. -/
theorem activeCoarse_card_le_delta_negativePower_of_stickyAtEveryScale
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (cover : StickyMultiscaleCover D.family)
    {frostmanError katzTaoError : ENNReal}
    (hsticky : cover.IsStickyAtEveryScale frostmanError katzTaoError)
    (rho : NNReal) (hdeltaRho : delta <= rho) (hrhoOne : rho <= 1)
    (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    {scaleExponent katzTaoExponent absorbExponent : Real}
    (habsorbExponent : 0 < absorbExponent)
    (hdeltaThreshold :
      delta <= stickyPopularParentPowerThreshold absorbExponent)
    (hscale :
      (delta : ENNReal) ^ scaleExponent <= (rho : ENNReal))
    (hKatzTaoPower : katzTaoError <=
      (delta : ENNReal) ^ (-katzTaoExponent)) :
    (Fintype.card {k // k ∈
        (cover.cover rho hdeltaRho hrhoOne).activeCoarse} : ENNReal) <=
      (delta : ENNReal) ^
        (-(katzTaoExponent + 2 * scaleExponent + absorbExponent)) := by
  exact activeCoarse_card_le_delta_negativePower_of_katzTaoAtScale
    D hD (cover.cover rho hdeltaRho hrhoOne) hrhoHalf
      (hsticky.katzTao rho hdeltaRho hrhoOne) habsorbExponent
        hdeltaThreshold hscale hKatzTaoPower

#print axioms stickyPopularParentPowerThreshold_pos
#print axioms activeCoarse_card_le_delta_negativePower_of_katzTaoAtScale
#print axioms activeCoarse_card_le_delta_negativePower_of_stickyAtEveryScale

end

end Family8AllFrostmanStickyPopularParentPowerV4
