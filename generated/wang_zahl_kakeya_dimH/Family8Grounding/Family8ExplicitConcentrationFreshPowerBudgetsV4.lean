import Family8Grounding.Family8ScaleContainedB2FreshKatzTaoEndpointV1
import Family8Grounding.Family8B2NormalizedConflictKatzTaoCapV6
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8ExplicitConcentrationFreshPowerBudgetsV4

open Family8ScaleContainedB2FreshKatzTaoEndpointV1
open Family8B2NormalizedConflictKatzTaoCapV6
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

/-!
# Pure-power budgets for sampled fresh Katz--Tao

This closes the two literal scalar premises left by zero-colour sampling and
fresh selection.  V1--V3 are failed mechanical drafts and are intentionally
not imported.
-/

def explicitConcentrationFreshDensityConstant : ENNReal :=
  128 * (480000 * 128 + 2) * 32

theorem sourceKatzTaoFreshLoss_coe_le_fixed_mul
    {C : ENNReal} (hCfinite : C ≠ ∞) (hCone : 1 ≤ C) :
    (sourceKatzTaoFreshLoss C : ENNReal) ≤
      (480000 * 128 + 2) * C := by
  have hscaledFinite : (128 : ENNReal) * C ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) hCfinite
  have hclosed :
      ((Nat.ceil ((480000 * (128 * C) : ENNReal).toReal) + 1 : Nat) :
          ENNReal) ≤ 480000 * (128 * C) + 2 :=
    fixedKatzTaoClosedLoss_coe_le_add_two hscaledFinite
  have htwo : (2 : ENNReal) ≤ 2 * C := by
    simpa only [mul_one] using
      (mul_le_mul' (show (2 : ENNReal) ≤ 2 from le_rfl) hCone)
  change
    ((Nat.ceil ((480000 * (128 * C) : ENNReal).toReal) + 1 : Nat) :
        ENNReal) ≤ (480000 * 128 + 2) * C
  calc
    _ ≤ 480000 * (128 * C) + 2 := hclosed
    _ ≤ 480000 * (128 * C) + 2 * C := add_le_add le_rfl htwo
    _ = (480000 * 128 + 2) * C := by ring

def explicitConcentrationFreshDensityThreshold (absorbEta : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold
    explicitConcentrationFreshDensityConstant absorbEta

theorem explicitConcentrationFreshDensityThreshold_pos
    (absorbEta : Real) :
    0 < explicitConcentrationFreshDensityThreshold absorbEta :=
  finiteConstantSmallDeltaThreshold_pos _ _

theorem explicitConcentrationFreshDensityConstant_ne_top :
    explicitConcentrationFreshDensityConstant ≠ ∞ := by
  norm_num [explicitConcentrationFreshDensityConstant]

theorem explicitConcentration_fresh_density_power_budget
    {delta : NNReal} {Csample tail : ENNReal}
    {targetEta sampleEta sourceEta absorbEta : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (htargetEta : 0 ≤ targetEta)
    (hCfinite : Csample ≠ ∞) (hCone : 1 ≤ Csample)
    (htail : tail ≤ Csample)
    (hCpower : Csample ≤ (delta : ENNReal) ^ (-sampleEta))
    (habsorbEta : 0 < absorbEta)
    (hsmall : delta ≤
      explicitConcentrationFreshDensityThreshold absorbEta)
    (hbudget : 2 * sampleEta + sourceEta + absorbEta ≤ targetEta) :
    ((((delta / 8 : NNReal) : ENNReal) ^ targetEta) *
          (128 * (sourceKatzTaoFreshLoss Csample : ENNReal))) *
        (32 * tail) ≤ (delta : ENNReal) ^ sourceEta := by
  let d : ENNReal := (delta : ENNReal)
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hdOne : d ≤ 1 := by
    dsimp only [d]
    exact_mod_cast hdeltaOne
  have hscale : (((delta / 8 : NNReal) : ENNReal)) ≤ d := by
    dsimp only [d]
    exact_mod_cast
      (div_le_self (show 0 ≤ delta from bot_le)
        (by norm_num : (1 : NNReal) ≤ 8))
  have hscalePower :
      (((delta / 8 : NNReal) : ENNReal) ^ targetEta) ≤ d ^ targetEta :=
    ENNReal.rpow_le_rpow hscale htargetEta
  have hloss := sourceKatzTaoFreshLoss_coe_le_fixed_mul hCfinite hCone
  have hCtwo : Csample * Csample ≤ d ^ (-(2 * sampleEta)) := by
    calc
      Csample * Csample ≤ d ^ (-sampleEta) * d ^ (-sampleEta) :=
        mul_le_mul' hCpower hCpower
      _ = d ^ ((-sampleEta) + (-sampleEta)) := by
        rw [ENNReal.rpow_add _ _ hd0 hdTop]
      _ = d ^ (-(2 * sampleEta)) := by
        congr 1
        ring
  have hscaleSample :
      d ^ targetEta * (Csample * Csample) ≤
        d ^ (targetEta - 2 * sampleEta) := by
    calc
      d ^ targetEta * (Csample * Csample) ≤
          d ^ targetEta * d ^ (-(2 * sampleEta)) :=
        mul_le_mul' le_rfl hCtwo
      _ = d ^ (targetEta + (-(2 * sampleEta))) := by
        rw [ENNReal.rpow_add _ _ hd0 hdTop]
      _ = d ^ (targetEta - 2 * sampleEta) := by rfl
  have hconstant : explicitConcentrationFreshDensityConstant ≤
      d ^ (-absorbEta) := by
    exact finiteConstant_le_delta_negativePower
      explicitConcentrationFreshDensityConstant_ne_top habsorbEta hdelta
        (by simpa [explicitConcentrationFreshDensityThreshold] using hsmall)
  have hfinalPower :
      d ^ (targetEta - 2 * sampleEta - absorbEta) ≤
        d ^ sourceEta := by
    exact ENNReal.rpow_le_rpow_of_exponent_ge hdOne (by linarith)
  calc
    ((((delta / 8 : NNReal) : ENNReal) ^ targetEta) *
          (128 * (sourceKatzTaoFreshLoss Csample : ENNReal))) *
        (32 * tail) ≤
      (d ^ targetEta * (128 * ((480000 * 128 + 2) * Csample))) *
        (32 * Csample) := by gcongr
    _ = explicitConcentrationFreshDensityConstant *
        (d ^ targetEta * (Csample * Csample)) := by
      unfold explicitConcentrationFreshDensityConstant
      ring
    _ ≤ explicitConcentrationFreshDensityConstant *
        d ^ (targetEta - 2 * sampleEta) :=
      mul_le_mul' le_rfl hscaleSample
    _ ≤ d ^ (-absorbEta) *
        d ^ (targetEta - 2 * sampleEta) :=
      mul_le_mul' hconstant le_rfl
    _ = d ^ ((-absorbEta) + (targetEta - 2 * sampleEta)) := by
      rw [ENNReal.rpow_add _ _ hd0 hdTop]
    _ = d ^ (targetEta - 2 * sampleEta - absorbEta) := by
      congr 1
      ring
    _ ≤ d ^ sourceEta := hfinalPower

def explicitConcentrationFreshCoefficientThreshold
    (absorbEta : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold 128 absorbEta

theorem explicitConcentrationFreshCoefficientThreshold_pos
    (absorbEta : Real) :
    0 < explicitConcentrationFreshCoefficientThreshold absorbEta :=
  finiteConstantSmallDeltaThreshold_pos _ _

theorem explicitConcentration_fresh_coefficient_power_budget
    {delta : NNReal} {Csample : ENNReal}
    {targetEta sampleEta absorbEta : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (htargetEta : 0 ≤ targetEta)
    (hCpower : Csample ≤ (delta : ENNReal) ^ (-sampleEta))
    (habsorbEta : 0 < absorbEta)
    (hsmall : delta ≤
      explicitConcentrationFreshCoefficientThreshold absorbEta)
    (hbudget : sampleEta + absorbEta ≤ targetEta) :
    128 * Csample ≤
      ((delta / 8 : NNReal) : ENNReal) ^ (-targetEta) := by
  let d : ENNReal := (delta : ENNReal)
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hdOne : d ≤ 1 := by
    dsimp only [d]
    exact_mod_cast hdeltaOne
  have hconstant : (128 : ENNReal) ≤ d ^ (-absorbEta) := by
    exact finiteConstant_le_delta_negativePower (by norm_num) habsorbEta
      hdelta (by simpa [explicitConcentrationFreshCoefficientThreshold]
        using hsmall)
  have hproduct :
      128 * Csample ≤ d ^ (-(absorbEta + sampleEta)) := by
    calc
      128 * Csample ≤ d ^ (-absorbEta) * d ^ (-sampleEta) :=
        mul_le_mul' hconstant hCpower
      _ = d ^ ((-absorbEta) + (-sampleEta)) := by
        rw [ENNReal.rpow_add _ _ hd0 hdTop]
      _ = d ^ (-(absorbEta + sampleEta)) := by
        congr 1
        ring
  have htarget :
      d ^ (-(absorbEta + sampleEta)) ≤ d ^ (-targetEta) :=
    ENNReal.rpow_le_rpow_of_exponent_ge hdOne (by linarith)
  have hdeltaEightPos : 0 < delta / 8 := div_pos hdelta (by norm_num)
  have hscalePowerNN :
      delta ^ (-targetEta) ≤ (delta / 8) ^ (-targetEta) := by
    exact NNReal.rpow_le_rpow_of_nonpos hdeltaEightPos
      (div_le_self (show 0 ≤ delta from bot_le)
        (by norm_num : (1 : NNReal) ≤ 8))
      (neg_nonpos.mpr htargetEta)
  have hscalePower :
      d ^ (-targetEta) ≤
        ((delta / 8 : NNReal) : ENNReal) ^ (-targetEta) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hdelta.ne' (-targetEta),
      ← ENNReal.coe_rpow_of_ne_zero hdeltaEightPos.ne' (-targetEta)]
    exact ENNReal.coe_le_coe.mpr hscalePowerNN
  exact hproduct.trans (htarget.trans hscalePower)

#print axioms sourceKatzTaoFreshLoss_coe_le_fixed_mul
#print axioms explicitConcentrationFreshDensityThreshold_pos
#print axioms explicitConcentrationFreshDensityConstant_ne_top
#print axioms explicitConcentration_fresh_density_power_budget
#print axioms explicitConcentrationFreshCoefficientThreshold_pos
#print axioms explicitConcentration_fresh_coefficient_power_budget

end
end Family8ExplicitConcentrationFreshPowerBudgetsV4
