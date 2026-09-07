import Family8Grounding.Family8FrostmanUnionMultiplicityAlgebraV1
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

open scoped ENNReal NNReal

namespace Family8AllFrostmanBranchNumericsV1

open Family8KatzTaoFrostmanPropertiesV1
open Family8FrostmanUnionMultiplicityAlgebraV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Constant absorption in the all-Frostman branch

The paper writes `|T| <= delta^(-4)` and `|T| ~ delta^2` with suppressed
absolute constants.  This module keeps an arbitrary finite constant `C` in
the resulting bound `actualVolume <= C * delta^(-2)` and absorbs exactly
`C^(gamma/4)` into the allowed `delta^epsilon` loss below an explicit scale.
-/

/-- Explicit small-scale threshold for the all-Frostman volume constant. -/
def allFrostmanConstantThreshold
    (C : ENNReal) (epsilon gamma : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold (C ^ (gamma / 4)) epsilon

theorem allFrostmanConstantThreshold_pos
    (C : ENNReal) (epsilon gamma : Real) :
    0 < allFrostmanConstantThreshold C epsilon gamma :=
  finiteConstantSmallDeltaThreshold_pos _ _

theorem allFrostmanConstantThreshold_le_one
    (C : ENNReal) {epsilon gamma : Real} (hepsilon : 0 < epsilon) :
    allFrostmanConstantThreshold C epsilon gamma ≤ 1 :=
  finiteConstantSmallDeltaThreshold_le_one _ hepsilon

/-- Below the explicit threshold, the entire finite volume constant is paid
for by the positive `delta^epsilon` loss. -/
theorem delta_rpow_mul_constant_rpow_le_one
    {delta : NNReal} {C : ENNReal} {epsilon gamma : Real}
    (hdelta : 0 < delta)
    (hdeltaThreshold :
      delta ≤ allFrostmanConstantThreshold C epsilon gamma)
    (hCtop : C ≠ ∞) (hepsilon : 0 < epsilon) (hgamma : 0 ≤ gamma) :
    (delta : ENNReal) ^ epsilon * C ^ (gamma / 4) ≤ 1 := by
  have hquarter : 0 ≤ gamma / 4 := by linarith
  have hCpowTop : C ^ (gamma / 4) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hquarter hCtop
  have hconstant :
      C ^ (gamma / 4) ≤ (delta : ENNReal) ^ (-epsilon) := by
    exact finiteConstant_le_delta_negativePower hCpowTop hepsilon hdelta
      hdeltaThreshold
  have hd0 : (delta : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  calc
    (delta : ENNReal) ^ epsilon * C ^ (gamma / 4)
        ≤ (delta : ENNReal) ^ epsilon *
            (delta : ENNReal) ^ (-epsilon) :=
      mul_le_mul_right hconstant _
    _ = (delta : ENNReal) ^ (epsilon + (-epsilon)) := by
      rw [ENNReal.rpow_add epsilon (-epsilon) hd0 hdTop]
    _ = 1 := by simp

/-- The volume-factor comparison with an arbitrary finite multiplicative
constant retained. -/
theorem allFrostman_volumeFactor_le_with_constant
    {delta : NNReal} {actualVolume C : ENNReal} {gamma : Real}
    (hdelta : 0 < delta) (hgamma : 0 ≤ gamma)
    (hvolume :
      actualVolume ≤ C * (delta : ENNReal) ^ (-2 : Real)) :
    (delta : ENNReal) ^ gamma * actualVolume ^ (gamma / 4) ≤
      C ^ (gamma / 4) * (delta : ENNReal) ^ (gamma / 2) := by
  have hd0 : (delta : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hquarter : 0 ≤ gamma / 4 := by linarith
  calc
    (delta : ENNReal) ^ gamma * actualVolume ^ (gamma / 4)
        ≤ (delta : ENNReal) ^ gamma *
            (C * (delta : ENNReal) ^ (-2 : Real)) ^ (gamma / 4) := by
          exact mul_le_mul_right
            (ENNReal.rpow_le_rpow hvolume hquarter) _
    _ = (delta : ENNReal) ^ gamma *
          (C ^ (gamma / 4) *
            ((delta : ENNReal) ^ (-2 : Real)) ^ (gamma / 4)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hquarter]
    _ = C ^ (gamma / 4) *
          ((delta : ENNReal) ^ gamma *
            ((delta : ENNReal) ^ (-2 : Real)) ^ (gamma / 4)) := by
          ac_rfl
    _ = C ^ (gamma / 4) *
          ((delta : ENNReal) ^ gamma *
            (delta : ENNReal) ^ ((-2 : Real) * (gamma / 4))) := by
          rw [ENNReal.rpow_mul]
    _ = C ^ (gamma / 4) *
          (delta : ENNReal) ^
            (gamma + ((-2 : Real) * (gamma / 4))) := by
          rw [ENNReal.rpow_add gamma ((-2 : Real) * (gamma / 4)) hd0 hdTop]
    _ = C ^ (gamma / 4) *
          (delta : ENNReal) ^ (gamma / 2) := by
          congr 2
          ring_nf

/-- Exact all-Frostman exponent conversion with all absolute constants
absorbed at the displayed small-delta threshold. -/
theorem frostmanUnionLowerRHS_halfExponent_le_of_volume_constant
    {delta : NNReal} {actualVolume C : ENNReal}
    {epsilon gamma : Real}
    (hdelta : 0 < delta)
    (hdeltaThreshold :
      delta ≤ allFrostmanConstantThreshold C epsilon gamma)
    (hCtop : C ≠ ∞) (hepsilon : 0 < epsilon) (hgamma : 0 ≤ gamma)
    (hvolume :
      actualVolume ≤ C * (delta : ENNReal) ^ (-2 : Real)) :
    frostmanUnionLowerRHS delta actualVolume epsilon (gamma / 2) ≤
      (delta : ENNReal) ^ (gamma / 2) := by
  have habsorb := delta_rpow_mul_constant_rpow_le_one
    hdelta hdeltaThreshold hCtop hepsilon hgamma
  have hfactor := allFrostman_volumeFactor_le_with_constant
    hdelta hgamma hvolume
  unfold frostmanUnionLowerRHS
  have hrewrite :
      (delta : ENNReal) ^ (2 * (gamma / 2)) *
          actualVolume ^ ((gamma / 2) / 2) =
        (delta : ENNReal) ^ gamma * actualVolume ^ (gamma / 4) := by
    congr 1 <;> ring_nf
  rw [mul_assoc, hrewrite]
  calc
    (delta : ENNReal) ^ epsilon *
        ((delta : ENNReal) ^ gamma * actualVolume ^ (gamma / 4))
        ≤ (delta : ENNReal) ^ epsilon *
            (C ^ (gamma / 4) *
              (delta : ENNReal) ^ (gamma / 2)) :=
          mul_le_mul_right hfactor _
    _ = ((delta : ENNReal) ^ epsilon * C ^ (gamma / 4)) *
          (delta : ENNReal) ^ (gamma / 2) := by ac_rfl
    _ ≤ 1 * (delta : ENNReal) ^ (gamma / 2) :=
          mul_le_mul_left habsorb _
    _ = (delta : ENNReal) ^ (gamma / 2) := by simp

#print axioms delta_rpow_mul_constant_rpow_le_one
#print axioms allFrostman_volumeFactor_le_with_constant
#print axioms frostmanUnionLowerRHS_halfExponent_le_of_volume_constant

end

end Family8AllFrostmanBranchNumericsV1
