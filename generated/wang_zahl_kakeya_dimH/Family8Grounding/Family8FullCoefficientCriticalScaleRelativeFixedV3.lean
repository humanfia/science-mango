import Family8Grounding.Family8FullCoefficientCriticalScaleRatioV2
import Mathlib.Tactic

/-!
# Relative-fixed form of the full-coefficient proxy scale

For the endpoint three-scale decomposition the middle scale remains the
literal buffered radius `coarse`.  The critical normalization radius
`2 * fine / t` must therefore be written as

`(2 * coarse / t) * (fine / coarse)`.

This small algebraic connector prevents the dimensionless coefficient scale
`t` from being substituted for the physical DSO middle scale.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8FullCoefficientCriticalScaleRelativeFixedV3

open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8FullCoefficientCriticalScaleRatioV2
open Family8WeightedCanonicalCriticalScalePositiveV1

noncomputable section

universe u

/-- The coefficient multiplying the literal fine-to-buffered ratio after
full-coefficient critical normalization. -/
def fullCoefficientRelativeFixed
    (coarse : NNReal) {iota : Type u}
    (W : WeightedCanonicalNormBallData iota) : ENNReal :=
  2 * ((coarse : ENNReal) /
    (weightedCanonicalCriticalScaleNNReal W : ENNReal))

theorem fullCoefficientRelativeFixed_ne_top
    {coarse : NNReal} (_hcoarse : 0 < coarse)
    {iota : Type u} (W : WeightedCanonicalNormBallData iota) :
    fullCoefficientRelativeFixed coarse W ≠ ∞ := by
  unfold fullCoefficientRelativeFixed
  apply ENNReal.mul_ne_top
  · norm_num
  · exact ENNReal.div_ne_top ENNReal.coe_ne_top
      (ENNReal.coe_ne_zero.mpr
        (weightedCanonicalCriticalScaleNNReal_pos W).ne')

theorem fullCoefficientRelativeFixed_pos
    {coarse : NNReal} (hcoarse : 0 < coarse)
    {iota : Type u} (W : WeightedCanonicalNormBallData iota) :
    0 < fullCoefficientRelativeFixed coarse W := by
  unfold fullCoefficientRelativeFixed
  exact ENNReal.mul_pos (by norm_num)
    (ENNReal.div_ne_zero.mpr
      ⟨ENNReal.coe_ne_zero.mpr hcoarse.ne', ENNReal.coe_ne_top⟩)

/-- Exact scale identity used by the arbitrary-fixed relative Frostman
envelope while retaining `coarse` as the DSO middle scale. -/
theorem coe_criticalScaleProxyRadius_eq_relativeFixed_mul_ratio
    (fine coarse : NNReal) (hcoarse : 0 < coarse)
    {iota : Type u} (W : WeightedCanonicalNormBallData iota) :
    (criticalScaleProxyRadius fine W.criticalScale
        (weightedCanonicalCriticalScale_pos W) : ENNReal) =
      fullCoefficientRelativeFixed coarse W *
        ((fine : ENNReal) / (coarse : ENNReal)) := by
  rw [coe_criticalScaleProxyRadius_eq_two_mul_ratio]
  unfold fullCoefficientRelativeFixed
  let f : ENNReal := fine
  let c : ENNReal := coarse
  let t : ENNReal := weightedCanonicalCriticalScaleNNReal W
  have hc0 : c ≠ 0 := by
    dsimp only [c]
    exact ENNReal.coe_ne_zero.mpr hcoarse.ne'
  have hcTop : c ≠ ∞ := by
    dsimp only [c]
    exact ENNReal.coe_ne_top
  change 2 * (f / t) = (2 * (c / t)) * (f / c)
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  symm
  calc
    (2 * (c * t⁻¹)) * (f * c⁻¹) =
        2 * (f * (c⁻¹ * c)) * t⁻¹ := by ac_rfl
    _ = 2 * (f * 1) * t⁻¹ := by
      rw [ENNReal.inv_mul_cancel hc0 hcTop]
    _ = 2 * (f * t⁻¹) := by simp [mul_assoc]

#print axioms fullCoefficientRelativeFixed
#print axioms fullCoefficientRelativeFixed_ne_top
#print axioms fullCoefficientRelativeFixed_pos
#print axioms
  coe_criticalScaleProxyRadius_eq_relativeFixed_mul_ratio

end
end Family8FullCoefficientCriticalScaleRelativeFixedV3
