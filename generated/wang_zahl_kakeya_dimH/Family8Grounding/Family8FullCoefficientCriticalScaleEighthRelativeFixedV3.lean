import Family8Grounding.Family8FullCoefficientCriticalScaleRelativeFixedV3
import Mathlib.Tactic

/-!
# Eighth-normalized relative-fixed proxy scale

The endpoint full-metric route first sends its B2-supported WZL3 family
through the exact eighth normalization.  Its proxy input radius is therefore
`fine / 8`, while the Section-8 middle factor must remain written at the
original physical scales `fine -> coarse`.  The fixed coefficient is the
un-normalized relative coefficient divided by eight (equivalently
`coarse / (4 * criticalScale)`).
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8FullCoefficientCriticalScaleEighthRelativeFixedV3

open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8FullCoefficientCriticalScaleRelativeFixedV3
open Family8WeightedCanonicalCriticalScalePositiveV1

noncomputable section

universe u

/-- Relative coefficient after exact eighth normalization of the WZL3
source. -/
def fullCoefficientEighthRelativeFixed
    (coarse : NNReal) {iota : Type u}
    (W : WeightedCanonicalNormBallData iota) : ENNReal :=
  fullCoefficientRelativeFixed coarse W / 8

theorem fullCoefficientEighthRelativeFixed_ne_top
    {coarse : NNReal} (hcoarse : 0 < coarse)
    {iota : Type u} (W : WeightedCanonicalNormBallData iota) :
    fullCoefficientEighthRelativeFixed coarse W ≠ ∞ := by
  unfold fullCoefficientEighthRelativeFixed
  exact ENNReal.div_ne_top
    (fullCoefficientRelativeFixed_ne_top hcoarse W) (by norm_num)

theorem fullCoefficientEighthRelativeFixed_pos
    {coarse : NNReal} (hcoarse : 0 < coarse)
    {iota : Type u} (W : WeightedCanonicalNormBallData iota) :
    0 < fullCoefficientEighthRelativeFixed coarse W := by
  unfold fullCoefficientEighthRelativeFixed
  exact ENNReal.div_pos
    (fullCoefficientRelativeFixed_pos hcoarse W).ne' (by norm_num)

/-- The eighth-normalized proxy radius is exactly an arbitrary fixed
coefficient times the original physical fine-to-middle ratio. -/
theorem coe_eighth_criticalScaleProxyRadius_eq_relativeFixed_mul_ratio
    (fine coarse : NNReal) (hcoarse : 0 < coarse)
    {iota : Type u} (W : WeightedCanonicalNormBallData iota) :
    (criticalScaleProxyRadius (fine / 8) W.criticalScale
        (weightedCanonicalCriticalScale_pos W) : ENNReal) =
      fullCoefficientEighthRelativeFixed coarse W *
        ((fine : ENNReal) / (coarse : ENNReal)) := by
  calc
    (criticalScaleProxyRadius (fine / 8) W.criticalScale
        (weightedCanonicalCriticalScale_pos W) : ENNReal) =
        fullCoefficientRelativeFixed coarse W *
          (((fine / 8 : NNReal) : ENNReal) / (coarse : ENNReal)) :=
      coe_criticalScaleProxyRadius_eq_relativeFixed_mul_ratio
        (fine / 8) coarse hcoarse W
    _ = (fullCoefficientRelativeFixed coarse W / 8) *
          ((fine : ENNReal) / (coarse : ENNReal)) := by
      rw [ENNReal.coe_div (by norm_num : (8 : NNReal) ≠ 0)]
      simp only [ENNReal.coe_ofNat, div_eq_mul_inv]
      ac_rfl
    _ = fullCoefficientEighthRelativeFixed coarse W *
          ((fine : ENNReal) / (coarse : ENNReal)) := rfl

#print axioms fullCoefficientEighthRelativeFixed
#print axioms fullCoefficientEighthRelativeFixed_ne_top
#print axioms fullCoefficientEighthRelativeFixed_pos
#print axioms
  coe_eighth_criticalScaleProxyRadius_eq_relativeFixed_mul_ratio

end
end Family8FullCoefficientCriticalScaleEighthRelativeFixedV3
