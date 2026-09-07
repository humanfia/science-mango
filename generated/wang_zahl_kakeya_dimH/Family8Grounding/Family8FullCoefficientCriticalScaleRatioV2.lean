import Family8Grounding.Family8WeightedCanonicalCriticalScalePositiveV1
import Family8Grounding.Family8Family7NativeHighCriticalScaleProxyGeometryV1
import Mathlib.Tactic

/-!
# NNReal wrapper and exact ratio for a weighted canonical critical scale
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8FullCoefficientCriticalScaleRatioV2

open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8WeightedCanonicalCriticalScalePositiveV1

noncomputable section

universe u

/-- The positive real canonical critical scale as an `NNReal`. -/
def weightedCanonicalCriticalScaleNNReal
    {iota : Type u} (W : WeightedCanonicalNormBallData iota) : NNReal :=
  ⟨W.criticalScale, (weightedCanonicalCriticalScale_pos W).le⟩

@[simp] theorem weightedCanonicalCriticalScaleNNReal_coe
    {iota : Type u} (W : WeightedCanonicalNormBallData iota) :
    (weightedCanonicalCriticalScaleNNReal W : Real) = W.criticalScale :=
  rfl

theorem weightedCanonicalCriticalScaleNNReal_pos
    {iota : Type u} (W : WeightedCanonicalNormBallData iota) :
    0 < weightedCanonicalCriticalScaleNNReal W := by
  exact_mod_cast weightedCanonicalCriticalScale_pos W

/-- The critical-scale proxy radius is exactly twice the fine/coarse ratio. -/
theorem criticalScaleProxyRadius_eq_two_mul_ratio
    {iota : Type u} (radius : NNReal)
    (W : WeightedCanonicalNormBallData iota) :
    criticalScaleProxyRadius radius W.criticalScale
        (weightedCanonicalCriticalScale_pos W) =
      2 * (radius / weightedCanonicalCriticalScaleNNReal W) := by
  apply NNReal.eq
  simp only [criticalScaleProxyRadius_coe, NNReal.coe_mul,
    NNReal.coe_ofNat, NNReal.coe_div,
    weightedCanonicalCriticalScaleNNReal_coe, mul_div_assoc]

/-- `ENNReal` form used by the relative-scale Frostman envelope. -/
theorem coe_criticalScaleProxyRadius_eq_two_mul_ratio
    {iota : Type u} (radius : NNReal)
    (W : WeightedCanonicalNormBallData iota) :
    (criticalScaleProxyRadius radius W.criticalScale
        (weightedCanonicalCriticalScale_pos W) : ENNReal) =
      2 * ((radius : ENNReal) /
        (weightedCanonicalCriticalScaleNNReal W : ENNReal)) := by
  rw [← ENNReal.coe_div
    (weightedCanonicalCriticalScaleNNReal_pos W).ne']
  simpa using congrArg (fun x : NNReal => (x : ENNReal))
    (criticalScaleProxyRadius_eq_two_mul_ratio radius W)

#print axioms weightedCanonicalCriticalScaleNNReal
#print axioms criticalScaleProxyRadius_eq_two_mul_ratio
#print axioms coe_criticalScaleProxyRadius_eq_two_mul_ratio

end
end Family8FullCoefficientCriticalScaleRatioV2
