import Family8Grounding.Family8ContractedJohnActualTubeProxyV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open scoped ENNReal NNReal

namespace Family8ContractedJohnNormalizedProxyScaleRatioV3

open Family8ContractedJohnActualTubeProxyV1

noncomputable section

/-!
# The fixed `3/64` normalized contracted-John scale ratio

After the contracted-John proxy is normalized by the final factor eight, its
radius is exactly `(3/64) * (delta/rho)`.  The results below expose both
directions of this identity and their `ENNReal.rpow` forms.  Thus downstream
first-factor arguments can work at the literal proxy scale and pay only the
fixed coefficient `(64/3)^p` when returning to the official relative scale.
-/

theorem contractedJohnProxyRadius_div_eight_eq_fixed_mul_ratio
    {delta rho : NNReal} (hrho : 0 < rho) :
    contractedJohnProxyRadius delta rho / 8 =
      (3 / 64 : NNReal) * (delta / rho) := by
  apply NNReal.eq
  simp only [contractedJohnProxyRadius, NNReal.coe_div,
    NNReal.coe_mul, NNReal.coe_ofNat]
  have hrhoReal : (rho : Real) ≠ 0 := by
    exact_mod_cast hrho.ne'
  field_simp [hrhoReal]
  ring

theorem ratio_eq_fixed_mul_contractedJohnProxyRadius_div_eight
    {delta rho : NNReal} (hrho : 0 < rho) :
    delta / rho =
      (64 / 3 : NNReal) * (contractedJohnProxyRadius delta rho / 8) := by
  apply NNReal.eq
  simp only [contractedJohnProxyRadius, NNReal.coe_div,
    NNReal.coe_mul, NNReal.coe_ofNat]
  have hrhoReal : (rho : Real) ≠ 0 := by
    exact_mod_cast hrho.ne'
  field_simp [hrhoReal]
  ring

theorem coe_contractedJohnProxyRadius_div_eight_eq_fixed_mul_ratio
    {delta rho : NNReal} (hrho : 0 < rho) :
    (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal)) =
      (3 / 64 : ENNReal) *
        ((delta : ENNReal) / (rho : ENNReal)) := by
  rw [← ENNReal.coe_div hrho.ne']
  simpa using congrArg (fun x : NNReal => (x : ENNReal))
    (contractedJohnProxyRadius_div_eight_eq_fixed_mul_ratio
      (delta := delta) hrho)

theorem coe_ratio_eq_fixed_mul_contractedJohnProxyRadius_div_eight
    {delta rho : NNReal} (hrho : 0 < rho) :
    (delta : ENNReal) / (rho : ENNReal) =
      (64 / 3 : ENNReal) *
        (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal)) := by
  rw [← ENNReal.coe_div hrho.ne']
  simpa using congrArg (fun x : NNReal => (x : ENNReal))
    (ratio_eq_fixed_mul_contractedJohnProxyRadius_div_eight
      (delta := delta) hrho)

/-- Exact rpow splitting at the literal normalized proxy scale. -/
theorem contractedJohnProxyRadius_div_eight_rpow_eq
    {delta rho : NNReal} (hrho : 0 < rho) (p : Real) :
    (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal)) ^ p =
      (3 / 64 : ENNReal) ^ p *
        (((delta : ENNReal) / (rho : ENNReal)) ^ p) := by
  rw [coe_contractedJohnProxyRadius_div_eight_eq_fixed_mul_ratio hrho,
    ENNReal.mul_rpow_of_ne_top]
  . finiteness
  . finiteness

/-- Returning from the literal proxy scale to the official relative scale
costs exactly the fixed coefficient `(64/3)^p`. -/
theorem ratio_rpow_eq_fixed_mul_contractedJohnProxyRadius_div_eight_rpow
    {delta rho : NNReal} (hrho : 0 < rho) (p : Real) :
    (((delta : ENNReal) / (rho : ENNReal)) ^ p) =
      (64 / 3 : ENNReal) ^ p *
        (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal) ^ p) := by
  rw [coe_ratio_eq_fixed_mul_contractedJohnProxyRadius_div_eight hrho,
    ENNReal.mul_rpow_of_ne_top]
  . finiteness
  . finiteness

/-- For a nonnegative exponent, the literal normalized proxy power is no
larger than the official relative-scale power. -/
theorem contractedJohnProxyRadius_div_eight_rpow_le_ratio_rpow
    {delta rho : NNReal} (hrho : 0 < rho) {p : Real} (hp : 0 ≤ p) :
    (((contractedJohnProxyRadius delta rho / 8 : NNReal) : ENNReal)) ^ p ≤
      (((delta : ENNReal) / (rho : ENNReal)) ^ p) := by
  apply ENNReal.rpow_le_rpow _ hp
  rw [coe_contractedJohnProxyRadius_div_eight_eq_fixed_mul_ratio hrho]
  apply mul_le_of_le_one_left bot_le
  apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
  norm_num

#print axioms contractedJohnProxyRadius_div_eight_eq_fixed_mul_ratio
#print axioms ratio_eq_fixed_mul_contractedJohnProxyRadius_div_eight
#print axioms contractedJohnProxyRadius_div_eight_rpow_eq
#print axioms
  ratio_rpow_eq_fixed_mul_contractedJohnProxyRadius_div_eight_rpow
#print axioms contractedJohnProxyRadius_div_eight_rpow_le_ratio_rpow

end
end Family8ContractedJohnNormalizedProxyScaleRatioV3
