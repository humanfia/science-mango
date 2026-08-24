import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41CriticalLocalizationNumericsV1

/-!
# Numerical localization for PYZ Proposition 4.1

Provenance: Pramanik--Yang--Zahl, arXiv:2207.02259v3,
Lemma 3.8(1b) as used in the proof of Lemma 4.7.

This file contains only the positive square-root algebra and the interval-hull
step.  The critical point and the localization of the two actual roots are
produced in the subsequent geometric module.
-/

/-- The explicit constant obtained from the sharp curvature lower bound
`coefficient / 45` and critical-value bound `10 * tangency`. -/
noncomputable def prop41CriticalLocalizationFactor (K q : Real) : Real :=
  2 * Real.sqrt (45 * (10 * K + q))

/-- Normalize the raw critical-point radius by a coefficient lower scale.
The parameter `q` is the sublevel tolerance in units of `delta`; roots use
`q = 0`, while rectangle bases use a fixed positive `q`. -/
theorem two_mul_sqrt_critical_ratio_le_factor_mul_sqrt_delta_div_scale
    {delta t coefficient tangency K q : Real}
    (hdelta : 0 < delta) (ht : 0 < t)
    (hcoefficient : t <= coefficient)
    (htangency : 0 <= tangency)
    (hK : 0 <= K) (hq : 0 <= q)
    (htangencyUpper : tangency <= K * delta) :
    2 * Real.sqrt
        ((10 * tangency + q * delta) / (coefficient / 45)) <=
      prop41CriticalLocalizationFactor K q * Real.sqrt (delta / t) := by
  have hcoefficientPos : 0 < coefficient := lt_of_lt_of_le ht hcoefficient
  have hdenomPos : 0 < coefficient / 45 := by positivity
  have hdeltaDiv : 0 <= delta / t := by positivity
  have hfactor : 0 <= 45 * (10 * K + q) := by positivity
  have hnumerator : 0 <= 10 * tangency + q * delta := by positivity
  have hratio :
      (10 * tangency + q * delta) / (coefficient / 45) <=
        (45 * (10 * K + q)) * (delta / t) := by
    apply (div_le_iff₀ hdenomPos).2
    have htCoefficient : t / coefficient <= 1 := by
      exact (div_le_one hcoefficientPos).2 hcoefficient
    have hnumUpper :
        10 * tangency + q * delta <= (10 * K + q) * delta := by
      nlinarith
    calc
      10 * tangency + q * delta <= (10 * K + q) * delta := hnumUpper
      _ <= ((10 * K + q) * delta) * (coefficient / t) := by
        have hone : 1 <= coefficient / t :=
          (one_le_div ht).2 hcoefficient
        have hnonneg : 0 <= (10 * K + q) * delta := by positivity
        nlinarith
      _ = (45 * (10 * K + q) * (delta / t)) *
            (coefficient / 45) := by
        field_simp [ne_of_gt ht, ne_of_gt hcoefficientPos]
  have hsqrt := Real.sqrt_le_sqrt hratio
  have hsqrtMul :
      Real.sqrt ((45 * (10 * K + q)) * (delta / t)) =
        Real.sqrt (45 * (10 * K + q)) * Real.sqrt (delta / t) := by
    rw [Real.sqrt_mul hfactor]
  rw [hsqrtMul] at hsqrt
  dsimp [prop41CriticalLocalizationFactor]
  nlinarith [Real.sqrt_nonneg
    ((10 * tangency + q * delta) / (coefficient / 45))]

/-- Every point between two endpoints localized at the same center is
localized by the same radius.  This is the finite interval support step for
the lens cut out by two roots. -/
theorem abs_sub_le_of_mem_Icc_of_endpoint_abs_sub_le
    {thetaLeft thetaRight theta theta0 radius : Real}
    (htheta : theta ∈ Icc thetaLeft thetaRight)
    (hleft : |thetaLeft - theta0| <= radius)
    (hright : |thetaRight - theta0| <= radius) :
    |theta - theta0| <= radius := by
  rw [abs_le] at hleft hright ⊢
  constructor <;> linarith [htheta.1, htheta.2]

/-- The root-support interval inherits a normalized square-root localization
from the two raw endpoint bounds. -/
theorem rootSupport_localized_at_critical_scale
    {delta t coefficient tangency K thetaLeft thetaRight theta theta0 : Real}
    (hdelta : 0 < delta) (ht : 0 < t)
    (hcoefficient : t <= coefficient)
    (htangency : 0 <= tangency) (hK : 0 <= K)
    (htangencyUpper : tangency <= K * delta)
    (htheta : theta ∈ Icc thetaLeft thetaRight)
    (hleft : |thetaLeft - theta0| <=
      2 * Real.sqrt ((10 * tangency) / (coefficient / 45)))
    (hright : |thetaRight - theta0| <=
      2 * Real.sqrt ((10 * tangency) / (coefficient / 45))) :
    |theta - theta0| <=
      prop41CriticalLocalizationFactor K 0 * Real.sqrt (delta / t) := by
  have hhull := abs_sub_le_of_mem_Icc_of_endpoint_abs_sub_le
    htheta hleft hright
  exact hhull.trans
    (by
      simpa only [zero_mul, add_zero] using
        two_mul_sqrt_critical_ratio_le_factor_mul_sqrt_delta_div_scale
          hdelta ht hcoefficient htangency hK (by norm_num : (0 : Real) <= 0)
          htangencyUpper)

#print axioms two_mul_sqrt_critical_ratio_le_factor_mul_sqrt_delta_div_scale
#print axioms abs_sub_le_of_mem_Icc_of_endpoint_abs_sub_le
#print axioms rootSupport_localized_at_critical_scale

end FamilyStickyCinematicL32Prop41CriticalLocalizationNumericsV1
