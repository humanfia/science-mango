import ArchonPhysics.LocalCollisionDensityTransfer
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Fractional pointwise decay of the normalized resonance kernel

The height and inverse-square tail bounds for the normalized sinc-squared
kernel are individually insufficient at the critical quadratic small-ball
exponent.  This module records an intermediate pointwise estimate.  The
elementary global inequality

`sin(x)^2 <= sqrt |x|`

gives a half-power of time decay while requiring only a negative half moment
after multiplication by the acoustic leg factor.  This is the useful
fractional estimate for the repeated parent--child sectors.
-/

namespace ArchonPhysics.FractionalResonanceKernelDecay

open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.ResonanceWeightSinc
open ArchonPhysics.SincSquareMassExact

noncomputable section

/-- A global fractional interpolation between `sin(x)^2 <= x^2` near zero
and `sin(x)^2 <= 1` away from zero. -/
theorem sin_sq_le_sqrt_abs (x : Real) :
    Real.sin x ^ 2 <= Real.sqrt |x| := by
  by_cases hx : |x| <= 1
  · have hsquare : x ^ 2 <= |x| := by
      rw [show x ^ 2 = |x| ^ 2 by simp [sq_abs]]
      nlinarith [abs_nonneg x]
    have habsSqrt : |x| <= Real.sqrt |x| :=
      Real.le_sqrt_self_iff.mpr hx
    exact Real.sin_sq_le_sq.trans (hsquare.trans habsSqrt)
  · have hxone : 1 <= |x| := le_of_lt (lt_of_not_ge hx)
    have hsqrtOne : 1 <= Real.sqrt |x| := by
      simpa using Real.sqrt_le_sqrt hxone
    exact (Real.sin_sq_le_one x).trans hsqrtOne

/-- At nonzero mismatch the normalized finite-time resonance kernel admits
an exact fractional tail bound.  The deliberately unsimplified right-hand
side avoids hiding any power of `T` or `Omega` behind asymptotic notation. -/
theorem normalizedFiniteTimeResonanceKernel_le_fractionalTail
    {Omega T : Real} (hOmega : Omega ≠ 0) (hT : 0 < T) :
    normalizedFiniteTimeResonanceKernel Omega T <=
      2 * Real.sqrt |Omega * T / 2| /
        (Real.pi * Omega ^ 2 * T) := by
  rw [normalizedFiniteTimeResonanceKernel, sincSquareMass_eq_pi,
    finiteTimeResonanceWeight_eq_sine hOmega hT]
  have hdenom : 0 < Real.pi * Omega ^ 2 * T := by positivity
  have hsin := sin_sq_le_sqrt_abs (Omega * T / 2)
  rw [div_div]
  calc
    (2 * Real.sin (Omega * T / 2)) ^ 2 /
          (Omega ^ 2 * T * (2 * Real.pi)) =
        2 * Real.sin (Omega * T / 2) ^ 2 /
          (Real.pi * Omega ^ 2 * T) := by
      field_simp [hOmega, hT.ne', Real.pi_ne_zero]
    _ <= 2 * Real.sqrt |Omega * T / 2| /
          (Real.pi * Omega ^ 2 * T) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsin (by norm_num)) hdenom.le

/-- After multiplication by a positive acoustic frequency, one inverse
power cancels exactly.  This is the form used with fixed-child interaction
weight estimates. -/
theorem frequency_mul_normalizedFiniteTimeResonanceKernel_le_fractionalTail
    {frequency T : Real} (hfrequency : 0 < frequency) (hT : 0 < T) :
    frequency * normalizedFiniteTimeResonanceKernel frequency T <=
      2 * Real.sqrt |frequency * T / 2| /
        (Real.pi * frequency * T) := by
  have hbase := normalizedFiniteTimeResonanceKernel_le_fractionalTail
    hfrequency.ne' hT
  have hmul := mul_le_mul_of_nonneg_left hbase hfrequency.le
  calc
    frequency * normalizedFiniteTimeResonanceKernel frequency T <=
        frequency *
          (2 * Real.sqrt |frequency * T / 2| /
            (Real.pi * frequency ^ 2 * T)) := hmul
    _ = 2 * Real.sqrt |frequency * T / 2| /
          (Real.pi * frequency * T) := by
      field_simp [hfrequency.ne', hT.ne', Real.pi_ne_zero]

end

end ArchonPhysics.FractionalResonanceKernelDecay
