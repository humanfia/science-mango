import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Nonresonant oscillatory gain

The diagrammatic expansions used in rigorous wave-kinetic derivations reduce
nonresonant interactions to oscillatory time integrals.  This module isolates
the model-independent first estimate: a nonzero phase mismatch `Omega` gives
an inverse-gap gain.

The result is independent of translation invariance, Fourier momentum
conservation, or a particular dispersion relation, so it remains applicable
after replacing the homogeneous FPUT Fourier modes by the finite normal modes
of a positive random-mass realization.

No lower bound on a random phase mismatch and no kinetic-limit convergence is
asserted here.
-/

namespace ArchonPhysics.NonresonantOscillatoryGain

open scoped Interval

noncomputable section

/-- The constant-amplitude oscillatory factor with real phase mismatch `Omega`. -/
def oscillatoryIntegral (Omega t : Real) : Complex :=
  ∫ s in (0 : Real)..t, Complex.exp ((Complex.I * Omega) * s)

/-- At exact resonance the oscillatory factor is just the elapsed time. -/
@[simp] theorem oscillatoryIntegral_zero (t : Real) :
    oscillatoryIntegral 0 t = t := by
  simp [oscillatoryIntegral]

/-- Exact evaluation away from resonance. -/
theorem oscillatoryIntegral_eq_div {Omega t : Real} (hOmega : Omega ≠ 0) :
    oscillatoryIntegral Omega t =
      (Complex.exp (Complex.I * (Omega * t)) - 1) / (Complex.I * Omega) := by
  unfold oscillatoryIntegral
  rw [integral_exp_mul_complex]
  · simp [mul_assoc]
  · exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hOmega)

/-- A nonzero phase mismatch gives the standard inverse-gap estimate. -/
theorem norm_oscillatoryIntegral_le_two_div_abs {Omega t : Real} (hOmega : Omega ≠ 0) :
    ‖oscillatoryIntegral Omega t‖ ≤ 2 / |Omega| := by
  rw [oscillatoryIntegral_eq_div hOmega, norm_div]
  have hnum :
      ‖Complex.exp (Complex.I * (Omega * t)) - 1‖ ≤ (2 : Real) := by
    calc
      ‖Complex.exp (Complex.I * (Omega * t)) - 1‖ ≤
          ‖Complex.exp (Complex.I * (Omega * t))‖ + ‖(1 : Complex)‖ :=
        norm_sub_le _ _
      _ = 2 := by
        rw [← Complex.ofReal_mul, Complex.norm_exp_I_mul_ofReal]
        norm_num
  simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
    (div_le_div_of_nonneg_right hnum (abs_nonneg Omega))

/-- The same factor is always bounded by the length of the time interval. -/
theorem norm_oscillatoryIntegral_le_abs_time (Omega t : Real) :
    ‖oscillatoryIntegral Omega t‖ ≤ |t| := by
  by_cases hOmega : Omega = 0
  · subst Omega
    simp [Real.norm_eq_abs]
  · rw [oscillatoryIntegral_eq_div hOmega, norm_div]
    have hnum := Real.norm_exp_I_mul_ofReal_sub_one_le (x := Omega * t)
    calc
      ‖Complex.exp (Complex.I * (Omega * t)) - 1‖ /
          ‖Complex.I * (Omega : Complex)‖ ≤
          |Omega * t| / |Omega| := by
        simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
          (div_le_div_of_nonneg_right hnum (abs_nonneg Omega))
      _ = |t| := by
        rw [abs_mul]
        exact mul_div_cancel_left₀ |t| (abs_ne_zero.mpr hOmega)

/-- Combined time-length and inverse-gap control. -/
theorem norm_oscillatoryIntegral_le_min {Omega t : Real} (hOmega : Omega ≠ 0) :
    ‖oscillatoryIntegral Omega t‖ ≤ min |t| (2 / |Omega|) := by
  exact le_min (norm_oscillatoryIntegral_le_abs_time Omega t)
    (norm_oscillatoryIntegral_le_two_div_abs hOmega)

end

end ArchonPhysics.NonresonantOscillatoryGain
