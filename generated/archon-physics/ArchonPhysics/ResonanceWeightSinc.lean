import ArchonPhysics.FiniteTimeResonanceWeight
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Sinc representation of the finite-time resonance weight

The squared oscillatory integral divided by time is exactly the rescaled
square of the real sinc function.  This identifies the finite-time weight
with the standard Fejer-type approximate-delta profile and records its
pointwise decay away from resonance.

No integration over phase mismatch or empirical collision limit is asserted.
-/

namespace ArchonPhysics.ResonanceWeightSinc

open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.NonresonantOscillatoryGain
open Filter

noncomputable section

/-- Exact trigonometric formula away from zero phase mismatch. -/
theorem finiteTimeResonanceWeight_eq_sine
    {Omega T : Real} (hOmega : Omega ≠ 0) (hT : 0 < T) :
    finiteTimeResonanceWeight Omega T =
      (2 * Real.sin (Omega * T / 2)) ^ 2 / (Omega ^ 2 * T) := by
  rw [finiteTimeResonanceWeight, if_pos hT,
    oscillatoryIntegral_eq_div hOmega, norm_div]
  have harg : Complex.I * ((Omega : Complex) * (T : Complex)) =
      Complex.I * (Omega * T : Real) := by norm_num
  rw [harg, Complex.norm_exp_I_mul_ofReal_sub_one]
  simp only [norm_mul, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, one_mul]
  rw [abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
  field_simp [abs_ne_zero.mpr hOmega, hOmega, hT.ne']
  rw [sq_abs, sq_abs Omega]

/-- Exact globally valid rescaled-sinc formula at positive time. -/
theorem finiteTimeResonanceWeight_eq_mul_sinc_sq
    (Omega : Real) {T : Real} (hT : 0 < T) :
    finiteTimeResonanceWeight Omega T =
      T * Real.sinc (Omega * T / 2) ^ 2 := by
  by_cases hOmega : Omega = 0
  · subst Omega
    simp [finiteTimeResonanceWeight_zero_of_pos hT, Real.sinc_zero]
  · rw [finiteTimeResonanceWeight_eq_sine hOmega hT,
      Real.sinc_of_ne_zero]
    · field_simp
    · exact div_ne_zero (mul_ne_zero hOmega hT.ne') (by norm_num)

/-- The resonance profile is even in the phase mismatch. -/
theorem finiteTimeResonanceWeight_neg (Omega T : Real) :
    finiteTimeResonanceWeight (-Omega) T =
      finiteTimeResonanceWeight Omega T := by
  by_cases hT : 0 < T
  · rw [finiteTimeResonanceWeight_eq_mul_sinc_sq (-Omega) hT,
      finiteTimeResonanceWeight_eq_mul_sinc_sq Omega hT,
      show -Omega * T / 2 = -(Omega * T / 2) by ring, Real.sinc_neg]
  · rw [finiteTimeResonanceWeight_of_nonpos (le_of_not_gt hT),
      finiteTimeResonanceWeight_of_nonpos (le_of_not_gt hT)]

/-- At every fixed nonzero mismatch, the finite-time resonance weight tends
to zero along integer observation times. -/
theorem tendsto_finiteTimeResonanceWeight_nat_at_nonzero
    {Omega : Real} (hOmega : Omega ≠ 0) :
    Tendsto (fun n : Nat ↦ finiteTimeResonanceWeight Omega (n + 1))
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact finiteTimeResonanceWeight_nonneg _ _
  · intro n
    exact finiteTimeResonanceWeight_le_inverse_gap hOmega (by positivity)
  · have hconst : Tendsto
        (fun _n : Nat ↦ ((2 / |Omega|) ^ 2 : Real)) atTop
        (nhds ((2 / |Omega|) ^ 2)) := tendsto_const_nhds
    have hdenom :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real)
    simpa only [div_eq_mul_inv, one_div, one_mul, mul_zero] using
      hconst.mul hdenom

end

end ArchonPhysics.ResonanceWeightSinc
