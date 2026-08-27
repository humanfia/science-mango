import ArchonPhysics.ModalPhaseMismatch

/-!
# Finite-time resonance weights

This module packages the deterministic finite-time broadening associated with
one real phase mismatch.  For a positive observation time `T`, the weight is
the squared norm of the oscillatory integral divided by `T`; for `T ≤ 0`, it
is defined to be zero.

The modal sum below is finite and belongs to one fixed positive-mass
realization.  No limiting delta measure, random empirical-measure limit, or
collision-kernel identification is asserted.
-/

namespace ArchonPhysics.FiniteTimeResonanceWeight

open ArchonPhysics
open ModeCoupling
open ModalPhaseMismatch
open NonresonantOscillatoryGain

noncomputable section

/-- Finite-time broadening of a real phase mismatch, extended by zero to
nonpositive observation times. -/
def finiteTimeResonanceWeight (Omega T : Real) : Real :=
  if 0 < T then ‖oscillatoryIntegral Omega T‖ ^ 2 / T else 0

@[simp] theorem finiteTimeResonanceWeight_of_nonpos {Omega T : Real}
    (hT : T ≤ 0) :
    finiteTimeResonanceWeight Omega T = 0 := by
  simp [finiteTimeResonanceWeight, not_lt.mpr hT]

/-- A finite-time resonance weight is nonnegative for every real `T`. -/
theorem finiteTimeResonanceWeight_nonneg (Omega T : Real) :
    0 ≤ finiteTimeResonanceWeight Omega T := by
  by_cases hT : 0 < T
  · rw [finiteTimeResonanceWeight, if_pos hT]
    exact div_nonneg (sq_nonneg _) hT.le
  · simp [finiteTimeResonanceWeight, hT]

/-- At exact resonance, a positive observation time has weight exactly `T`. -/
@[simp] theorem finiteTimeResonanceWeight_zero_of_pos {T : Real} (hT : 0 < T) :
    finiteTimeResonanceWeight 0 T = T := by
  rw [finiteTimeResonanceWeight, if_pos hT, oscillatoryIntegral_zero]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  rw [pow_two, mul_div_cancel_left₀ T hT.ne']

/-- Exact resonant value, including the convention at nonpositive times. -/
@[simp] theorem finiteTimeResonanceWeight_zero (T : Real) :
    finiteTimeResonanceWeight 0 T = max T 0 := by
  by_cases hT : 0 < T
  · rw [finiteTimeResonanceWeight_zero_of_pos hT, max_eq_left hT.le]
  · rw [finiteTimeResonanceWeight_of_nonpos (le_of_not_gt hT),
      max_eq_right (le_of_not_gt hT)]

/-- Away from resonance, the finite-time weight has the squared inverse-gap
tail obtained from the oscillatory integral estimate. -/
theorem finiteTimeResonanceWeight_le_inverse_gap {Omega T : Real}
    (hOmega : Omega ≠ 0) (hT : 0 < T) :
    finiteTimeResonanceWeight Omega T ≤ (2 / |Omega|) ^ 2 / T := by
  rw [finiteTimeResonanceWeight, if_pos hT]
  have hgap : 0 ≤ 2 / |Omega| :=
    div_nonneg (by norm_num) (abs_nonneg Omega)
  have hsquare :
      ‖oscillatoryIntegral Omega T‖ ^ 2 ≤ (2 / |Omega|) ^ 2 := by
    nlinarith [norm_nonneg (oscillatoryIntegral Omega T),
      norm_oscillatoryIntegral_le_two_div_abs (t := T) hOmega]
  exact div_le_div_of_nonneg_right hsquare hT.le

/-- Finite sum of broadened modal weights for one fixed positive-mass
realization, weighted by the square of the exact interaction tensor. -/
def finiteModeResonanceSum {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (sign : Fin n → InteractionSign) (T : Real) : Real :=
  ∑ modes : Fin n → Lattice.Site N,
    (interactionTensor m n modes) ^ 2 *
      finiteTimeResonanceWeight (phaseMismatch m sign modes) T

/-- The fixed-realization finite modal sum is nonnegative. -/
theorem finiteModeResonanceSum_nonneg {N n : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (sign : Fin n → InteractionSign) (T : Real) :
    0 ≤ finiteModeResonanceSum m sign T := by
  unfold finiteModeResonanceSum
  exact Finset.sum_nonneg fun modes _ =>
    mul_nonneg (sq_nonneg _) (finiteTimeResonanceWeight_nonneg _ _)

end

end ArchonPhysics.FiniteTimeResonanceWeight
