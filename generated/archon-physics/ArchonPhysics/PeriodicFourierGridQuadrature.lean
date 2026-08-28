import ArchonPhysics.EqualMassPeriodicFPUTDiscreteContinuumShellBridge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule

/-!
# Quantitative quadrature on the periodic Fourier grid

The canonical representatives of `ZMod N` sample the half-open Brillouin
interval at spacing `2π/N`.  For a function whose endpoint values agree,
the corresponding left-grid sum is exactly Mathlib's composite trapezoidal
rule.  Its existing error estimate therefore gives a deterministic
thermodynamic-limit bound of order `N⁻²` under a uniform `C²` bound.

This is a quadrature theorem only.  When the sampled function contains a
finite-time resonance kernel, its second-derivative bound is time dependent;
the required joint relation between time and volume remains explicit.
-/

namespace ArchonPhysics.PeriodicFourierGridQuadrature

open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTDiscreteContinuumShellBridge
open ArchonPhysics.Lattice
open MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- `ZMod.finEquiv` preserves the canonical representative in a nonempty
volume. -/
theorem finEquiv_val
    {N : Nat} [NeZero N] (i : Fin N) :
    ((ZMod.finEquiv N).toEquiv i).val = i.val := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

/-- A periodic Fourier-grid sum is exactly the composite trapezoidal rule.
The endpoint equality is the only periodicity fact needed by this identity. -/
theorem fourierGrid_sum_eq_trapezoidal_integral
    (N : Nat) [NeZero N] (f : Real → Real)
    (hendpoint : f 0 = f (2 * Real.pi)) :
    (2 * Real.pi / (N : Real)) *
        ∑ k : Site N, f (gridWaveNumber N k) =
      trapezoidal_integral f N 0 (2 * Real.pi) := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      rw [← (ZMod.finEquiv (n + 1)).sum_comp]
      rw [Fin.sum_univ_succ]
      unfold trapezoidal_integral gridWaveNumber
      rw [← Fin.sum_univ_eq_sum_range]
      simp only [finEquiv_val, Fin.val_zero, Nat.cast_zero, mul_zero,
        zero_div, Fin.val_succ, Nat.cast_add, Nat.cast_one,
        zero_add]
      rw [← hendpoint]
      congr 1
      · ring
      · have hhalf : (f 0 + f 0) / 2 = f 0 := by ring
        rw [hhalf]
        apply congrArg (fun value : Real ↦ f 0 + value)
        apply Finset.sum_congr rfl
        intro i _hi
        congr 1
        ring

/-- Quantitative one-dimensional thermodynamic-limit estimate on the
Brillouin grid.  The right side is the standard trapezoidal error
`(2π)³ ζ /(12 N²)`. -/
theorem abs_fourierGrid_sum_sub_integral_le
    (N : Nat) [NeZero N] (f : Real → Real)
    (hendpoint : f 0 = f (2 * Real.pi))
    (hC2 : ContDiffOn Real 2 f (uIcc (0 : Real) (2 * Real.pi)))
    {zeta : Real}
    (hsecond : ∀ x,
      |iteratedDerivWithin 2 f (uIcc (0 : Real) (2 * Real.pi)) x| ≤ zeta) :
    |(2 * Real.pi / (N : Real)) *
        ∑ k : Site N, f (gridWaveNumber N k) -
      ∫ x in (0 : Real)..(2 * Real.pi), f x| ≤
      |2 * Real.pi - 0| ^ 3 * zeta / (12 * (N : Real) ^ 2) := by
  rw [fourierGrid_sum_eq_trapezoidal_integral N f hendpoint]
  exact trapezoidal_error_le_of_c2 hC2 hsecond (Nat.pos_of_ne_zero (NeZero.ne N))

end

end ArchonPhysics.PeriodicFourierGridQuadrature
