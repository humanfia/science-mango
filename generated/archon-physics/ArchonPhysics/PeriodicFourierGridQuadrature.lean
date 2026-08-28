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

/-! ## A lower-regularity bound suited to finite-time resonance kernels -/

/-- A periodic Lipschitz integrand has deterministic Fourier-grid error of
order `N⁻¹`.  This weaker rate needs no second derivative and is therefore
useful when the Lipschitz constant grows with the observation time. -/
theorem abs_fourierGrid_sum_sub_integral_le_of_lipschitz
    (N : Nat) [NeZero N] (f : Real → Real) {L : Real}
    (hL : 0 ≤ L)
    (hendpoint : f 0 = f (2 * Real.pi))
    (hcontinuous : ContinuousOn f (Icc (0 : Real) (2 * Real.pi)))
    (hlipschitz : ∀ x ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
        |f x - f y| ≤ L * |x - y|) :
    |(2 * Real.pi / (N : Real)) *
        ∑ k : Site N, f (gridWaveNumber N k) -
      ∫ x in (0 : Real)..(2 * Real.pi), f x| ≤
      L * (2 * Real.pi) ^ 2 / (N : Real) := by
  let step : Real := 2 * Real.pi / (N : Real)
  have hNnat : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNreal : (0 : Real) < (N : Real) := by exact_mod_cast hNnat
  have hstep : 0 < step := by
    dsimp [step]
    positivity
  have htotal : (N : Real) * step = 2 * Real.pi := by
    dsimp [step]
    field_simp
  have hglobalIntegrable :
      IntervalIntegrable f volume (0 : Real) (2 * Real.pi) :=
    hcontinuous.intervalIntegrable_of_Icc (by positivity)
  have hcell (k : Nat) (hk : k < N) :
      |trapezoidal_error f 1 ((k : Real) * step)
          (((k : Real) + 1) * step)| ≤ L * step ^ 2 := by
    let left : Real := (k : Real) * step
    let right : Real := ((k : Real) + 1) * step
    have hleftNonneg : 0 ≤ left := by
      dsimp [left]
      positivity
    have hkSuccReal : (k : Real) + 1 ≤ (N : Real) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hk)
    have hrightLe : right ≤ 2 * Real.pi := by
      dsimp [right]
      rw [← htotal]
      exact mul_le_mul_of_nonneg_right hkSuccReal hstep.le
    have hleftLeRight : left ≤ right := by
      dsimp [left, right]
      exact mul_le_mul_of_nonneg_right (by linarith) hstep.le
    have hcellSubset : Icc left right ⊆ Icc (0 : Real) (2 * Real.pi) := by
      intro x hx
      exact ⟨hleftNonneg.trans hx.1, hx.2.trans hrightLe⟩
    have hcellIntegrable : IntervalIntegrable f volume left right :=
      (hcontinuous.mono hcellSubset).intervalIntegrable_of_Icc hleftLeRight
    have hwidth : right - left = step := by
      dsimp [left, right]
      ring
    have herrorIdentity :
        trapezoidal_error f 1 left right =
          ∫ x in left..right, ((f left + f right) / 2 - f x) := by
      rw [trapezoidal_error, trapezoidal_integral_one,
        intervalIntegral.integral_sub intervalIntegrable_const hcellIntegrable,
        intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    rw [herrorIdentity, ← Real.norm_eq_abs]
    calc
      ‖∫ x in left..right, ((f left + f right) / 2 - f x)‖ ≤
          (L * step) * |right - left| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro x hx
        rw [uIoc_of_le hleftLeRight] at hx
        have hxIcc : x ∈ Icc left right := ⟨hx.1.le, hx.2⟩
        have hleftFull : left ∈ Icc (0 : Real) (2 * Real.pi) :=
          ⟨hleftNonneg, hleftLeRight.trans hrightLe⟩
        have hrightFull : right ∈ Icc (0 : Real) (2 * Real.pi) :=
          ⟨hleftNonneg.trans hleftLeRight, hrightLe⟩
        have hxFull : x ∈ Icc (0 : Real) (2 * Real.pi) :=
          hcellSubset hxIcc
        have hleftDistance : |left - x| ≤ step := by
          rw [abs_of_nonpos (sub_nonpos.mpr hxIcc.1), neg_sub, ← hwidth]
          linarith [hxIcc.2]
        have hrightDistance : |right - x| ≤ step := by
          rw [abs_of_nonneg (sub_nonneg.mpr hxIcc.2)]
          rw [← hwidth]
          linarith [hxIcc.1]
        have hleftLip := hlipschitz left hleftFull x hxFull
        have hrightLip := hlipschitz right hrightFull x hxFull
        have hleftBound : |f left - f x| ≤ L * step :=
          hleftLip.trans
            (mul_le_mul_of_nonneg_left hleftDistance hL)
        have hrightBound : |f right - f x| ≤ L * step :=
          hrightLip.trans
            (mul_le_mul_of_nonneg_left hrightDistance hL)
        rw [Real.norm_eq_abs]
        calc
          |(f left + f right) / 2 - f x| =
              |(f left - f x + (f right - f x)) / 2| := by
                congr 1
                ring
          _ = |f left - f x + (f right - f x)| / 2 := by
                rw [abs_div]
                norm_num
          _ ≤ (|f left - f x| + |f right - f x|) / 2 := by
                exact div_le_div_of_nonneg_right
                  (abs_add_le (f left - f x) (f right - f x))
                  (by norm_num)
          _ ≤ (L * step + L * step) / 2 := by
                exact div_le_div_of_nonneg_right
                  (add_le_add hleftBound hrightBound) (by norm_num)
          _ = L * step := by ring
      _ = L * step ^ 2 := by rw [abs_of_nonneg (sub_nonneg.mpr hleftLeRight), hwidth]; ring
  rw [fourierGrid_sum_eq_trapezoidal_integral N f hendpoint]
  change |trapezoidal_error f N 0 (2 * Real.pi)| ≤ _
  have hendpointGrid : (0 : Real) + (N : Real) * step = 2 * Real.pi := by
    linarith [htotal]
  have hglobalGrid :
      IntervalIntegrable f volume (0 : Real)
        ((0 : Real) + (N : Real) * step) := by
    rw [hendpointGrid]
    exact hglobalIntegrable
  have hsum := sum_trapezoidal_error_adjacent_intervals
    (f := f) (a := 0) (h := step) hNnat hglobalGrid
  rw [hendpointGrid] at hsum
  rw [← hsum]
  calc
    |∑ k ∈ Finset.range N,
        trapezoidal_error f 1 ((0 : Real) + (k : Real) * step)
          ((0 : Real) + ((k : Real) + 1) * step)| ≤
        ∑ k ∈ Finset.range N,
          |trapezoidal_error f 1 ((0 : Real) + (k : Real) * step)
            ((0 : Real) + ((k : Real) + 1) * step)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range N, L * step ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [zero_add] using hcell k (Finset.mem_range.mp hk)
    _ = L * (2 * Real.pi) ^ 2 / (N : Real) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      dsimp [step]
      field_simp [ne_of_gt hNreal]

end

end ArchonPhysics.PeriodicFourierGridQuadrature
