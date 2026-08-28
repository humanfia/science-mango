import ArchonPhysics.EqualMassPeriodicFPUTLocalCollisionGridDiagonal
import Mathlib.Analysis.BoundedVariation

/-!
# Bounded-variation quadrature for finite-time collision peaks

This module replaces the pointwise `O(T^2)` Lipschitz cost of a finite-time
resonance peak by its `O(T)` total variation.  The first result is a general
periodic Fourier-grid quadrature estimate for continuous functions of bounded
variation.  The remaining results isolate the analytic scaling argument for
the squared-sinc peak.
-/

namespace ArchonPhysics.FPUTFiniteTimeCollisionBVQuadrature

open ArchonPhysics
open ArchonPhysics.EqualMassPeriodicFPUTActualEffectiveDiagramEnumeration
open ArchonPhysics.EqualMassPeriodicFPUTActualFirstNormalForm
open ArchonPhysics.EqualMassPeriodicFPUTCanonicalPositiveRootBrillouin
open ArchonPhysics.EqualMassPeriodicFPUTCanonicalUmklappCompactTest
open ArchonPhysics.EqualMassPeriodicFPUTExplicitCollisionKernelCertificate
open ArchonPhysics.EqualMassPeriodicFPUTLocalCollisionGridDiagonal
open ArchonPhysics.EqualMassPeriodicFPUTUmklappOnShellJacobian
open ArchonPhysics.EqualMassPeriodicFPUTUmklappTransversality
open ArchonPhysics.EqualMassPeriodicFPUTDiscreteContinuumShellBridge
open ArchonPhysics.FPUTFiniteTimeCollisionQuadrature
open ArchonPhysics.Lattice
open ArchonPhysics.PeriodicFourierGridQuadrature
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.ResonanceKernelLipschitz
open ArchonPhysics.SincSquareMassExact
open ArchonPhysics.UniformCollisionDensityTransfer
open Filter MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

/-- A periodic continuous function has Fourier-grid quadrature error bounded
by one mesh width times its total variation. -/
theorem abs_fourierGrid_sum_sub_integral_le_of_boundedVariation
    (N : Nat) [NeZero N] (f : Real → Real)
    (hendpoint : f 0 = f (2 * Real.pi))
    (hcontinuous : ContinuousOn f (Icc (0 : Real) (2 * Real.pi)))
    (hvariation : BoundedVariationOn f (Icc (0 : Real) (2 * Real.pi))) :
    |(2 * Real.pi / (N : Real)) *
        ∑ k : Site N, f (gridWaveNumber N k) -
      ∫ x in (0 : Real)..(2 * Real.pi), f x| ≤
      (2 * Real.pi / (N : Real)) *
        (eVariationOn f (Icc (0 : Real) (2 * Real.pi))).toReal := by
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
  have hcellVariationFinite (k : Nat) (hk : k < N) :
      BoundedVariationOn f
        (Icc ((k : Real) * step) (((k : Real) + 1) * step)) := by
    apply hvariation.mono
    intro x hx
    have hkSuccReal : (k : Real) + 1 ≤ (N : Real) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hk)
    constructor
    · exact (mul_nonneg (Nat.cast_nonneg k) hstep.le).trans hx.1
    · calc
        x ≤ ((k : Real) + 1) * step := hx.2
        _ ≤ (N : Real) * step :=
          mul_le_mul_of_nonneg_right hkSuccReal hstep.le
        _ = 2 * Real.pi := htotal
  have hcell (k : Nat) (hk : k < N) :
      |trapezoidal_error f 1 ((k : Real) * step)
          (((k : Real) + 1) * step)| ≤
        step * (eVariationOn f
          (Icc ((k : Real) * step)
            (((k : Real) + 1) * step))).toReal := by
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
    have hcellBV : BoundedVariationOn f (Icc left right) := by
      simpa only [left, right] using hcellVariationFinite k hk
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
          (eVariationOn f (Icc left right)).toReal * |right - left| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro x hx
        rw [uIoc_of_le hleftLeRight] at hx
        have hxIcc : x ∈ Icc left right := ⟨hx.1.le, hx.2⟩
        have hleftMem : left ∈ Icc left right := left_mem_Icc.mpr hleftLeRight
        have hrightMem : right ∈ Icc left right := right_mem_Icc.mpr hleftLeRight
        have hleftBound := hcellBV.dist_le hleftMem hxIcc
        have hrightBound := hcellBV.dist_le hrightMem hxIcc
        rw [Real.dist_eq] at hleftBound hrightBound
        rw [Real.norm_eq_abs]
        calc
          |(f left + f right) / 2 - f x| =
              |(f left - f x + (f right - f x)) / 2| := by
                congr 1
                ring
          _ ≤ (|f left - f x| + |f right - f x|) / 2 := by
                rw [abs_div]
                norm_num
                exact div_le_div_of_nonneg_right
                  (abs_add_le (f left - f x) (f right - f x))
                  (by norm_num)
          _ ≤ ((eVariationOn f (Icc left right)).toReal +
                (eVariationOn f (Icc left right)).toReal) / 2 := by
              exact div_le_div_of_nonneg_right
                (add_le_add hleftBound hrightBound) (by norm_num)
          _ = (eVariationOn f (Icc left right)).toReal := by ring
      _ = step * (eVariationOn f (Icc left right)).toReal := by
        rw [abs_of_nonneg (sub_nonneg.mpr hleftLeRight), hwidth]
        ring
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
    _ ≤ ∑ k ∈ Finset.range N,
        step * (eVariationOn f
          (Icc ((k : Real) * step)
            (((k : Real) + 1) * step))).toReal := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [zero_add] using hcell k (Finset.mem_range.mp hk)
    _ = step * ∑ k ∈ Finset.range N,
        (eVariationOn f
          (Icc ((k : Real) * step)
            (((k : Real) + 1) * step))).toReal := by
      rw [Finset.mul_sum]
    _ = step * (eVariationOn f
          (Icc (0 : Real) ((N : Real) * step))).toReal := by
      congr 1
      rw [← ENNReal.toReal_sum]
      · congr 1
        simpa only [Nat.cast_zero, zero_mul, Nat.cast_add, Nat.cast_one] using
          (eVariationOn.sum' f
            (I := fun k : Nat ↦ (k : Real) * step)
            (monotone_nat_of_le_succ fun k ↦ by
              exact mul_le_mul_of_nonneg_right
                (by exact_mod_cast Nat.le_succ k) hstep.le)
            (n := N))
      · intro k hk
        exact (hcellVariationFinite k (Finset.mem_range.mp hk))
    _ = (2 * Real.pi / (N : Real)) *
        (eVariationOn f (Icc (0 : Real) (2 * Real.pi))).toReal := by
      rw [htotal]

/-! ## Finite total variation of the squared-sinc profile -/

/-- Classical derivative of `sinc(x)^2` away from the removable point
`x = 0`. -/
def sincSquareTailDerivative (x : Real) : Real :=
  2 * Real.sin x * Real.cos x / x ^ 2 -
    2 * Real.sin x ^ 2 / x ^ 3

theorem hasDerivAt_sincSquareKernel_of_ne
    {x : Real} (hx : x ≠ 0) :
    HasDerivAt sincSquareKernel (sincSquareTailDerivative x) x := by
  have hquot := (Real.hasDerivAt_sin x).div (hasDerivAt_id x) hx
  have hsquare := hquot.pow 2
  have heq : sincSquareKernel =ᶠ[nhds x]
      (fun y : Real ↦ (Real.sin y / y) ^ 2) :=
    (continuousAt_id.eventually_ne hx).mono fun y hy ↦ by
      change y ≠ 0 at hy
      rw [sincSquareKernel, Real.sinc_of_ne_zero hy]
  have h := hsquare.congr_of_eventuallyEq heq
  apply h.congr_deriv
  change (2 : Real) * (Real.sin x / x) ^ (2 - 1) *
      ((Real.cos x * x - Real.sin x * 1) / x ^ 2) = _
  unfold sincSquareTailDerivative
  norm_num
  field_simp [hx]

theorem continuousOn_sincSquareTailDerivative_Ici_one :
    ContinuousOn sincSquareTailDerivative (Ici (1 : Real)) := by
  intro x hx
  change 1 ≤ x at hx
  have hx0 : x ≠ 0 := by linarith
  have hnum1 : ContinuousAt
      (fun y : Real ↦ 2 * Real.sin y * Real.cos y) x :=
    (continuousAt_const.mul Real.continuous_sin.continuousAt).mul
      Real.continuous_cos.continuousAt
  have hnum2 : ContinuousAt
      (fun y : Real ↦ 2 * Real.sin y ^ 2) x :=
    continuousAt_const.mul (Real.continuous_sin.continuousAt.pow 2)
  have hden2 : ContinuousAt (fun y : Real ↦ y ^ 2) x :=
    continuousAt_id.pow 2
  have hden3 : ContinuousAt (fun y : Real ↦ y ^ 3) x :=
    continuousAt_id.pow 3
  exact ((hnum1.div hden2 (pow_ne_zero 2 hx0)).sub
    (hnum2.div hden3 (pow_ne_zero 3 hx0))).continuousWithinAt

theorem abs_sincSquareTailDerivative_le
    {x : Real} (hx : 1 ≤ x) :
    |sincSquareTailDerivative x| ≤ 8 / (1 + x ^ 2) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hsin : |Real.sin x| ≤ 1 := Real.abs_sin_le_one x
  have hcos : |Real.cos x| ≤ 1 := Real.abs_cos_le_one x
  have hsq : 1 ≤ x ^ 2 := by nlinarith
  have hcube : 0 < x ^ 3 := by positivity
  have hsquarePos : 0 < x ^ 2 := by positivity
  have hfirst : |2 * Real.sin x * Real.cos x / x ^ 2| ≤ 2 / x ^ 2 := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos hsquarePos,
      abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
    apply div_le_div_of_nonneg_right _ hsquarePos.le
    nlinarith [mul_le_mul hsin hcos (abs_nonneg (Real.cos x)) zero_le_one]
  have hsecond : |2 * Real.sin x ^ 2 / x ^ 3| ≤ 2 / x ^ 3 := by
    rw [abs_div, abs_mul, abs_pow, abs_of_pos hcube,
      abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
    apply div_le_div_of_nonneg_right _ hcube.le
    nlinarith [sq_le_sq₀ (abs_nonneg (Real.sin x)) zero_le_one |>.2 hsin]
  calc
    |sincSquareTailDerivative x| ≤
        |2 * Real.sin x * Real.cos x / x ^ 2| +
          |2 * Real.sin x ^ 2 / x ^ 3| := by
      exact abs_sub _ _
    _ ≤ 2 / x ^ 2 + 2 / x ^ 3 := add_le_add hfirst hsecond
    _ ≤ 4 / x ^ 2 := by
      have hinvCube : 2 / x ^ 3 ≤ 2 / x ^ 2 := by
        apply div_le_div_of_nonneg_left (by norm_num) hsquarePos
        nlinarith
      calc
        2 / x ^ 2 + 2 / x ^ 3 ≤ 2 / x ^ 2 + 2 / x ^ 2 :=
          by simpa [add_comm] using add_le_add_right hinvCube (2 / x ^ 2)
        _ = 4 / x ^ 2 := by ring
    _ ≤ 8 / (1 + x ^ 2) := by
      rw [div_le_div_iff₀ hsquarePos (by positivity : 0 < 1 + x ^ 2)]
      nlinarith

theorem integrableOn_sincSquareTailDerivative_Ici_one :
    IntegrableOn sincSquareTailDerivative (Ici (1 : Real)) := by
  have hmajorant : Integrable (fun x : Real ↦ 8 / (1 + x ^ 2)) := by
    simpa only [div_eq_mul_inv] using
      integrable_inv_one_add_sq.const_mul (8 : Real)
  refine hmajorant.integrableOn.mono'
    (continuousOn_sincSquareTailDerivative_Ici_one.aestronglyMeasurable
      measurableSet_Ici) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
  rw [Real.norm_eq_abs]
  exact abs_sincSquareTailDerivative_le hx

/-- An integrable classical derivative controls total variation on a right
half-line.  This elementary lemma keeps the quantitative content in the
`L¹` norm, rather than replacing it by a pointwise derivative supremum. -/
theorem boundedVariationOn_Ici_of_hasDerivAt_integrableOn
    {f g : Real → Real} {c : Real}
    (hderiv : ∀ x ∈ Ici c, HasDerivAt f (g x) x)
    (hint : IntegrableOn g (Ici c)) :
    BoundedVariationOn f (Ici c) := by
  have hintAbs : IntegrableOn (fun x ↦ |g x|) (Ici c) := by
    change Integrable (fun x ↦ |g x|) (volume.restrict (Ici c))
    simpa only [Real.norm_eq_abs] using hint.norm
  have hbound : eVariationOn f (Ici c) ≤
      ENNReal.ofReal (∫ x in Ici c, |g x|) := by
    apply iSup_le
    rintro ⟨n, ⟨u, hu, hus⟩⟩
    have hsegment (i : Nat) (hi : i < n) :
        edist (f (u (i + 1))) (f (u i)) ≤
          ENNReal.ofReal (∫ x in u i..u (i + 1), |g x|) := by
      have hui : u i ≤ u (i + 1) := hu (Nat.le_succ i)
      have hintervalSubset : uIcc (u i) (u (i + 1)) ⊆ Ici c := by
        rw [uIcc_of_le hui]
        intro x hx
        exact (hus i).trans hx.1
      have hsegmentIntegrable : IntervalIntegrable g volume (u i) (u (i + 1)) :=
        (hint.mono_set hintervalSubset).intervalIntegrable
      have hftc : (∫ x in u i..u (i + 1), g x) =
          f (u (i + 1)) - f (u i) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x hx ↦ hderiv x (hintervalSubset hx)) hsegmentIntegrable
      rw [edist_dist, Real.dist_eq, ← hftc]
      exact ENNReal.ofReal_mono
        (intervalIntegral.abs_integral_le_integral_abs hui)
    calc
      ∑ i ∈ Finset.range n,
          edist (f (u (i + 1))) (f (u i)) ≤
          ∑ i ∈ Finset.range n,
            ENNReal.ofReal (∫ x in u i..u (i + 1), |g x|) := by
        exact Finset.sum_le_sum fun i hi ↦
          hsegment i (Finset.mem_range.mp hi)
      _ = ENNReal.ofReal (∑ i ∈ Finset.range n,
            ∫ x in u i..u (i + 1), |g x|) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro i hi
        exact intervalIntegral.integral_nonneg
          (hu (Nat.le_succ i)) fun _ _ ↦ abs_nonneg _
      _ = ENNReal.ofReal (∫ x in u 0..u n, |g x|) := by
        congr 1
        apply intervalIntegral.sum_integral_adjacent_intervals
        intro i hi
        have hui : u i ≤ u (i + 1) := hu (Nat.le_succ i)
        apply (hintAbs.mono_set ?_).intervalIntegrable
        rw [uIcc_of_le hui]
        intro x hx
        exact (hus i).trans hx.1
      _ ≤ ENNReal.ofReal (∫ x in Ici c, |g x|) := by
        apply ENNReal.ofReal_mono
        have h0n : u 0 ≤ u n := hu (Nat.zero_le n)
        rw [intervalIntegral.integral_of_le h0n]
        apply MeasureTheory.setIntegral_mono_set hintAbs
        · exact Eventually.of_forall fun _ ↦ abs_nonneg _
        · exact Eventually.of_forall fun x hx ↦ (hus 0).trans hx.1.le
  exact ne_top_of_le_ne_top (by simp) hbound

theorem boundedVariationOn_sincSquareKernel_Ici_one :
    BoundedVariationOn sincSquareKernel (Ici (1 : Real)) := by
  apply boundedVariationOn_Ici_of_hasDerivAt_integrableOn
    (g := sincSquareTailDerivative)
  · intro x hx
    exact hasDerivAt_sincSquareKernel_of_ne (by
      change 1 ≤ x at hx
      linarith)
  · exact integrableOn_sincSquareTailDerivative_Ici_one

/-- Left-half-line counterpart of
`boundedVariationOn_Ici_of_hasDerivAt_integrableOn`. -/
theorem boundedVariationOn_Iic_of_hasDerivAt_integrableOn
    {f g : Real → Real} {c : Real}
    (hderiv : ∀ x ∈ Iic c, HasDerivAt f (g x) x)
    (hint : IntegrableOn g (Iic c)) :
    BoundedVariationOn f (Iic c) := by
  have hintAbs : IntegrableOn (fun x ↦ |g x|) (Iic c) := by
    change Integrable (fun x ↦ |g x|) (volume.restrict (Iic c))
    simpa only [Real.norm_eq_abs] using hint.norm
  have hbound : eVariationOn f (Iic c) ≤
      ENNReal.ofReal (∫ x in Iic c, |g x|) := by
    apply iSup_le
    rintro ⟨n, ⟨u, hu, hus⟩⟩
    have hsegment (i : Nat) (hi : i < n) :
        edist (f (u (i + 1))) (f (u i)) ≤
          ENNReal.ofReal (∫ x in u i..u (i + 1), |g x|) := by
      have hui : u i ≤ u (i + 1) := hu (Nat.le_succ i)
      have hintervalSubset : uIcc (u i) (u (i + 1)) ⊆ Iic c := by
        rw [uIcc_of_le hui]
        intro x hx
        exact hx.2.trans (hus (i + 1))
      have hsegmentIntegrable : IntervalIntegrable g volume (u i) (u (i + 1)) :=
        (hint.mono_set hintervalSubset).intervalIntegrable
      have hftc : (∫ x in u i..u (i + 1), g x) =
          f (u (i + 1)) - f (u i) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x hx ↦ hderiv x (hintervalSubset hx)) hsegmentIntegrable
      rw [edist_dist, Real.dist_eq, ← hftc]
      exact ENNReal.ofReal_mono
        (intervalIntegral.abs_integral_le_integral_abs hui)
    calc
      ∑ i ∈ Finset.range n,
          edist (f (u (i + 1))) (f (u i)) ≤
          ∑ i ∈ Finset.range n,
            ENNReal.ofReal (∫ x in u i..u (i + 1), |g x|) := by
        exact Finset.sum_le_sum fun i hi ↦
          hsegment i (Finset.mem_range.mp hi)
      _ = ENNReal.ofReal (∑ i ∈ Finset.range n,
            ∫ x in u i..u (i + 1), |g x|) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro i hi
        exact intervalIntegral.integral_nonneg
          (hu (Nat.le_succ i)) fun _ _ ↦ abs_nonneg _
      _ = ENNReal.ofReal (∫ x in u 0..u n, |g x|) := by
        congr 1
        apply intervalIntegral.sum_integral_adjacent_intervals
        intro i hi
        have hui : u i ≤ u (i + 1) := hu (Nat.le_succ i)
        apply (hintAbs.mono_set ?_).intervalIntegrable
        rw [uIcc_of_le hui]
        intro x hx
        exact hx.2.trans (hus (i + 1))
      _ ≤ ENNReal.ofReal (∫ x in Iic c, |g x|) := by
        apply ENNReal.ofReal_mono
        have h0n : u 0 ≤ u n := hu (Nat.zero_le n)
        rw [intervalIntegral.integral_of_le h0n]
        apply MeasureTheory.setIntegral_mono_set hintAbs
        · exact Eventually.of_forall fun _ ↦ abs_nonneg _
        · exact Eventually.of_forall fun x hx ↦ hx.2.trans (hus n)
  exact ne_top_of_le_ne_top (by simp) hbound

theorem sincSquareTailDerivative_neg (x : Real) :
    sincSquareTailDerivative (-x) = -sincSquareTailDerivative x := by
  unfold sincSquareTailDerivative
  simp only [Real.sin_neg, Real.cos_neg]
  ring

theorem continuousOn_sincSquareTailDerivative_Iic_neg_one :
    ContinuousOn sincSquareTailDerivative (Iic (-1 : Real)) := by
  intro x hx
  change x ≤ -1 at hx
  have hx0 : x ≠ 0 := by linarith
  have hnum1 : ContinuousAt
      (fun y : Real ↦ 2 * Real.sin y * Real.cos y) x :=
    (continuousAt_const.mul Real.continuous_sin.continuousAt).mul
      Real.continuous_cos.continuousAt
  have hnum2 : ContinuousAt
      (fun y : Real ↦ 2 * Real.sin y ^ 2) x :=
    continuousAt_const.mul (Real.continuous_sin.continuousAt.pow 2)
  exact (((hnum1.div (continuousAt_id.pow 2) (pow_ne_zero 2 hx0)).sub
    (hnum2.div (continuousAt_id.pow 3)
      (pow_ne_zero 3 hx0)))).continuousWithinAt

theorem abs_sincSquareTailDerivative_le_of_le_neg_one
    {x : Real} (hx : x ≤ -1) :
    |sincSquareTailDerivative x| ≤ 8 / (1 + x ^ 2) := by
  have h := abs_sincSquareTailDerivative_le (x := -x) (by linarith)
  rw [sincSquareTailDerivative_neg, abs_neg] at h
  simpa only [neg_sq] using h

theorem integrableOn_sincSquareTailDerivative_Iic_neg_one :
    IntegrableOn sincSquareTailDerivative (Iic (-1 : Real)) := by
  have hmajorant : Integrable (fun x : Real ↦ 8 / (1 + x ^ 2)) := by
    simpa only [div_eq_mul_inv] using
      integrable_inv_one_add_sq.const_mul (8 : Real)
  refine hmajorant.integrableOn.mono'
    (continuousOn_sincSquareTailDerivative_Iic_neg_one.aestronglyMeasurable
      measurableSet_Iic) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Iic] with x hx
  rw [Real.norm_eq_abs]
  exact abs_sincSquareTailDerivative_le_of_le_neg_one hx

theorem boundedVariationOn_sincSquareKernel_Iic_neg_one :
    BoundedVariationOn sincSquareKernel (Iic (-1 : Real)) := by
  apply boundedVariationOn_Iic_of_hasDerivAt_integrableOn
    (g := sincSquareTailDerivative)
  · intro x hx
    exact hasDerivAt_sincSquareKernel_of_ne (by
      change x ≤ -1 at hx
      linarith)
  · exact integrableOn_sincSquareTailDerivative_Iic_neg_one

/-- A convenient global Lipschitz bound for the central part of `sinc²`.
It is obtained from the already proved finite-time kernel estimate at `T=2`;
the tail proof above is what avoids paying this Lipschitz constant globally. -/
theorem abs_sincSquareKernel_sub_le (x y : Real) :
    |sincSquareKernel x - sincSquareKernel y| ≤ 4 * |x - y| := by
  have h := abs_normalizedFiniteTimeResonanceKernel_sub_le
    x y (T := (2 : Real)) (by norm_num)
  rw [normalizedFiniteTimeResonanceKernel_eq_scaled x (by norm_num),
    normalizedFiniteTimeResonanceKernel_eq_scaled y (by norm_num)] at h
  norm_num only at h
  unfold normalizedSincSquareKernel at h
  rw [sincSquareMass_eq_pi] at h
  simp only [one_mul] at h
  have heq :
      Real.pi⁻¹ * sincSquareKernel x -
          Real.pi⁻¹ * sincSquareKernel y =
        (sincSquareKernel x - sincSquareKernel y) / Real.pi := by
    field_simp [Real.pi_ne_zero]
  rw [heq, abs_div, abs_of_pos Real.pi_pos] at h
  have hmul := (div_le_iff₀ Real.pi_pos).mp h
  calc
    |sincSquareKernel x - sincSquareKernel y| ≤
        (4 / Real.pi) * |x - y| * Real.pi := hmul
    _ = 4 * |x - y| := by field_simp [Real.pi_ne_zero]

theorem lipschitzWith_sincSquareKernel :
    LipschitzWith (4 : NNReal) sincSquareKernel := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [NNReal.coe_ofNat, Real.dist_eq] using
    abs_sincSquareKernel_sub_le x y

theorem boundedVariationOn_sincSquareKernel_Icc_neg_one_one :
    BoundedVariationOn sincSquareKernel (Icc (-1 : Real) 1) := by
  have h := lipschitzWith_sincSquareKernel.comp_boundedVariationOn
    (BoundedVariationOn.id_Icc (-1 : Real) 1)
  simpa [Function.comp_def] using h

theorem boundedVariationOn_union_of_ordered
    {f : Real → Real} {s t : Set Real} {x : Real}
    (hs : BoundedVariationOn f s) (ht : BoundedVariationOn f t)
    (hgreatest : IsGreatest s x) (hleast : IsLeast t x) :
    BoundedVariationOn f (s ∪ t) := by
  rw [BoundedVariationOn, eVariationOn.union f hgreatest hleast]
  exact ENNReal.add_ne_top.mpr ⟨hs, ht⟩

/-- The squared-sinc profile has finite total variation on the real line.
This is the analytic fact that changes the collision-grid cost from `T²/N`
to `T/N`. -/
theorem boundedVariationOn_sincSquareKernel_univ :
    BoundedVariationOn sincSquareKernel (Set.univ : Set Real) := by
  have hleftCenter : BoundedVariationOn sincSquareKernel (Iic (1 : Real)) := by
    rw [show Iic (1 : Real) = Iic (-1 : Real) ∪ Icc (-1 : Real) 1 by
      ext x
      simp only [mem_Iic, mem_union, mem_Icc]
      constructor
      · intro hx
        by_cases hxm : x ≤ -1
        · exact Or.inl hxm
        · exact Or.inr ⟨le_of_not_ge hxm, hx⟩
      · exact fun hx ↦ hx.elim (fun h ↦ h.trans (by norm_num)) (fun h ↦ h.2)]
    apply boundedVariationOn_union_of_ordered
      boundedVariationOn_sincSquareKernel_Iic_neg_one
      boundedVariationOn_sincSquareKernel_Icc_neg_one_one
    · exact ⟨by simp, fun y hy ↦ hy⟩
    · exact ⟨by simp, fun y hy ↦ hy.1⟩
  rw [show (Set.univ : Set Real) = Iic (1 : Real) ∪ Ici (1 : Real) by
    ext x
    simp only [mem_univ, mem_union, mem_Iic, mem_Ici, true_iff]
    exact le_total x 1]
  apply boundedVariationOn_union_of_ordered hleftCenter
    boundedVariationOn_sincSquareKernel_Ici_one
  · exact ⟨by simp, fun y hy ↦ hy⟩
  · exact ⟨by simp, fun y hy ↦ hy⟩

/-- Finite real total-variation constant of the universal `sinc²` profile. -/
def sincSquareTotalVariation : Real :=
  (eVariationOn sincSquareKernel (Set.univ : Set Real)).toReal

theorem sincSquareTotalVariation_nonneg :
    0 ≤ sincSquareTotalVariation := ENNReal.toReal_nonneg

theorem eVariationOn_sincSquareKernel_univ_eq :
    eVariationOn sincSquareKernel (Set.univ : Set Real) =
      ENNReal.ofReal sincSquareTotalVariation := by
  exact (ENNReal.ofReal_toReal
    boundedVariationOn_sincSquareKernel_univ).symm

/-- Monotone reparametrization cannot create more variation than is present
in the full target profile. -/
theorem eVariationOn_comp_le_univ_of_monotoneOn
    {f φ : Real → Real} {s : Set Real}
    (hφ : MonotoneOn φ s) :
    eVariationOn (f ∘ φ) s ≤ eVariationOn f Set.univ := by
  apply iSup_le
  rintro ⟨n, ⟨u, hu, hus⟩⟩
  simpa only [Function.comp_apply] using
    (eVariationOn.sum_le (f := f) (s := Set.univ) (n := n)
      (u := φ ∘ u)
      (fun i j hij ↦ hφ (hus i) (hus j) (hu hij))
      (fun _ ↦ Set.mem_univ _))

theorem lipschitzWith_const_mul (A : Real) :
    LipschitzWith ⟨|A|, abs_nonneg A⟩ (fun x : Real ↦ A * x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul]
  rfl

/-- On every monotone phase chart, the physical finite-time peak has total
variation at most `T/(2π)` times the universal `sinc²` variation. -/
theorem eVariationOn_normalizedFiniteTimeResonanceKernel_comp_le
    {phase : Real → Real} {s : Set Real} {T : Real} (hT : 0 < T)
    (hphase : MonotoneOn phase s) :
    eVariationOn
        (fun x ↦ normalizedFiniteTimeResonanceKernel (phase x) T) s ≤
      ENNReal.ofReal (T / (2 * Real.pi) * sincSquareTotalVariation) := by
  let scale : Real := T / 2
  let amplitude : Real := T / (2 * Real.pi)
  let amplitudeNN : NNReal := ⟨|amplitude|, abs_nonneg amplitude⟩
  let reparam : Real → Real := fun x ↦ scale * phase x
  have hscale : 0 ≤ scale := by
    dsimp [scale]
    positivity
  have hamplitude : 0 ≤ amplitude := by
    dsimp [amplitude]
    positivity
  have hreparam : MonotoneOn reparam s := by
    intro x hx y hy hxy
    exact mul_le_mul_of_nonneg_left (hphase hx hy hxy) hscale
  have hcomp : eVariationOn (sincSquareKernel ∘ reparam) s ≤
      eVariationOn sincSquareKernel Set.univ :=
    eVariationOn_comp_le_univ_of_monotoneOn hreparam
  have hmul : eVariationOn
      (fun x ↦ amplitude * sincSquareKernel (reparam x)) s ≤
      (amplitudeNN : ENNReal) *
        eVariationOn (sincSquareKernel ∘ reparam) s := by
    simpa [Function.comp_def, amplitudeNN] using
      ((lipschitzWith_const_mul amplitude).lipschitzOnWith
        |>.comp_eVariationOn_le (s := s)
          (g := sincSquareKernel ∘ reparam) (mapsTo_univ _ _))
  have hpointwise : EqOn
      (fun x ↦ normalizedFiniteTimeResonanceKernel (phase x) T)
      (fun x ↦ amplitude * sincSquareKernel (reparam x)) s := by
    intro x _hx
    change normalizedFiniteTimeResonanceKernel (phase x) T = _
    rw [normalizedFiniteTimeResonanceKernel_eq_scaled (phase x) hT]
    unfold normalizedSincSquareKernel
    rw [sincSquareMass_eq_pi]
    dsimp [amplitude, scale, reparam]
    ring
  rw [eVariationOn.congr hpointwise]
  calc
    eVariationOn
        (fun x ↦ amplitude * sincSquareKernel (reparam x)) s ≤
        (amplitudeNN : ENNReal) *
          eVariationOn (sincSquareKernel ∘ reparam) s := hmul
    _ ≤ (amplitudeNN : ENNReal) *
          eVariationOn sincSquareKernel Set.univ := by
      exact mul_le_mul_of_nonneg_left hcomp zero_le
    _ = ENNReal.ofReal
        (T / (2 * Real.pi) * sincSquareTotalVariation) := by
      rw [eVariationOn_sincSquareKernel_univ_eq]
      have hampNN : (amplitudeNN : ENNReal) =
          ENNReal.ofReal amplitude := by
        rw [ENNReal.coe_nnreal_eq amplitudeNN]
        congr 1
        dsimp [amplitudeNN]
        exact abs_of_nonneg hamplitude
      rw [hampNN, ← ENNReal.ofReal_mul hamplitude]

/-! ## A linearly varying marked collision chart -/

def localCollisionLinearVariationConstant
    (markBound markSlope a b : Real) : Real :=
  markBound * sincSquareTotalVariation + markSlope * (b - a)

theorem localCollisionLinearVariationConstant_nonneg
    {markBound markSlope a b : Real}
    (hmarkBound : 0 ≤ markBound) (hmarkSlope : 0 ≤ markSlope)
    (hab : a ≤ b) :
    0 ≤ localCollisionLinearVariationConstant
      markBound markSlope a b := by
  unfold localCollisionLinearVariationConstant
  exact add_nonneg
    (mul_nonneg hmarkBound sincSquareTotalVariation_nonneg)
    (mul_nonneg hmarkSlope (sub_nonneg.mpr hab))

theorem eVariationOn_mark_le_of_lipschitz
    {mark : Real → Real} {a b markSlope : Real}
    (_hab : a ≤ b) (hmarkSlope : 0 ≤ markSlope)
    (hmarkLip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      |mark x - mark y| ≤ markSlope * |x - y|) :
    eVariationOn mark (Icc a b) ≤
      ENNReal.ofReal (markSlope * (b - a)) := by
  let slopeNN : NNReal := ⟨markSlope, hmarkSlope⟩
  have hlip : LipschitzOnWith slopeNN mark (Icc a b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    change |mark x - mark y| ≤ markSlope * |x - y|
    simpa only [Real.dist_eq] using
      hmarkLip x hx y hy
  have hvar := hlip.comp_eVariationOn_le (g := id)
    (s := Icc a b) (mapsTo_id (Icc a b))
  calc
    eVariationOn mark (Icc a b) ≤
        (slopeNN : ENNReal) * eVariationOn id (Icc a b) := by
      simpa [Function.comp_def] using hvar
    _ = ENNReal.ofReal (markSlope * (b - a)) := by
      rw [eVariationOn_id_Icc, ENNReal.coe_nnreal_eq slopeNN]
      change ENNReal.ofReal markSlope * ENNReal.ofReal (b - a) = _
      rw [← ENNReal.ofReal_mul hmarkSlope]

/-- Product variation for a marked finite-time peak on a monotone transverse
chart.  Both contributions are linear in `T`: peak variation times mark
height, and peak height times mark variation. -/
theorem eVariationOn_finiteTimeMarkedCollisionIntegrand_le_linear
    {mismatch mark : Real → Real}
    {a b T markBound markSlope : Real}
    (hab : a ≤ b) (hT : 0 < T)
    (hmarkBound : 0 ≤ markBound) (hmarkSlope : 0 ≤ markSlope)
    (hmarkBoundOn : ∀ x ∈ Icc a b, |mark x| ≤ markBound)
    (hmarkLipOn : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      |mark x - mark y| ≤ markSlope * |x - y|)
    (hmismatchMonotone : MonotoneOn mismatch (Icc a b)) :
    eVariationOn
        (finiteTimeMarkedCollisionIntegrand mismatch mark T) (Icc a b) ≤
      ENNReal.ofReal
        (T / (2 * Real.pi) *
          localCollisionLinearVariationConstant markBound markSlope a b) := by
  let kernel : Real → Real := fun x ↦
    normalizedFiniteTimeResonanceKernel (mismatch x) T
  let height : Real := T / (2 * Real.pi)
  have hheight : 0 ≤ height := by
    dsimp [height]
    positivity
  have hkernelVariation : eVariationOn kernel (Icc a b) ≤
      ENNReal.ofReal (height * sincSquareTotalVariation) := by
    simpa only [kernel, height] using
      eVariationOn_normalizedFiniteTimeResonanceKernel_comp_le
        hT hmismatchMonotone
  have hmarkVariation : eVariationOn mark (Icc a b) ≤
      ENNReal.ofReal (markSlope * (b - a)) :=
    eVariationOn_mark_le_of_lipschitz hab hmarkSlope hmarkLipOn
  have hmarkEnorm : ∀ x ∈ Icc a b,
      ‖mark x‖ₑ ≤ ENNReal.ofReal markBound := by
    intro x hx
    rw [← ofReal_norm, Real.norm_eq_abs]
    exact ENNReal.ofReal_mono (hmarkBoundOn x hx)
  have hkernelEnorm : ∀ x ∈ Icc a b,
      ‖kernel x‖ₑ ≤ ENNReal.ofReal height := by
    intro x _hx
    rw [← ofReal_norm, Real.norm_eq_abs,
      abs_of_nonneg (normalizedFiniteTimeResonanceKernel_nonneg
        (mismatch x) T)]
    exact ENNReal.ofReal_mono
      (normalizedFiniteTimeResonanceKernel_le_height (mismatch x) hT)
  have hproduct := eVariation_mul_le
    (s := Icc a b) (f := mark) (g := kernel)
    hmarkEnorm hkernelEnorm
  change eVariationOn (mark * kernel) (Icc a b) ≤ _
  calc
    eVariationOn (mark * kernel) (Icc a b) ≤
        ENNReal.ofReal markBound * eVariationOn kernel (Icc a b) +
          ENNReal.ofReal height * eVariationOn mark (Icc a b) := hproduct
    _ ≤ ENNReal.ofReal markBound *
          ENNReal.ofReal (height * sincSquareTotalVariation) +
        ENNReal.ofReal height *
          ENNReal.ofReal (markSlope * (b - a)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hkernelVariation zero_le)
        (mul_le_mul_of_nonneg_left hmarkVariation zero_le)
    _ = ENNReal.ofReal
        (T / (2 * Real.pi) *
          localCollisionLinearVariationConstant markBound markSlope a b) := by
      rw [← ENNReal.ofReal_mul hmarkBound,
        ← ENNReal.ofReal_mul hheight]
      rw [← ENNReal.ofReal_add
        (mul_nonneg hmarkBound
          (mul_nonneg hheight sincSquareTotalVariation_nonneg))
        (mul_nonneg hheight
          (mul_nonneg hmarkSlope (sub_nonneg.mpr hab)))]
      apply congrArg ENNReal.ofReal
      dsimp [height, localCollisionLinearVariationConstant]
      ring

theorem eVariationOn_clampedCollision_eq_local
    {mismatch mark : Real → Real} {a b T : Real}
    (hab : a ≤ b) (ha0 : 0 ≤ a) (hb2pi : b ≤ 2 * Real.pi)
    (hmarkLeft : mark a = 0) (hmarkRight : mark b = 0) :
    eVariationOn
        (finiteTimeMarkedCollisionIntegrand mismatch
          (clampedChartMark a b hab mark) T)
        (Icc (0 : Real) (2 * Real.pi)) =
      eVariationOn
        (finiteTimeMarkedCollisionIntegrand mismatch mark T)
        (Icc a b) := by
  let full : Real → Real :=
    finiteTimeMarkedCollisionIntegrand mismatch
      (clampedChartMark a b hab mark) T
  let localFn : Real → Real :=
    finiteTimeMarkedCollisionIntegrand mismatch mark T
  have hzeroLeft : eVariationOn full (Icc (0 : Real) a) = 0 := by
    rw [eVariationOn.congr (g := fun _ : Real ↦ 0) (by
      intro x hx
      dsimp [full, finiteTimeMarkedCollisionIntegrand]
      rw [clampedChartMark_eq_zero_of_le_left
        hab hmarkLeft hx.2]
      simp)]
    change eVariationOn (0 : Real → Real) (Icc (0 : Real) a) = 0
    apply le_antisymm
    · apply iSup_le
      rintro ⟨n, ⟨u, hu, hus⟩⟩
      simp
    · exact zero_le
  have hzeroRight :
      eVariationOn full (Icc b (2 * Real.pi)) = 0 := by
    rw [eVariationOn.congr (g := fun _ : Real ↦ 0) (by
      intro x hx
      dsimp [full, finiteTimeMarkedCollisionIntegrand]
      rw [clampedChartMark_eq_zero_of_right_le
        hab hmarkRight hx.1]
      simp)]
    change eVariationOn (0 : Real → Real)
      (Icc b (2 * Real.pi)) = 0
    apply le_antisymm
    · apply iSup_le
      rintro ⟨n, ⟨u, hu, hus⟩⟩
      simp
    · exact zero_le
  have hlocal : eVariationOn full (Icc a b) =
      eVariationOn localFn (Icc a b) := by
    apply eVariationOn.congr
    intro x hx
    dsimp [full, localFn, finiteTimeMarkedCollisionIntegrand]
    rw [clampedChartMark_eq_of_mem hab mark hx]
  have hsplitRight := eVariationOn.Icc_add_Icc
    (f := full) (s := Set.univ) hab hb2pi (Set.mem_univ b)
  simp only [Set.univ_inter] at hsplitRight
  have hsplitLeft := eVariationOn.Icc_add_Icc
    (f := full) (s := Set.univ) ha0 (hab.trans hb2pi) (Set.mem_univ a)
  simp only [Set.univ_inter] at hsplitLeft
  rw [hzeroRight, add_zero] at hsplitRight
  rw [hzeroLeft, zero_add, ← hsplitRight, hlocal] at hsplitLeft
  exact hsplitLeft.symm

/-- Explicit `O(T/N)` quadrature error on any monotone local chart. -/
theorem abs_localFourierGridCollisionQuadrature_sub_integral_le_linearTime
    (N : Nat) [NeZero N]
    {mismatch mark : Real → Real} {a b T : Real}
    (hab : a ≤ b) (ha0 : 0 ≤ a) (hb2pi : b ≤ 2 * Real.pi)
    {markBound markSlope : Real}
    (hT : 0 < T) (hmarkBound : 0 ≤ markBound)
    (hmarkSlope : 0 ≤ markSlope)
    (hmarkContinuous : Continuous mark)
    (hmismatchContinuous : Continuous mismatch)
    (hmarkLeft : mark a = 0) (hmarkRight : mark b = 0)
    (hmarkBoundOn : ∀ x ∈ Icc a b, |mark x| ≤ markBound)
    (hmarkLipOn : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      |mark x - mark y| ≤ markSlope * |x - y|)
    (hmismatchMonotone : MonotoneOn mismatch (Icc a b)) :
    |localFourierGridCollisionQuadrature N mismatch mark a b hab T -
      ∫ x in a..b,
        finiteTimeMarkedCollisionIntegrand mismatch mark T x| ≤
      localCollisionLinearVariationConstant markBound markSlope a b *
        (1 + T) / (N : Real) := by
  let full : Real → Real :=
    finiteTimeMarkedCollisionIntegrand mismatch
      (clampedChartMark a b hab mark) T
  let constant : Real :=
    localCollisionLinearVariationConstant markBound markSlope a b
  have hconstant : 0 ≤ constant :=
    localCollisionLinearVariationConstant_nonneg
      hmarkBound hmarkSlope hab
  have hvariationLocal :=
    eVariationOn_finiteTimeMarkedCollisionIntegrand_le_linear
      hab hT hmarkBound hmarkSlope hmarkBoundOn hmarkLipOn
      hmismatchMonotone
  have hvariationFull : eVariationOn full
      (Icc (0 : Real) (2 * Real.pi)) ≤
        ENNReal.ofReal (T / (2 * Real.pi) * constant) := by
    rw [eVariationOn_clampedCollision_eq_local
      hab ha0 hb2pi hmarkLeft hmarkRight]
    simpa only [constant] using hvariationLocal
  have hvariationFullFinite : BoundedVariationOn full
      (Icc (0 : Real) (2 * Real.pi)) :=
    ne_top_of_le_ne_top (by simp) hvariationFull
  have hvariationReal :
      (eVariationOn full (Icc (0 : Real) (2 * Real.pi))).toReal ≤
        T / (2 * Real.pi) * constant := by
    have h := ENNReal.toReal_mono (by simp) hvariationFull
    rw [ENNReal.toReal_ofReal (mul_nonneg
      (by positivity : 0 ≤ T / (2 * Real.pi)) hconstant)] at h
    exact h
  have hfullContinuous : ContinuousOn full
      (Icc (0 : Real) (2 * Real.pi)) := by
    exact ((continuous_clampedChartMark hab hmarkContinuous).mul
      ((continuous_normalizedFiniteTimeResonanceKernel hT).comp
        hmismatchContinuous)).continuousOn
  have hfullEndpoint : full 0 = full (2 * Real.pi) := by
    dsimp [full, finiteTimeMarkedCollisionIntegrand]
    rw [clampedChartMark_eq_zero_of_le_left hab hmarkLeft ha0,
      clampedChartMark_eq_zero_of_right_le hab hmarkRight hb2pi]
    simp
  rw [← intervalIntegral_clampedCollision_eq_local
    hab ha0 hb2pi hmarkLeft hmarkRight]
  have hquadrature :=
    abs_fourierGrid_sum_sub_integral_le_of_boundedVariation
      N full hfullEndpoint hfullContinuous hvariationFullFinite
  change |(2 * Real.pi / (N : Real)) *
      ∑ mode : Site N, full (gridWaveNumber N mode) -
        ∫ x in (0 : Real)..(2 * Real.pi), full x| ≤ _
  calc
    |(2 * Real.pi / (N : Real)) *
        ∑ mode : Site N, full (gridWaveNumber N mode) -
          ∫ x in (0 : Real)..(2 * Real.pi), full x| ≤
        (2 * Real.pi / (N : Real)) *
          (eVariationOn full
            (Icc (0 : Real) (2 * Real.pi))).toReal := hquadrature
    _ ≤ (2 * Real.pi / (N : Real)) *
          (T / (2 * Real.pi) * constant) := by
      exact mul_le_mul_of_nonneg_left hvariationReal (by positivity)
    _ = constant * T / (N : Real) := by
      field_simp [Real.pi_ne_zero]
    _ ≤ constant * (1 + T) / (N : Real) := by
      have hN : (0 : Real) < (N : Real) := by
        exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
      apply div_le_div_of_nonneg_right _ hN.le
      exact mul_le_mul_of_nonneg_left (by linarith) hconstant

/-- Construct the formerly abstract linear-time quadrature certificate from
ordinary deterministic chart data. -/
def monotoneLocalCollisionQuadratureCertificate
    {mismatch mark : Real → Real} {a b : Real}
    (hab : a ≤ b) (ha0 : 0 ≤ a) (hb2pi : b ≤ 2 * Real.pi)
    {markBound markSlope : Real}
    (hmarkBound : 0 ≤ markBound) (hmarkSlope : 0 ≤ markSlope)
    (hmarkContinuous : Continuous mark)
    (hmismatchContinuous : Continuous mismatch)
    (hmarkLeft : mark a = 0) (hmarkRight : mark b = 0)
    (hmarkBoundOn : ∀ x ∈ Icc a b, |mark x| ≤ markBound)
    (hmarkLipOn : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      |mark x - mark y| ≤ markSlope * |x - y|)
    (hmismatchMonotone : MonotoneOn mismatch (Icc a b)) :
    LinearTimeLocalCollisionQuadratureCertificate
      mismatch mark a b hab where
  constant := localCollisionLinearVariationConstant
    markBound markSlope a b
  constant_nonneg := localCollisionLinearVariationConstant_nonneg
    hmarkBound hmarkSlope hab
  error_bound := by
    intro N _ T hT
    exact abs_localFourierGridCollisionQuadrature_sub_integral_le_linearTime
      N hab ha0 hb2pi hT hmarkBound hmarkSlope hmarkContinuous
        hmismatchContinuous hmarkLeft hmarkRight hmarkBoundOn
        hmarkLipOn hmismatchMonotone

/-! ## The actual rooted Umklapp chart -/

/-- The explicit rooted FPUT tent mark satisfies the formerly abstract
linear-time quadrature certificate.  Thus the actual local collision
diagonal needs only `T_N/N → 0`, not `T_N²/N → 0`. -/
noncomputable def actualRootedLinearTimeLocalCollisionQuadratureCertificate
    {N₀ : Nat} [NeZero N₀] (alpha : Real)
    (out : ActualInteractionBranchMode N₀)
    (diagram : ActiveFeedbackEffectiveDiagramImage N₀ out)
    (hdisc : 0 < umklappTransverseDiscriminant
      (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram))
    (ha0 : 0 ≤ canonicalDiagramLocalLeft diagram)
    (hb2pi : canonicalDiagramLocalRight diagram ≤ 2 * Real.pi) :
    LinearTimeLocalCollisionQuadratureCertificate
      (canonicalDiagramUmklappMismatch diagram)
      (actualRootedLocalCollisionMark alpha out diagram)
      (canonicalDiagramLocalLeft diagram)
      (canonicalDiagramLocalRight diagram)
      (canonicalPositiveGeometry_principalZone
        (canonicalDiagramGridK₀_pos diagram)
        (canonicalDiagramGridK₀_lt_two_pi diagram)
        (canonicalDiagramGridK₁_pos diagram)
        (canonicalDiagramGridK₁_lt_two_pi diagram) hdisc).interval_lt.le := by
  let geometry := canonicalPositiveGeometry_principalZone
    (canonicalDiagramGridK₀_pos diagram)
    (canonicalDiagramGridK₀_lt_two_pi diagram)
    (canonicalDiagramGridK₁_pos diagram)
    (canonicalDiagramGridK₁_lt_two_pi diagram) hdisc
  let regularity := actualRootedLocalMarkRegularity
    alpha out diagram hdisc
  apply monotoneLocalCollisionQuadratureCertificate
    geometry.interval_lt.le ha0 hb2pi
    regularity.markBound_nonneg regularity.markSlope_nonneg
    (continuous_actualRootedLocalCollisionMark alpha out diagram hdisc)
    (continuous_canonicalDiagramUmklappMismatch diagram)
    regularity.mark_left_zero regularity.mark_right_zero
    regularity.mark_bound regularity.mark_lipschitz
  exact geometry.mismatch_strictMono.monotoneOn

/-- Fully unconditional (within the explicit local chart) actual collision
diagonal at the optimal linear-time scale. -/
theorem actualRootedLocalFourierGridCollision_tendsto_rate_of_linearTime_unconditional
    {N₀ : Nat} [NeZero N₀] (alpha : Real)
    (out : ActualInteractionBranchMode N₀)
    (diagram : ActiveFeedbackEffectiveDiagramImage N₀ out)
    (hdisc : 0 < umklappTransverseDiscriminant
      (canonicalDiagramGridK₀ diagram) (canonicalDiagramGridK₁ diagram))
    (ha0 : 0 ≤ canonicalDiagramLocalLeft diagram)
    (hb2pi : canonicalDiagramLocalRight diagram ≤ 2 * Real.pi)
    (time : Nat → Real) (htimePos : ∀ n, 0 < time n)
    (htime : Tendsto time atTop atTop)
    (hlinear : Tendsto
      (fun n : Nat ↦ time n / (((n + 1 : Nat) : Real)))
      atTop (nhds 0)) :
    Tendsto
      (fun n : Nat ↦
        localFourierGridCollisionQuadrature (n + 1)
          (canonicalDiagramUmklappMismatch diagram)
          (actualRootedLocalCollisionMark alpha out diagram)
          (canonicalDiagramLocalLeft diagram)
          (canonicalDiagramLocalRight diagram)
          (canonicalPositiveGeometry_principalZone
            (canonicalDiagramGridK₀_pos diagram)
            (canonicalDiagramGridK₀_lt_two_pi diagram)
            (canonicalDiagramGridK₁_pos diagram)
            (canonicalDiagramGridK₁_lt_two_pi diagram) hdisc).interval_lt.le
          (time n))
      atTop (nhds (actualRootedLocalCollisionRate alpha out diagram)) := by
  exact actualRootedLocalFourierGridCollision_tendsto_rate_of_linearTime
    alpha out diagram hdisc
      (actualRootedLinearTimeLocalCollisionQuadratureCertificate
        alpha out diagram hdisc ha0 hb2pi)
      time htimePos htime hlinear

end

end ArchonPhysics.FPUTFiniteTimeCollisionBVQuadrature
