import ArchonPhysics.SincSquareMassExact
import ArchonPhysics.UniformCollisionDensityTransfer

/-!
# Quantitative regularity of the finite-time resonance kernel

For positive observation time `T`, the normalized finite-time resonance
kernel is bounded by `T / (2*pi)` and is Lipschitz in phase mismatch with
constant `T^2 / pi`.  The constants are deliberately elementary rather than
sharp.  Their purpose is to expose the rate required when a discrete
empirical measure is tested against a peak whose height and slope grow with
time.
-/

namespace ArchonPhysics.ResonanceKernelLipschitz

open scoped Interval NNReal
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.NonresonantOscillatoryGain
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.SincSquareMassExact
open ArchonPhysics.UniformCollisionDensityTransfer

noncomputable section

/-- Unit-modulus complex phases are one-Lipschitz in their real phase. -/
theorem norm_exp_phase_sub_le (Omega Xi s : Real) :
    ‖Complex.exp ((Complex.I * Omega) * s) -
        Complex.exp ((Complex.I * Xi) * s)‖ <=
      |Omega - Xi| * |s| := by
  simp only [mul_assoc, ← Complex.ofReal_mul]
  have hfactor :
      Complex.exp (Complex.I * ((Omega * s : Real) : Complex)) -
          Complex.exp (Complex.I * ((Xi * s : Real) : Complex)) =
        Complex.exp (Complex.I * ((Xi * s : Real) : Complex)) *
          (Complex.exp (Complex.I * (((Omega - Xi) * s : Real) : Complex)) - 1) := by
    rw [mul_sub, mul_one, <- Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hfactor, norm_mul]
  have hunit :
      ‖Complex.exp (Complex.I * ((Xi * s : Real) : Complex))‖ = 1 :=
    Complex.norm_exp_I_mul_ofReal (Xi * s)
  rw [hunit, one_mul]
  have hphase := Real.norm_exp_I_mul_ofReal_sub_one_le
    (x := (Omega - Xi) * s)
  calc
    ‖Complex.exp (Complex.I * (((Omega - Xi) * s : Real) : Complex)) - 1‖ <=
        ‖(Omega - Xi) * s‖ := hphase
    _ = |Omega - Xi| * |s| := by
      rw [Real.norm_eq_abs, abs_mul]

/-- The oscillatory integral is uniformly Lipschitz in mismatch on a finite
positive time interval. -/
theorem norm_oscillatoryIntegral_sub_le
    (Omega Xi : Real) {T : Real} (hT : 0 < T) :
    ‖oscillatoryIntegral Omega T - oscillatoryIntegral Xi T‖ <=
      T ^ 2 * |Omega - Xi| := by
  have hOmegaLinear : Continuous
      (fun s : Real => (Complex.I * (Omega : Complex)) * (s : Complex)) :=
    continuous_const.mul Complex.continuous_ofReal
  have hXiLinear : Continuous
      (fun s : Real => (Complex.I * (Xi : Complex)) * (s : Complex)) :=
    continuous_const.mul Complex.continuous_ofReal
  have hOmega : IntervalIntegrable
      (fun s : Real => Complex.exp ((Complex.I * Omega) * s))
        MeasureTheory.volume 0 T :=
    (Complex.continuous_exp.comp hOmegaLinear).intervalIntegrable
      (μ := MeasureTheory.volume) 0 T
  have hXi : IntervalIntegrable
      (fun s : Real => Complex.exp ((Complex.I * Xi) * s))
        MeasureTheory.volume 0 T :=
    (Complex.continuous_exp.comp hXiLinear).intervalIntegrable
      (μ := MeasureTheory.volume) 0 T
  rw [oscillatoryIntegral, oscillatoryIntegral,
    <- intervalIntegral.integral_sub hOmega hXi]
  calc
    ‖∫ s in (0 : Real)..T,
        Complex.exp ((Complex.I * Omega) * s) -
          Complex.exp ((Complex.I * Xi) * s)‖ <=
        (|Omega - Xi| * T) * |T - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      have hsIcc : s ∈ Set.Icc (0 : Real) T := by
        simpa only [Set.uIcc_of_le hT.le] using Set.uIoc_subset_uIcc hs
      have hsabs : |s| <= T := by
        rw [abs_of_nonneg hsIcc.1]
        exact hsIcc.2
      exact (norm_exp_phase_sub_le Omega Xi s).trans
        (mul_le_mul_of_nonneg_left hsabs (abs_nonneg _))
    _ = T ^ 2 * |Omega - Xi| := by
      rw [sub_zero, abs_of_pos hT]
      ring

/-- The unnormalized resonance weight never exceeds the observation time. -/
theorem finiteTimeResonanceWeight_le_time
    (Omega : Real) {T : Real} (hT : 0 < T) :
    finiteTimeResonanceWeight Omega T <= T := by
  rw [finiteTimeResonanceWeight, if_pos hT]
  apply (div_le_iff₀ hT).2
  have hnorm := norm_oscillatoryIntegral_le_abs_time Omega T
  rw [abs_of_pos hT] at hnorm
  nlinarith [norm_nonneg (oscillatoryIntegral Omega T)]

/-- Difference of unnormalized finite-time weights has an explicit quadratic
Lipschitz constant. -/
theorem abs_finiteTimeResonanceWeight_sub_le
    (Omega Xi : Real) {T : Real} (hT : 0 < T) :
    |finiteTimeResonanceWeight Omega T -
        finiteTimeResonanceWeight Xi T| <=
      2 * T ^ 2 * |Omega - Xi| := by
  let a := ‖oscillatoryIntegral Omega T‖
  let b := ‖oscillatoryIntegral Xi T‖
  have ha : a <= T := by
    simpa [a, abs_of_pos hT] using
      norm_oscillatoryIntegral_le_abs_time Omega T
  have hb : b <= T := by
    simpa [b, abs_of_pos hT] using
      norm_oscillatoryIntegral_le_abs_time Xi T
  have hab : |a - b| <= T ^ 2 * |Omega - Xi| := by
    exact (abs_norm_sub_norm_le
      (oscillatoryIntegral Omega T) (oscillatoryIntegral Xi T)).trans
      (norm_oscillatoryIntegral_sub_le Omega Xi hT)
  have hsquare : |a ^ 2 - b ^ 2| <=
      (2 * T) * (T ^ 2 * |Omega - Xi|) := by
    rw [show a ^ 2 - b ^ 2 = (a + b) * (a - b) by ring,
      abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact mul_le_mul (by linarith) hab (abs_nonneg _) (by positivity)
  simp only [finiteTimeResonanceWeight, if_pos hT]
  change |a ^ 2 / T - b ^ 2 / T| <= 2 * T ^ 2 * |Omega - Xi|
  rw [<- sub_div, abs_div, abs_of_pos hT]
  calc
    |a ^ 2 - b ^ 2| / T <=
        ((2 * T) * (T ^ 2 * |Omega - Xi|)) / T :=
      div_le_div_of_nonneg_right hsquare hT.le
    _ = 2 * T ^ 2 * |Omega - Xi| := by
      field_simp [hT.ne']

/-- The normalized peak has height at most `T/(2*pi)`. -/
theorem normalizedFiniteTimeResonanceKernel_le_height
    (Omega : Real) {T : Real} (hT : 0 < T) :
    normalizedFiniteTimeResonanceKernel Omega T <=
      T / (2 * Real.pi) := by
  rw [normalizedFiniteTimeResonanceKernel_eq_div_two_pi]
  exact div_le_div_of_nonneg_right
    (finiteTimeResonanceWeight_le_time Omega hT)
    (mul_nonneg zero_le_two Real.pi_pos.le)

theorem abs_normalizedFiniteTimeResonanceKernel_le_height
    (Omega : Real) {T : Real} (hT : 0 < T) :
    |normalizedFiniteTimeResonanceKernel Omega T| <=
      T / (2 * Real.pi) := by
  rw [abs_of_nonneg
    (normalizedFiniteTimeResonanceKernel_nonneg Omega T)]
  exact normalizedFiniteTimeResonanceKernel_le_height Omega hT

/-- Explicit quadratic Lipschitz bound for the normalized resonance peak. -/
theorem abs_normalizedFiniteTimeResonanceKernel_sub_le
    (Omega Xi : Real) {T : Real} (hT : 0 < T) :
    |normalizedFiniteTimeResonanceKernel Omega T -
        normalizedFiniteTimeResonanceKernel Xi T| <=
      (T ^ 2 / Real.pi) * |Omega - Xi| := by
  rw [normalizedFiniteTimeResonanceKernel_eq_div_two_pi,
    normalizedFiniteTimeResonanceKernel_eq_div_two_pi,
    <- sub_div, abs_div,
    abs_of_pos (mul_pos zero_lt_two Real.pi_pos)]
  calc
    |finiteTimeResonanceWeight Omega T -
        finiteTimeResonanceWeight Xi T| / (2 * Real.pi) <=
      (2 * T ^ 2 * |Omega - Xi|) / (2 * Real.pi) :=
        div_le_div_of_nonneg_right
          (abs_finiteTimeResonanceWeight_sub_le Omega Xi hT)
          (mul_nonneg zero_le_two Real.pi_pos.le)
    _ = (T ^ 2 / Real.pi) * |Omega - Xi| := by
      field_simp [Real.pi_ne_zero]

/-- Bundled Lipschitz form used by quantitative empirical-measure bounds. -/
theorem lipschitzWith_normalizedFiniteTimeResonanceKernel
    {T : Real} (hT : 0 < T) :
    LipschitzWith ⟨T ^ 2 / Real.pi, by positivity⟩
      (fun Omega : Real => normalizedFiniteTimeResonanceKernel Omega T) := by
  apply LipschitzWith.of_dist_le_mul
  intro Omega Xi
  change |normalizedFiniteTimeResonanceKernel Omega T -
      normalizedFiniteTimeResonanceKernel Xi T| <=
    (T ^ 2 / Real.pi) * |Omega - Xi|
  exact abs_normalizedFiniteTimeResonanceKernel_sub_le Omega Xi hT

end

end ArchonPhysics.ResonanceKernelLipschitz
