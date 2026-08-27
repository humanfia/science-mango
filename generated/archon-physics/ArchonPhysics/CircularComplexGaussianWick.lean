import ArchonPhysics.CircularComplexGaussianRPA
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Independence.Integration

/-!
# Fourth-order Wick data for the finite circular complex-Gaussian law

This file supplies the fourth-order finite-law identities that are absent from
`CircularComplexGaussianRPA`.  The calculation is grounded in Mathlib's exact
Gaussian moment-generating function, the independence of uncorrelated jointly
Gaussian quadratures, and the already constructed independent finite product
law.

These are initial-law statements only.  In particular, they do not assert that
an FPUT or Lennard--Jones nonlinear flow propagates Gaussianity, Wick
factorization, or random phases to kinetic time.
-/

namespace ArchonPhysics.CircularComplexGaussianWick

open MeasureTheory ProbabilityTheory Complex
open ArchonPhysics.CircularComplexGaussianRPA
open scoped BigOperators ComplexConjugate NNReal InnerProductSpace RealInnerProductSpace

noncomputable section

/-- The fourth moment of a centered unit-variance real Gaussian is three. -/
@[simp] theorem integral_pow_four_gaussianReal_zero_one :
    ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1 = 3 := by
  change (gaussianReal 0 1)[(fun x : ℝ ↦ x) ^ 4] = 3
  rw [← iteratedDeriv_mgf_zero (X := fun x : ℝ ↦ x) (by simp) 4,
    mgf_fun_id_gaussianReal]
  simp only [NNReal.coe_one, zero_mul, one_mul, zero_add]
  have h1 : deriv (fun t : ℝ ↦ Real.exp (t ^ 2 / 2)) =
      fun t : ℝ ↦ t * Real.exp (t ^ 2 / 2) := by
    funext t
    rw [_root_.deriv_exp (by fun_prop)]
    simp only [deriv_div_const, differentiableAt_fun_id, Nat.cast_ofNat,
      deriv_fun_pow, Nat.add_one_sub_one, pow_one, deriv_id'', mul_one]
    ring
  have h2 : iteratedDeriv 2 (fun t : ℝ ↦ Real.exp (t ^ 2 / 2)) =
      fun t : ℝ ↦ (1 + t ^ 2) * Real.exp (t ^ 2 / 2) := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one, h1]
    funext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop), h1]
    simp only [deriv_id'', one_mul]
    ring
  have hp2 : deriv (fun t : ℝ ↦ 1 + t ^ 2) = fun t : ℝ ↦ 2 * t := by
    funext t
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    norm_num [deriv_fun_pow]
  have h3 : iteratedDeriv 3 (fun t : ℝ ↦ Real.exp (t ^ 2 / 2)) =
      fun t : ℝ ↦ (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2) := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ, h2]
    funext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop), hp2, h1]
    ring
  have hp3 : deriv (fun t : ℝ ↦ 3 * t + t ^ 3) =
      fun t : ℝ ↦ 3 + 3 * t ^ 2 := by
    funext t
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    norm_num [deriv_fun_pow]
  rw [show (4 : ℕ) = 3 + 1 by norm_num, iteratedDeriv_succ, h3]
  rw [deriv_fun_mul (by fun_prop) (by fun_prop), hp3, h1]
  norm_num

/-- The real projection of the standard complex Gaussian is a centered
unit-variance real Gaussian. -/
theorem map_re_stdGaussian :
    (stdGaussian ℂ).map Complex.reCLM = gaussianReal 0 1 := by
  rw [IsGaussian.map_eq_gaussianReal]
  have hmean : ∫ z : ℂ, Complex.reCLM z ∂stdGaussian ℂ = 0 :=
    integral_strongDual_stdGaussian Complex.reCLM
  rw [hmean]
  simp [variance_dual_stdGaussian, Complex.reCLM_norm]

/-- The imaginary projection has the same centered unit-variance law. -/
theorem map_im_stdGaussian :
    (stdGaussian ℂ).map Complex.imCLM = gaussianReal 0 1 := by
  rw [IsGaussian.map_eq_gaussianReal]
  have hmean : ∫ z : ℂ, Complex.imCLM z ∂stdGaussian ℂ = 0 :=
    integral_strongDual_stdGaussian Complex.imCLM
  rw [hmean]
  simp [variance_dual_stdGaussian, Complex.imCLM_norm]

/-- Exact fourth moment of the real quadrature of a standard complex
Gaussian. -/
@[simp] theorem integral_re_pow_four_stdGaussian :
    ∫ z : ℂ, z.re ^ 4 ∂stdGaussian ℂ = 3 := by
  calc
    (∫ z : ℂ, z.re ^ 4 ∂stdGaussian ℂ) =
        ∫ x : ℝ, x ^ 4 ∂((stdGaussian ℂ).map Complex.reCLM) := by
      rw [integral_map Complex.reCLM.measurable.aemeasurable (by fun_prop)]
      rfl
    _ = 3 := by rw [map_re_stdGaussian, integral_pow_four_gaussianReal_zero_one]

/-- Exact fourth moment of the imaginary quadrature. -/
@[simp] theorem integral_im_pow_four_stdGaussian :
    ∫ z : ℂ, z.im ^ 4 ∂stdGaussian ℂ = 3 := by
  calc
    (∫ z : ℂ, z.im ^ 4 ∂stdGaussian ℂ) =
        ∫ x : ℝ, x ^ 4 ∂((stdGaussian ℂ).map Complex.imCLM) := by
      rw [integral_map Complex.imCLM.measurable.aemeasurable (by fun_prop)]
      rfl
    _ = 3 := by rw [map_im_stdGaussian, integral_pow_four_gaussianReal_zero_one]

/-- The continuous real-linear map collecting both real quadratures. -/
def quadratureCLM : ℂ →L[ℝ] ℝ × ℝ :=
  Complex.reCLM.prod Complex.imCLM

@[simp] theorem quadratureCLM_apply (z : ℂ) :
    quadratureCLM z = (z.re, z.im) := rfl

/-- The two quadratures are jointly Gaussian. -/
theorem hasGaussianLaw_quadratures_stdGaussian :
    HasGaussianLaw (fun z : ℂ ↦ (z.re, z.im)) (stdGaussian ℂ) := by
  simpa [quadratureCLM, Function.comp_def] using
    (IsGaussian.hasGaussianLaw_id (μ := stdGaussian ℂ)).map_fun quadratureCLM

/-- The two standard quadratures have zero covariance. -/
theorem covariance_re_im_stdGaussian :
    cov[(fun z : ℂ ↦ z.re), (fun z : ℂ ↦ z.im); stdGaussian ℂ] = 0 := by
  have hmem : MemLp id 2 (stdGaussian ℂ) :=
    IsGaussian.memLp_id (stdGaussian ℂ) 2 (by norm_num)
  have h := covarianceBilin_apply_eq_cov hmem (1 : ℂ) Complex.I
  rw [covarianceBilin_stdGaussian] at h
  have hzero : ((innerSL ℝ) (1 : ℂ)) Complex.I = 0 := by
    norm_num [innerSL_apply_apply, real_inner_eq_re_inner]
  rw [hzero] at h
  have hre : (fun u : ℂ ↦ ⟪(1 : ℂ), u⟫_ℝ) = fun u : ℂ ↦ u.re := by
    funext u
    simp [real_inner_eq_re_inner]
  have him : (fun u : ℂ ↦ ⟪Complex.I, u⟫_ℝ) = fun u : ℂ ↦ u.im := by
    funext u
    simp [real_inner_eq_re_inner]
  rw [hre, him] at h
  exact h.symm

/-- For the circular Gaussian, zero covariance upgrades to actual
independence of the two quadratures. -/
theorem indepFun_re_im_stdGaussian :
    IndepFun (fun z : ℂ ↦ z.re) (fun z : ℂ ↦ z.im) (stdGaussian ℂ) :=
  hasGaussianLaw_quadratures_stdGaussian.indepFun_of_covariance_eq_zero
    covariance_re_im_stdGaussian

/-- Exact mixed quadrature moment. -/
@[simp] theorem integral_re_sq_mul_im_sq_stdGaussian :
    ∫ z : ℂ, z.re ^ 2 * z.im ^ 2 ∂stdGaussian ℂ = 1 := by
  have h := indepFun_re_im_stdGaussian.integral_fun_comp_mul_comp
    (f := fun x : ℝ ↦ x ^ 2) (g := fun x : ℝ ↦ x ^ 2)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  simpa [Function.comp_def] using h


/-- Square-integrability of the real quadrature. -/
theorem integrable_re_sq_stdGaussian :
    Integrable (fun z : ℂ ↦ z.re ^ 2) (stdGaussian ℂ) := by
  simpa only [Complex.reCLM_apply] using
    (IsGaussian.memLp_dual (stdGaussian ℂ) Complex.reCLM 2 (by norm_num)).integrable_sq

/-- Square-integrability of the imaginary quadrature. -/
theorem integrable_im_sq_stdGaussian :
    Integrable (fun z : ℂ ↦ z.im ^ 2) (stdGaussian ℂ) := by
  simpa only [Complex.imCLM_apply] using
    (IsGaussian.memLp_dual (stdGaussian ℂ) Complex.imCLM 2 (by norm_num)).integrable_sq

/-- Fourth-power integrability of the real quadrature. -/
theorem integrable_re_pow_four_stdGaussian :
    Integrable (fun z : ℂ ↦ z.re ^ 4) (stdGaussian ℂ) := by
  have h := (IsGaussian.memLp_dual (stdGaussian ℂ) Complex.reCLM 4
    (by norm_num)).integrable_norm_pow'
  refine h.congr (Filter.Eventually.of_forall fun z ↦ ?_)
  simp only [Complex.reCLM_apply, Real.norm_eq_abs]
  nlinarith [sq_abs z.re]

/-- Fourth-power integrability of the imaginary quadrature. -/
theorem integrable_im_pow_four_stdGaussian :
    Integrable (fun z : ℂ ↦ z.im ^ 4) (stdGaussian ℂ) := by
  have h := (IsGaussian.memLp_dual (stdGaussian ℂ) Complex.imCLM 4
    (by norm_num)).integrable_norm_pow'
  refine h.congr (Filter.Eventually.of_forall fun z ↦ ?_)
  simp only [Complex.imCLM_apply, Real.norm_eq_abs]
  nlinarith [sq_abs z.im]

/-- The product of the two squared quadratures is integrable. -/
theorem integrable_re_sq_mul_im_sq_stdGaussian :
    Integrable (fun z : ℂ ↦ z.re ^ 2 * z.im ^ 2) (stdGaussian ℂ) := by
  have hind0 := indepFun_re_im_stdGaussian.comp
    (φ := fun x : ℝ ↦ x ^ 2) (ψ := fun x : ℝ ↦ x ^ 2) (by fun_prop) (by fun_prop)
  have hind : IndepFun (fun z : ℂ ↦ z.re ^ 2) (fun z : ℂ ↦ z.im ^ 2)
      (stdGaussian ℂ) := by
    simpa [Function.comp_def] using hind0
  change Integrable ((fun z : ℂ ↦ z.re ^ 2) * (fun z : ℂ ↦ z.im ^ 2))
    (stdGaussian ℂ)
  exact hind.integrable_mul integrable_re_sq_stdGaussian integrable_im_sq_stdGaussian

/-- The standard circular complex Gaussian has mean action two. -/
@[simp] theorem integral_normSq_stdGaussian :
    ∫ z : ℂ, Complex.normSq z ∂stdGaussian ℂ = 2 := by
  calc
    (∫ z : ℂ, Complex.normSq z ∂stdGaussian ℂ) =
        ∫ z : ℂ, z.re ^ 2 + z.im ^ 2 ∂stdGaussian ℂ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z ↦ by
        rw [Complex.normSq_apply]
        ring
    _ = (∫ z : ℂ, z.re ^ 2 ∂stdGaussian ℂ) +
        ∫ z : ℂ, z.im ^ 2 ∂stdGaussian ℂ :=
      integral_add integrable_re_sq_stdGaussian integrable_im_sq_stdGaussian
    _ = 2 := by rw [integral_re_sq_stdGaussian, integral_im_sq_stdGaussian]; norm_num

/-- Exact radial fourth moment of the standard circular complex Gaussian. -/
@[simp] theorem integral_normSq_sq_stdGaussian :
    ∫ z : ℂ, Complex.normSq z ^ 2 ∂stdGaussian ℂ = 8 := by
  calc
    (∫ z : ℂ, Complex.normSq z ^ 2 ∂stdGaussian ℂ) =
        ∫ z : ℂ, (z.re ^ 4 + 2 * (z.re ^ 2 * z.im ^ 2)) + z.im ^ 4
          ∂stdGaussian ℂ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z ↦ by
        change Complex.normSq z ^ 2 =
          (z.re ^ 4 + 2 * (z.re ^ 2 * z.im ^ 2)) + z.im ^ 4
        rw [Complex.normSq_apply]
        ring
    _ = (∫ z : ℂ, z.re ^ 4 + 2 * (z.re ^ 2 * z.im ^ 2) ∂stdGaussian ℂ) +
        ∫ z : ℂ, z.im ^ 4 ∂stdGaussian ℂ := by
      simpa only [Pi.add_apply] using
        (integral_add
          (integrable_re_pow_four_stdGaussian.add
            (integrable_re_sq_mul_im_sq_stdGaussian.const_mul 2))
          integrable_im_pow_four_stdGaussian)
    _ = ((∫ z : ℂ, z.re ^ 4 ∂stdGaussian ℂ) +
          2 * ∫ z : ℂ, z.re ^ 2 * z.im ^ 2 ∂stdGaussian ℂ) +
        ∫ z : ℂ, z.im ^ 4 ∂stdGaussian ℂ := by
      have hadd :
          (∫ z : ℂ, z.re ^ 4 + 2 * (z.re ^ 2 * z.im ^ 2) ∂stdGaussian ℂ) =
            (∫ z : ℂ, z.re ^ 4 ∂stdGaussian ℂ) +
              ∫ z : ℂ, 2 * (z.re ^ 2 * z.im ^ 2) ∂stdGaussian ℂ := by
        simpa only [Pi.add_apply] using
          (integral_add integrable_re_pow_four_stdGaussian
            (integrable_re_sq_mul_im_sq_stdGaussian.const_mul 2))
      rw [hadd, integral_const_mul]
    _ = 8 := by
      rw [integral_re_pow_four_stdGaussian, integral_re_sq_mul_im_sq_stdGaussian,
        integral_im_pow_four_stdGaussian]
      norm_num


/-- Real dilation scales complex squared norm by the square of the scale. -/
@[simp] theorem normSq_actionScaleCLM (n : ℝ≥0) (z : ℂ) :
    Complex.normSq (actionScaleCLM n z) =
      actionScale n ^ 2 * Complex.normSq z := by
  simp only [actionScaleCLM_apply, Complex.normSq_apply, smul_re, smul_im]
  ring

/-- A one-mode law has exactly its prescribed mean action. -/
@[simp] theorem integral_normSq_oneModeLaw (n : ℝ≥0) :
    ∫ z, Complex.normSq z ∂oneModeLaw n = (n : ℝ) := by
  unfold oneModeLaw
  rw [integral_map (actionScaleCLM n).measurable.aemeasurable (by fun_prop)]
  simp_rw [normSq_actionScaleCLM]
  rw [integral_const_mul, integral_normSq_stdGaussian, actionScale_sq]
  ring

/-- Exact circular complex-Gaussian fourth moment at prescribed action `n`:
`E |Z|^4 = 2 n^2`. -/
@[simp] theorem integral_normSq_sq_oneModeLaw (n : ℝ≥0) :
    ∫ z, Complex.normSq z ^ 2 ∂oneModeLaw n = 2 * (n : ℝ) ^ 2 := by
  unfold oneModeLaw
  rw [integral_map (actionScaleCLM n).measurable.aemeasurable (by fun_prop)]
  simp_rw [normSq_actionScaleCLM, mul_pow]
  rw [integral_const_mul, integral_normSq_sq_stdGaussian]
  rw [actionScale_sq]
  ring

/-- The one-mode fourth moment is twice the square of its second moment. -/
theorem oneMode_radial_wick_identity (n : ℝ≥0) :
    (∫ z, Complex.normSq z ^ 2 ∂oneModeLaw n) =
      2 * (∫ z, Complex.normSq z ∂oneModeLaw n) ^ 2 := by
  rw [integral_normSq_sq_oneModeLaw, integral_normSq_oneModeLaw]


/-- Each finite-product coordinate has the prescribed mean action. -/
@[simp] theorem integral_normSq_amplitude_finiteModeLaw
    {ι : Type*} [Fintype ι] (action : ι → ℝ≥0) (mode : ι) :
    (∫ sample, Complex.normSq (amplitude mode sample) ∂finiteModeLaw action) =
      (action mode : ℝ) := by
  have h := (amplitude_hasLaw action mode).integral_comp
    (f := Complex.normSq) (by fun_prop)
  simpa [Function.comp_def] using h

/-- Distinct modal actions factor exactly under the independent finite product
law. -/
theorem integral_distinct_normSq_mul_normSq_finiteModeLaw
    {ι : Type*} [Fintype ι] (action : ι → ℝ≥0) {i j : ι} (hij : i ≠ j) :
    (∫ sample,
      Complex.normSq (amplitude i sample) * Complex.normSq (amplitude j sample)
      ∂finiteModeLaw action) = (action i : ℝ) * (action j : ℝ) := by
  have hind := (amplitude_iIndep action).indepFun hij
  have h := hind.integral_fun_comp_mul_comp
    (f := Complex.normSq) (g := Complex.normSq)
    (measurable_amplitude i).aemeasurable (measurable_amplitude j).aemeasurable
    (by fun_prop) (by fun_prop)
  simpa [Function.comp_def] using h

/-- Distinct centered complex modes have zero unconjugated second product. -/
theorem integral_distinct_amplitude_mul_amplitude_finiteModeLaw
    {ι : Type*} [Fintype ι] (action : ι → ℝ≥0) {i j : ι} (hij : i ≠ j) :
    (∫ sample, amplitude i sample * amplitude j sample ∂finiteModeLaw action) = 0 := by
  have hind := (amplitude_iIndep action).indepFun hij
  have h := hind.integral_fun_comp_mul_comp
    (f := id) (g := id)
    (measurable_amplitude i).aemeasurable (measurable_amplitude j).aemeasurable
    (by fun_prop) (by fun_prop)
  simpa [Function.comp_def] using h

/-- Distinct centered complex modes also have zero conjugated second product. -/
theorem integral_distinct_amplitude_mul_conj_amplitude_finiteModeLaw
    {ι : Type*} [Fintype ι] (action : ι → ℝ≥0) {i j : ι} (hij : i ≠ j) :
    (∫ sample, amplitude i sample * conj (amplitude j sample)
      ∂finiteModeLaw action) = 0 := by
  have hind := (amplitude_iIndep action).indepFun hij
  have h := hind.integral_fun_comp_mul_comp
    (f := id) (g := conj)
    (measurable_amplitude i).aemeasurable (measurable_amplitude j).aemeasurable
    (by fun_prop) (by fun_prop)
  simpa [Function.comp_def] using h

end

end ArchonPhysics.CircularComplexGaussianWick
