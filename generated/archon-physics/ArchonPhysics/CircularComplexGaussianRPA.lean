import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.Basic

/-!
# Finite circular complex-Gaussian random-phase amplitudes

This module constructs the finite-mode complex-Gaussian ensemble that is used
by Gaussian RPA/Wick closures.  A mode with deterministic action `n` is a
scaled standard Gaussian vector in the real Euclidean plane `ℂ`; the scale is
`sqrt (n / 2)`, so its two real quadratures each have variance `n / 2`.

This is deliberately different from
`ConcreteGaussianTwoBandInitialEnsemble`: there the word `Gaussian` describes
the random masses, while every modal radius is deterministic and only its
phase is Haar.  Here the complex modal radius is genuinely Rayleigh/random.

Only an initial finite product law is constructed.  No claim is made that a
nonlinear FPUT or Lennard--Jones flow preserves Gaussianity, independence, or
Wick factorization.
Mathlib supplies Gaussian moment integrability but no ready-made fourth-moment
Wick formula; this file therefore proves moments through order two only.
-/

namespace ArchonPhysics.CircularComplexGaussianRPA

open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators ComplexConjugate NNReal InnerProductSpace RealInnerProductSpace

noncomputable section

/-- Real scaling that turns a standard circular complex Gaussian, whose two
quadratures have variance one, into one with total action `n`. -/
def actionScale (n : ℝ≥0) : ℝ := Real.sqrt ((n : ℝ) / 2)

/-- Real-linear scaling used in the one-mode push-forward law. -/
def actionScaleCLM (n : ℝ≥0) : ℂ →L[ℝ] ℂ :=
  actionScale n • ContinuousLinearMap.id ℝ ℂ

@[simp] theorem actionScaleCLM_apply (n : ℝ≥0) (z : ℂ) :
    actionScaleCLM n z = actionScale n • z := rfl


/-- One circular complex-Gaussian mode with deterministic action `n`. -/
def oneModeLaw (n : ℝ≥0) : Measure ℂ :=
  (stdGaussian ℂ).map (actionScaleCLM n)

instance oneModeLaw_isProbabilityMeasure (n : ℝ≥0) :
    IsProbabilityMeasure (oneModeLaw n) := by
  unfold oneModeLaw
  exact Measure.isProbabilityMeasure_map (actionScaleCLM n).measurable.aemeasurable

/-- Independent finite circular complex-Gaussian modes with a deterministic
action profile. -/
def finiteModeLaw {ι : Type*} [Fintype ι] (action : ι → ℝ≥0) :
    Measure (ι → ℂ) :=
  Measure.pi (fun mode => oneModeLaw (action mode))

instance finiteModeLaw_isProbabilityMeasure {ι : Type*} [Fintype ι]
    (action : ι → ℝ≥0) : IsProbabilityMeasure (finiteModeLaw action) := by
  unfold finiteModeLaw
  infer_instance

/-- Canonical amplitude coordinate on the finite product sample space. -/
def amplitude {ι : Type*} (mode : ι) (sample : ι → ℂ) : ℂ := sample mode

theorem measurable_amplitude {ι : Type*} (mode : ι) :
    Measurable (amplitude mode : (ι → ℂ) → ℂ) := by
  exact measurable_pi_apply mode

/-- The coordinate amplitudes are independent under the finite product law. -/
theorem amplitude_iIndep {ι : Type*} [Fintype ι]
    (action : ι → ℝ≥0) :
    iIndepFun (fun mode => amplitude mode)
      (finiteModeLaw action) := by
  unfold finiteModeLaw amplitude
  exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)

/-- Every coordinate has its prescribed one-mode circular Gaussian law. -/
theorem amplitude_hasLaw {ι : Type*} [Fintype ι]
    (action : ι → ℝ≥0) (mode : ι) :
    HasLaw (amplitude mode) (oneModeLaw (action mode))
      (finiteModeLaw action) := by
  refine ⟨(measurable_amplitude mode).aemeasurable, ?_⟩
  exact (measurePreserving_eval (fun k => oneModeLaw (action k)) mode).map_eq

/-- A circular complex-Gaussian mode is centered. -/
@[simp] theorem integral_id_oneModeLaw (n : ℝ≥0) :
    ∫ z, z ∂oneModeLaw n = 0 := by
  unfold oneModeLaw
  rw [integral_map (actionScaleCLM n).measurable.aemeasurable (by fun_prop)]
  simpa using (actionScaleCLM n).integral_comp_id_comm
    (IsGaussian.integrable_id (μ := stdGaussian ℂ))


/-- Each real quadrature of the standard circular Gaussian has second moment one. -/
@[simp] theorem integral_re_sq_stdGaussian :
    ∫ z : ℂ, z.re ^ 2 ∂stdGaussian ℂ = 1 := by
  have h := variance_dual_stdGaussian (E := ℂ) Complex.reCLM
  have hmean : ∫ z : ℂ, z.re ∂stdGaussian ℂ = 0 := by
    simpa only [Complex.reCLM_apply] using
      (integral_strongDual_stdGaussian (E := ℂ) Complex.reCLM)
  rw [variance_eq_integral (by fun_prop)] at h
  simpa [Complex.reCLM_norm, hmean] using h

@[simp] theorem integral_im_sq_stdGaussian :
    ∫ z : ℂ, z.im ^ 2 ∂stdGaussian ℂ = 1 := by
  have h := variance_dual_stdGaussian (E := ℂ) Complex.imCLM
  have hmean : ∫ z : ℂ, z.im ∂stdGaussian ℂ = 0 := by
    simpa only [Complex.imCLM_apply] using
      (integral_strongDual_stdGaussian (E := ℂ) Complex.imCLM)
  rw [variance_eq_integral (by fun_prop)] at h
  simpa [Complex.imCLM_norm, hmean] using h

/-- The square of the chosen real scale is exactly half the action. -/
@[simp] theorem actionScale_sq (n : ℝ≥0) :
    actionScale n ^ 2 = (n : ℝ) / 2 := by
  rw [actionScale, Real.sq_sqrt]
  positivity

/-- Real scalar dilation is self-adjoint. -/
@[simp] theorem adjoint_actionScaleCLM (n : ℝ≥0) :
    (actionScaleCLM n).adjoint = actionScaleCLM n := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff
    (actionScaleCLM n) (actionScaleCLM n)).2
  intro u v
  simp only [actionScaleCLM_apply, real_inner_smul_left, real_inner_smul_right]


/-- Exact isotropic real covariance of one circular complex-Gaussian mode. -/
theorem covarianceBilin_oneModeLaw (n : ℝ≥0) (u v : ℂ) :
    covarianceBilin (oneModeLaw n) u v =
      ((n : ℝ) / 2) * ⟪u, v⟫_ℝ := by
  unfold oneModeLaw
  rw [covarianceBilin_map
      (IsGaussian.memLp_id (stdGaussian ℂ) 2 (by norm_num))
      (actionScaleCLM n), covarianceBilin_stdGaussian]
  rw [innerSL_apply_apply]
  rw [adjoint_actionScaleCLM, actionScaleCLM_apply, actionScaleCLM_apply,
    real_inner_smul_left, real_inner_smul_right]
  calc
    actionScale n * (actionScale n * ⟪u, v⟫_ℝ) =
        actionScale n ^ 2 * ⟪u, v⟫_ℝ := by ring
    _ = ((n : ℝ) / 2) * ⟪u, v⟫_ℝ := by rw [actionScale_sq]

/-- Coordinate covariance matrix: both quadratures have variance `n / 2`
and their cross covariance vanishes. -/
@[simp] theorem covarianceBilin_oneModeLaw_one_one (n : ℝ≥0) :
    covarianceBilin (oneModeLaw n) (1 : ℂ) 1 = (n : ℝ) / 2 := by
  simpa using covarianceBilin_oneModeLaw n (1 : ℂ) 1

@[simp] theorem covarianceBilin_oneModeLaw_I_I (n : ℝ≥0) :
    covarianceBilin (oneModeLaw n) Complex.I Complex.I = (n : ℝ) / 2 := by
  simpa using covarianceBilin_oneModeLaw n Complex.I Complex.I

@[simp] theorem covarianceBilin_oneModeLaw_one_I (n : ℝ≥0) :
    covarianceBilin (oneModeLaw n) (1 : ℂ) Complex.I = 0 := by
  simpa using covarianceBilin_oneModeLaw n (1 : ℂ) Complex.I


/-- The sum of the two quadrature variances is the prescribed modal action. -/
@[simp] theorem totalQuadratureCovariance_oneModeLaw (n : ℝ≥0) :
    covarianceBilin (oneModeLaw n) (1 : ℂ) 1 +
      covarianceBilin (oneModeLaw n) Complex.I Complex.I = (n : ℝ) := by
  simp


/-- The full one-mode law is invariant under every deterministic phase rotation. -/
theorem map_rotation_oneModeLaw (n : ℝ≥0) (phase : Circle) :
    (oneModeLaw n).map (rotation phase) = oneModeLaw n := by
  unfold oneModeLaw
  calc
    ((stdGaussian ℂ).map (actionScaleCLM n)).map (rotation phase) =
        (stdGaussian ℂ).map ((rotation phase) ∘ (actionScaleCLM n)) :=
      Measure.map_map (rotation phase).continuous.measurable (actionScaleCLM n).measurable
    _ = (stdGaussian ℂ).map ((actionScaleCLM n) ∘ (rotation phase)) := by
      congr 1
      funext z
      simp only [Function.comp_apply, rotation_apply, actionScaleCLM_apply]
      change (phase : ℂ) * ((actionScale n : ℂ) * z) =
        (actionScale n : ℂ) * ((phase : ℂ) * z)
      ring
    _ = ((stdGaussian ℂ).map (rotation phase)).map (actionScaleCLM n) :=
      (Measure.map_map (actionScaleCLM n).measurable
        (rotation phase).continuous.measurable).symm
    _ = (stdGaussian ℂ).map (actionScaleCLM n) := by
      rw [stdGaussian_map (rotation phase)]

/-- Every finite-product amplitude coordinate is centered. -/
@[simp] theorem integral_amplitude_finiteModeLaw {ι : Type*} [Fintype ι]
    (action : ι → ℝ≥0) (mode : ι) :
    ∫ sample, amplitude mode sample ∂finiteModeLaw action = 0 := by
  unfold amplitude finiteModeLaw
  rw [integral_eval]
  exact integral_id_oneModeLaw (action mode)


/-- Independent deterministic phase rotations of all finite modes. -/
def phaseRotate {ι : Type*} (phase : ι → Circle) (sample : ι → ℂ) :
    ι → ℂ :=
  fun mode => rotation (phase mode) (sample mode)

/-- The complete finite product law is invariant under arbitrary deterministic
mode-by-mode phase rotations. -/
theorem map_phaseRotate_finiteModeLaw {ι : Type*} [Fintype ι]
    (action : ι → ℝ≥0) (phase : ι → Circle) :
    (finiteModeLaw action).map (phaseRotate phase) = finiteModeLaw action := by
  unfold finiteModeLaw phaseRotate
  rw [Measure.pi_map_pi (fun mode =>
    (rotation (phase mode)).continuous.measurable.aemeasurable)]
  congr 1
  funext mode
  exact map_rotation_oneModeLaw (action mode) (phase mode)

end

end ArchonPhysics.CircularComplexGaussianRPA
