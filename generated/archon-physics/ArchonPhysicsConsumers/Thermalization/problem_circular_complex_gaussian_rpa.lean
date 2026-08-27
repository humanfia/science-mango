import ArchonPhysics.CircularComplexGaussianRPA

/-!
# Consumer: finite circular complex-Gaussian RPA initial law

This acceptance target uses three independent modes, each with deterministic
action two.  It checks the probability/product law, coordinate marginals,
zero means, the exact isotropic covariance matrix, and invariance of the full
joint law under arbitrary deterministic mode-by-mode phase rotations.

Unlike `ConcreteGaussianTwoBandInitialEnsemble`, these modal radii are random
(Rayleigh after polar decomposition); this is the complex-Gaussian ensemble
needed for an initial Wick/RPA closure.  The target does not assert nonlinear
propagation of that closure.
-/

namespace ArchonPhysicsConsumers.Thermalization

open MeasureTheory ProbabilityTheory Complex
open ArchonPhysics.CircularComplexGaussianRPA
open scoped NNReal InnerProductSpace RealInnerProductSpace

noncomputable section

namespace CircularComplexGaussianRPA

/-- Three-mode test profile with modal action two. -/
def threeModeAction (_mode : Fin 3) : ℝ≥0 := 2

/-- Kernel-checked contract for a finite circular complex-Gaussian RPA law. -/
theorem problem_circular_complex_gaussian_rpa :
    finiteModeLaw threeModeAction Set.univ = 1 ∧
    iIndepFun (fun mode => amplitude mode)
      (finiteModeLaw threeModeAction) ∧
    (∀ mode : Fin 3,
      HasLaw (amplitude mode) (oneModeLaw (threeModeAction mode))
        (finiteModeLaw threeModeAction)) ∧
    (∀ mode : Fin 3,
      ∫ sample, amplitude mode sample ∂finiteModeLaw threeModeAction = 0) ∧
    covarianceBilin (oneModeLaw 2) (1 : ℂ) 1 = 1 ∧
    covarianceBilin (oneModeLaw 2) Complex.I Complex.I = 1 ∧
    covarianceBilin (oneModeLaw 2) (1 : ℂ) Complex.I = 0 ∧
    covarianceBilin (oneModeLaw 2) (1 : ℂ) 1 +
      covarianceBilin (oneModeLaw 2) Complex.I Complex.I = 2 ∧
    ∀ phase : Fin 3 → Circle,
      (finiteModeLaw threeModeAction).map (phaseRotate phase) =
        finiteModeLaw threeModeAction := by
  refine ⟨measure_univ, amplitude_iIndep threeModeAction,
    amplitude_hasLaw threeModeAction,
    integral_amplitude_finiteModeLaw threeModeAction, ?_, ?_, ?_, ?_,
    map_phaseRotate_finiteModeLaw threeModeAction⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num

#print axioms problem_circular_complex_gaussian_rpa
#print axioms covarianceBilin_oneModeLaw
#print axioms map_phaseRotate_finiteModeLaw

end CircularComplexGaussianRPA

end

end ArchonPhysicsConsumers.Thermalization
