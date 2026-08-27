import ArchonPhysics.CircularComplexGaussianWick

/-!
# Consumer: fourth-order finite circular complex-Gaussian Wick data

This target checks the exact one-mode fourth moment and the distinct-mode
factorizations needed as finite-law input for perturbative diagram algebra.
It deliberately makes no claim that a nonlinear microscopic flow propagates
Gaussianity or Wick factorization to kinetic time.
-/

namespace ArchonPhysicsConsumers.Thermalization

open MeasureTheory Complex
open ArchonPhysics.CircularComplexGaussianRPA
open ArchonPhysics.CircularComplexGaussianWick
open scoped ComplexConjugate NNReal

noncomputable section

namespace CircularComplexGaussianWick

/-- Three independent modes, each with prescribed action two. -/
def threeModeAction (_mode : Fin 3) : ℝ≥0 := 2

/-- Kernel-checked finite-law fourth-order Wick contract. -/
theorem problem_circular_complex_gaussian_wick :
    (∫ z, Complex.normSq z ∂oneModeLaw 2) = 2 ∧
    (∫ z, Complex.normSq z ^ 2 ∂oneModeLaw 2) = 8 ∧
    (∫ z, Complex.normSq z ^ 2 ∂oneModeLaw 2) =
      2 * (∫ z, Complex.normSq z ∂oneModeLaw 2) ^ 2 ∧
    (∫ sample,
      Complex.normSq (amplitude (0 : Fin 3) sample) *
        Complex.normSq (amplitude (1 : Fin 3) sample)
      ∂finiteModeLaw threeModeAction) = 4 ∧
    (∫ sample,
      amplitude (0 : Fin 3) sample * amplitude (1 : Fin 3) sample
      ∂finiteModeLaw threeModeAction) = 0 ∧
    (∫ sample,
      amplitude (0 : Fin 3) sample * conj (amplitude (1 : Fin 3) sample)
      ∂finiteModeLaw threeModeAction) = 0 := by
  refine ⟨by norm_num, by norm_num, oneMode_radial_wick_identity 2, ?_, ?_, ?_⟩
  · convert
      (integral_distinct_normSq_mul_normSq_finiteModeLaw threeModeAction
        (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide)) using 1;
      norm_num [threeModeAction]
  · exact integral_distinct_amplitude_mul_amplitude_finiteModeLaw threeModeAction
      (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide)
  · exact integral_distinct_amplitude_mul_conj_amplitude_finiteModeLaw threeModeAction
      (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide)

#print axioms problem_circular_complex_gaussian_wick
#print axioms integral_normSq_sq_oneModeLaw
#print axioms integral_distinct_normSq_mul_normSq_finiteModeLaw

end CircularComplexGaussianWick

end

end ArchonPhysicsConsumers.Thermalization
