import ArchonPhysics.RandomEnsemble

/-!
# Exact moments of the frozen uniform mass law

The frozen one-site mass law is normalized Lebesgue measure on
`[4/5, 6/5]`.  This module computes its mean and centered second moment
exactly, transports those identities to every coordinate having that law,
and records the purely algebraic quotient `variance / (8 * mean) = 1/600`.

The last number is only a moment coefficient.  No Lyapunov-exponent,
low-frequency asymptotic, localization, or thermodynamic-limit theorem is
asserted.
-/

namespace ArchonPhysics.FrozenUniformMassMoments

open ArchonPhysics
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- Integrating against the frozen mass law is integration over its support
times the exact normalizing density `5/2`. -/
theorem integral_massCoordinateLaw_eq_normalized_setIntegral
    (f : Real → Real) :
    (∫ x, f x ∂(RandomEnsemble.massCoordinateLaw)) =
      (5 / 2 : Real) * (∫ x in RandomEnsemble.massSupport, f x) := by
  rw [RandomEnsemble.massCoordinateLaw, ProbabilityTheory.cond]
  simp only [integral_smul_measure, smul_eq_mul]
  congr 1
  simp [RandomEnsemble.massSupport, RandomEnsemble.massLower,
    RandomEnsemble.massUpper, Real.volume_Icc]
  norm_num

/-- The support set integral agrees with the usual oriented interval integral. -/
theorem integral_massSupport_eq_intervalIntegral (f : Real → Real) :
    (∫ x in RandomEnsemble.massSupport, f x) =
      ∫ x in RandomEnsemble.massLower..RandomEnsemble.massUpper, f x := by
  rw [RandomEnsemble.massSupport, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le RandomEnsemble.massLower_le_massUpper]

/-- The exact mean of the frozen one-site mass law is `1`. -/
theorem massCoordinateLaw_mean :
    (∫ x, x ∂(RandomEnsemble.massCoordinateLaw)) = 1 := by
  rw [integral_massCoordinateLaw_eq_normalized_setIntegral,
    integral_massSupport_eq_intervalIntegral, integral_id]
  norm_num [RandomEnsemble.massLower, RandomEnsemble.massUpper]

private theorem hasDerivAt_centeredCube (x : Real) :
    HasDerivAt (fun y : Real ↦ (y - 1) ^ 3 / 3) ((x - 1) ^ 2) x := by
  have h := ((((hasDerivAt_id x).sub_const 1).pow 3).div_const 3)
  simpa [id] using h

/-- The exact second moment centered at the mean `1` is `1/75`. -/
theorem massCoordinateLaw_centeredSecondMoment :
    (∫ x, (x - 1) ^ 2 ∂(RandomEnsemble.massCoordinateLaw)) =
      (1 / 75 : Real) := by
  rw [integral_massCoordinateLaw_eq_normalized_setIntegral,
    integral_massSupport_eq_intervalIntegral]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : Real ↦ (x - 1) ^ 3 / 3)
    (f' := fun x : Real ↦ (x - 1) ^ 2)
    (fun x _hx ↦ hasDerivAt_centeredCube x) (by
      apply Continuous.intervalIntegrable
      fun_prop)]
  norm_num [RandomEnsemble.massLower, RandomEnsemble.massUpper]

/-- The variance of the identity under the frozen mass law is `1/75`. -/
theorem massCoordinateLaw_variance :
    Var[id; RandomEnsemble.massCoordinateLaw] = (1 / 75 : Real) := by
  rw [variance_eq_integral aemeasurable_id]
  simp only [id_eq]
  rw [massCoordinateLaw_mean]
  simpa [id] using massCoordinateLaw_centeredSecondMoment

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Every coordinate of any verified frozen iid ensemble has mean `1`. -/
theorem ensemble_mass_mean
    (ensemble : IIDMassPhaseEnsemble Omega) (n : Nat) :
    (∫ omega, ensemble.mass n omega ∂ensemble.probability) = 1 := by
  rw [(ensemble.mass_hasLaw n).integral_eq]
  exact massCoordinateLaw_mean

/-- Every coordinate of any verified frozen iid ensemble has centered second
moment `1/75`. -/
theorem ensemble_mass_centeredSecondMoment
    (ensemble : IIDMassPhaseEnsemble Omega) (n : Nat) :
    (∫ omega, (ensemble.mass n omega - 1) ^ 2 ∂ensemble.probability) =
      (1 / 75 : Real) := by
  have htransport := (ensemble.mass_hasLaw n).integral_comp
    (f := fun x : Real ↦ (x - 1) ^ 2) (by fun_prop)
  simpa [Function.comp_def] using
    htransport.trans massCoordinateLaw_centeredSecondMoment

/-- Every coordinate of any verified frozen iid ensemble has variance
`1/75`. -/
theorem ensemble_mass_variance
    (ensemble : IIDMassPhaseEnsemble Omega) (n : Nat) :
    Var[ensemble.mass n; ensemble.probability] = (1 / 75 : Real) := by
  rw [(ensemble.mass_hasLaw n).variance_eq]
  exact massCoordinateLaw_variance

/-- The moment quotient used as the Ajanki low-frequency coefficient reduces
algebraically to `1/600` for this frozen law.  This theorem asserts no
frequency asymptotic. -/
theorem frozen_variance_div_eight_mean :
    (1 / 75 : Real) / (8 * 1) = (1 / 600 : Real) := by
  norm_num

/-- The actual frozen base-law variance divided by eight times its actual
mean is `1/600`. -/
theorem massCoordinateLaw_variance_div_eight_mean :
    Var[id; RandomEnsemble.massCoordinateLaw] /
        (8 * (∫ x, x ∂(RandomEnsemble.massCoordinateLaw))) =
      (1 / 600 : Real) := by
  rw [massCoordinateLaw_variance, massCoordinateLaw_mean]
  exact frozen_variance_div_eight_mean

/-- HasLaw transports the same exact moment coefficient to every verified
frozen iid mass coordinate. -/
theorem ensemble_mass_variance_div_eight_mean
    (ensemble : IIDMassPhaseEnsemble Omega) (n : Nat) :
    Var[ensemble.mass n; ensemble.probability] /
        (8 * (∫ omega, ensemble.mass n omega ∂ensemble.probability)) =
      (1 / 600 : Real) := by
  rw [ensemble_mass_variance, ensemble_mass_mean]
  exact frozen_variance_div_eight_mean

end

end ArchonPhysics.FrozenUniformMassMoments
