import ArchonPhysics.GaussianRandomMassSimpleSpectrum

/-!
# Consumer: Gaussian inverse-polynomial avoidance and simple spectrum

This five-site acceptance target checks both layers of the adapter: every
nonzero polynomial in the inverse finite mass vector has a null zero event,
and the complete ordered harmonic spectrum is almost surely simple.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.GaussianRandomMassSimpleSpectrum
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open MeasureTheory

noncomputable section

namespace GaussianRandomMassSimpleSpectrum

def parameters : TruncatedGaussianMassLaw.Parameters where
  mean := 1
  variance := 1 / 100
  variance_ne_zero := by norm_num

abbrev SampleSpace := TruncatedGaussianMassPhaseEnsemble.SampleSpace

def ensemble : GaussianIIDMassPhaseEnsemble parameters SampleSpace :=
  canonicalGaussianIIDMassPhaseEnsemble parameters

/-- Concrete five-site acceptance contract for inverse-polynomial avoidance
and full ordered harmonic spectral simplicity. -/
theorem problem_gaussian_random_mass_simple_spectrum :
    (∀ P : MvPolynomial (Fin 5) Real, P ≠ 0 →
      ensemble.probability
        {sample |
          MvPolynomial.eval
            (coordinatewiseInv (restrictMassFin ensemble sample)) P = 0} = 0) ∧
    ∀ᵐ sample ∂ensemble.probability,
      SimpleOrderedSpectrum
        (harmonicHermitianSample
          (ensemble.restrictPositiveMass (N := 5)) sample) := by
  constructor
  · intro P hP
    exact probability_eval_inverse_restrictMassFin_eq_zero ensemble P hP
  · exact simpleOrderedSpectrum_ae ensemble (N := 5) (by norm_num)

#print axioms problem_gaussian_random_mass_simple_spectrum
#print axioms finiteLaw_absolutelyContinuous_volume
#print axioms probability_eval_inverse_restrictMassFin_eq_zero
#print axioms simpleOrderedSpectrum_ae

end GaussianRandomMassSimpleSpectrum

end

end ArchonPhysicsConsumers.Thermalization
