import ArchonPhysics.RandomMassThreeWaveCollisionNetwork
import ArchonPhysics.ThreeWaveCollisionFourierFactorization

/-!
# Fourier integration of the positive weighted mismatch measure

For every finite positive-mass realization, this module identifies the
Bochner integral of the complex Fourier character against the existing
coupling-weighted mismatch measure with its explicit filtered finite sum.
Combining that measure identity with the exact three-leg algebra gives the
one-leg spectral-projector factorization.

All statements are fixed-size deterministic identities.  No probabilistic,
infinite-volume, or kinetic limit is asserted.
-/

namespace ArchonPhysics.PositiveWeightedMismatchFourierIntegral

open ArchonPhysics
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.ThreeWaveCollisionFourierFactorization
open MeasureTheory

noncomputable section

/-- The complex Fourier character is integrable against every finite
positive weighted mismatch measure. -/
theorem integrable_exp_I_mul_positiveWeightedMismatchMeasure
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (t : Real) :
    Integrable
      (fun x : Real ↦ Complex.exp
        (Complex.I * ((t * x : Real) : Complex)))
      (positiveWeightedMismatchMeasure m sign) := by
  classical
  unfold positiveWeightedMismatchMeasure
  rw [integrable_finsetSum_measure]
  intro modes _hmodes
  by_cases hpositive : IsPositiveOrderedTriple m modes
  · rw [if_pos hpositive]
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · rw [if_neg hpositive]
    exact integrable_zero_measure

/-- The Fourier integral of the genuine finite mismatch measure is exactly
the explicit filtered Fourier sum. -/
theorem integral_positiveWeightedMismatchMeasure_eq_fourierSum
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (t : Real) :
    (∫ x : Real, Complex.exp
        (Complex.I * ((t * x : Real) : Complex))
      ∂positiveWeightedMismatchMeasure m sign) =
      positiveWeightedMismatchFourierSum m sign t := by
  classical
  unfold positiveWeightedMismatchMeasure positiveWeightedMismatchFourierSum
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro modes _hmodes
    by_cases hpositive : IsPositiveOrderedTriple m modes
    · simp only [if_pos hpositive, integral_smul_measure, integral_dirac]
      rw [ENNReal.toReal_ofReal
        (harmonicOrderedNormalizedInteractionWeight_nonneg m modes)]
      rfl
    · simp only [if_neg hpositive, integral_zero_measure]
  · intro modes _hmodes
    by_cases hpositive : IsPositiveOrderedTriple m modes
    · rw [if_pos hpositive]
      exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
    · rw [if_neg hpositive]
      exact integrable_zero_measure

/-- The genuine measure Fourier integral inherits the exact one-leg
spectral-projector factorization of the finite Fourier sum. -/
theorem integral_positiveWeightedMismatchMeasure_factorization
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (t : Real) :
    (∫ x : Real, Complex.exp
        (Complex.I * ((t * x : Real) : Complex))
      ∂positiveWeightedMismatchMeasure m sign) =
      ∑ j, ∑ l, ∏ r,
        complexWeightedProjectedBondKernel (massWeightedDifferenceMatrix m)
          (harmonicHermitian m) (orderedNormalizedPhaseLeg m sign t r) j l := by
  rw [integral_positiveWeightedMismatchMeasure_eq_fourierSum]
  exact positiveWeightedMismatchFourierSum_factorization m sign t

end

end ArchonPhysics.PositiveWeightedMismatchFourierIntegral
