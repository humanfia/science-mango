import ArchonPhysics.ComplexRegularizedMarkedLegBridge
import ArchonPhysics.UniformRandomMassHarmonicSpectrumBound

/-!
# Uniform effective-weight bound for normalized collision phases

After multiplication by the harmonic eigenvalue, the inverse-frequency
singularity is exactly cancelled.  The resulting complex weight has norm
`sqrt(lambda) / 2`, hence is bounded by `sqrt(5) / 2` throughout the frozen
random-mass spectral band.
-/

namespace ArchonPhysics.NormalizedPhaseEffectiveWeightBound

open ArchonPhysics
open ArchonPhysics.ComplexRegularizedMarkedLegBridge
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ThreeWaveCollisionFourierFactorization

noncomputable section

/-- A signed oscillatory leg has unit complex norm. -/
theorem norm_orderedPhaseLeg
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 -> InteractionSign) (time : Real)
    (r : Fin 3) (k : OrderedModeIndex N) :
    ‖orderedPhaseLeg m sign time r k‖ = 1 := by
  unfold orderedPhaseLeg
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

/-- Exact cancellation formula for one normalized phase leg. -/
theorem norm_eigenvalue_mul_orderedNormalizedPhaseLeg
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 -> InteractionSign) (time : Real)
    (r : Fin 3) (k : OrderedModeIndex N) :
    ‖(orderedEigenvalue (harmonicHermitian m) k : Complex) *
        orderedNormalizedPhaseLeg m sign time r k‖ =
      Real.sqrt (orderedEigenvalue (harmonicHermitian m) k) / 2 := by
  let lambda := orderedEigenvalue (harmonicHermitian m) k
  have hlambda : 0 <= lambda :=
    harmonicHermitian_orderedEigenvalue_nonneg m k
  by_cases hzero : lambda = 0
  · simp [lambda, hzero]
  have hsqrt : 0 < Real.sqrt lambda :=
    Real.sqrt_pos.2 (lt_of_le_of_ne hlambda (Ne.symm hzero))
  have hlambdaSq : Real.sqrt lambda ^ 2 = lambda :=
    Real.sq_sqrt hlambda
  unfold orderedNormalizedPhaseLeg orderedModeFrequency
  rw [norm_mul, norm_mul, norm_orderedPhaseLeg]
  simp only [Complex.norm_real, Real.norm_eq_abs, mul_one]
  rw [abs_of_nonneg hlambda, abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) hsqrt))]
  field_simp [ne_of_gt hsqrt]
  nlinarith

/-- The frozen spectral band gives a realization-, volume-, time-, and
sign-independent bound on every physical effective weight. -/
theorem norm_eigenvalue_mul_orderedNormalizedPhaseLeg_le_sqrtFive_div_two
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hband : forall k, orderedEigenvalue (harmonicHermitian m) k <= 5)
    (sign : Fin 3 -> InteractionSign) (time : Real)
    (r : Fin 3) (k : OrderedModeIndex N) :
    ‖(orderedEigenvalue (harmonicHermitian m) k : Complex) *
        orderedNormalizedPhaseLeg m sign time r k‖ <=
      Real.sqrt 5 / 2 := by
  rw [norm_eigenvalue_mul_orderedNormalizedPhaseLeg]
  gcongr
  exact hband k

end

end ArchonPhysics.NormalizedPhaseEffectiveWeightBound
