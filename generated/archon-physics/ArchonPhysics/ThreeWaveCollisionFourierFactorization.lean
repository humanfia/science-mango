import ArchonPhysics.NormalizedInteractionSpectralFactorization
import ArchonPhysics.RandomMassPositiveCollisionData

/-!
# Fourier factorization of the three-wave collision measure

For one finite random-mass realization, the Fourier transform of the
coupling-weighted mismatch measure factors into a product of three complex
one-leg spectral-projector kernels.  The physical inverse-frequency factors
and the signed oscillatory phases are both attached leg by leg.

The result is an exact finite identity.  It does not assert convergence of
the one-leg kernels, an integrated density of states, self-averaging, or a
kinetic limit.
-/

open scoped Matrix ComplexConjugate

namespace ArchonPhysics.ThreeWaveCollisionFourierFactorization

open ArchonPhysics
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedInteractionSpectralFactorization
open ArchonPhysics.RandomMassPositiveCollisionData

noncomputable section

variable {iota bond : Type*}
variable [Fintype iota] [DecidableEq iota] [Fintype bond]

/-- Complex finite Fubini identity underlying the Fourier factorization. -/
private theorem complex_sum_doubleSum_prod_mul_prod
    {mode leg left right : Type*}
    [Fintype mode] [Fintype leg] [DecidableEq leg]
    [Fintype left] [Fintype right]
    (kernel : leg → mode → left → right → Complex)
    (weight : leg → mode → Complex) :
    (∑ modes : leg → mode,
        (∑ j, ∑ l, ∏ r, kernel r (modes r) j l) *
          ∏ r, weight r (modes r)) =
      ∑ j, ∑ l, ∏ r, ∑ k, weight r k * kernel r k j l := by
  calc
    (∑ modes : leg → mode,
        (∑ j, ∑ l, ∏ r, kernel r (modes r) j l) *
          ∏ r, weight r (modes r)) =
        ∑ modes : leg → mode, ∑ j, ∑ l,
          ∏ r, weight r (modes r) * kernel r (modes r) j l := by
      apply Finset.sum_congr rfl
      intro modes _hmodes
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _hl
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro r _hr
      exact mul_comm _ _
    _ = ∑ j, ∑ l, ∑ modes : leg → mode,
          ∏ r, weight r (modes r) * kernel r (modes r) j l := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.sum_comm]
    _ = ∑ j, ∑ l, ∏ r, ∑ k, weight r k * kernel r k j l := by
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro l _hl
      rw [Fintype.prod_sum]

/-- Complex one-leg spectral-projector kernel. -/
def complexWeightedProjectedBondKernel (B : Matrix bond iota Real)
    (A : HermitianMatrix iota)
    (weight : Fin (Fintype.card iota) → Complex) : Matrix bond bond Complex :=
  fun j l ↦ ∑ k, weight k * (projectedBondKernel B A k j l : Complex)

/-- Complex interaction moment against arbitrary one-leg weights. -/
def complexWeightedInteractionMoment {n : Nat} (B : Matrix bond iota Real)
    (A : HermitianMatrix iota)
    (weight : Fin n → Fin (Fintype.card iota) → Complex) : Complex :=
  ∑ modes, (orderedInteractionWeightSq B A modes : Complex) *
    ∏ r, weight r (modes r)

/-- Exact complex analogue of the real spectral-kernel factorization. -/
theorem complexWeightedInteractionMoment_factorization {n : Nat}
    (B : Matrix bond iota Real) (A : HermitianMatrix iota)
    (weight : Fin n → Fin (Fintype.card iota) → Complex) :
    complexWeightedInteractionMoment B A weight =
      ∑ j, ∑ l, ∏ r,
        complexWeightedProjectedBondKernel B A (weight r) j l := by
  unfold complexWeightedInteractionMoment orderedInteractionWeightSq
    complexWeightedProjectedBondKernel
  push_cast
  exact complex_sum_doubleSum_prod_mul_prod
    (kernel := fun _r k j l ↦ (projectedBondKernel B A k j l : Complex)) weight

/-- Oscillatory factor of one signed ordered-frequency leg. -/
def orderedPhaseLeg {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (t : Real)
    (r : Fin 3) (k : OrderedModeIndex N) : Complex :=
  Complex.exp (Complex.I *
    ((t * (sign r).coefficient *
      orderedModeFrequency (harmonicHermitian m) k : Real) : Complex))

/-- Physical inverse-frequency normalization times one signed phase leg. -/
def orderedNormalizedPhaseLeg {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (t : Real)
    (r : Fin 3) (k : OrderedModeIndex N) : Complex :=
  ((2 * orderedModeFrequency (harmonicHermitian m) k)⁻¹ : Real) *
    orderedPhaseLeg m sign t r k

/-- The product of the three one-leg phases is the phase of the signed
three-wave mismatch. -/
theorem prod_orderedPhaseLeg_eq_exp_mismatch
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (t : Real)
    (modes : OrderedModeTriple N) :
    (∏ r, orderedPhaseLeg m sign t r (modes r)) =
      Complex.exp (Complex.I *
        ((t * orderedThreeWaveMismatch m sign modes : Real) : Complex)) := by
  unfold orderedPhaseLeg orderedThreeWaveMismatch
  rw [← Complex.exp_sum]
  congr 2
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  ring

/-- Exact factorization before displaying the positive-mode filter.  The
inverse-frequency factors make every tuple containing a zero mode vanish. -/
theorem complex_normalized_phase_sum_factorization
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (t : Real) :
    (∑ modes : OrderedModeTriple N,
        (harmonicOrderedNormalizedInteractionWeight m modes : Complex) *
          Complex.exp (Complex.I *
            ((t * orderedThreeWaveMismatch m sign modes : Real) : Complex))) =
      ∑ j, ∑ l, ∏ r,
        complexWeightedProjectedBondKernel (massWeightedDifferenceMatrix m)
          (harmonicHermitian m) (orderedNormalizedPhaseLeg m sign t r) j l := by
  rw [← complexWeightedInteractionMoment_factorization]
  unfold complexWeightedInteractionMoment orderedNormalizedPhaseLeg
    harmonicOrderedNormalizedInteractionWeight harmonicOrderedInteractionWeightSq
  apply Finset.sum_congr rfl
  intro modes _hmodes
  rw [Finset.prod_mul_distrib, prod_orderedPhaseLeg_eq_exp_mismatch]
  push_cast
  ring

/-- A normalized ordered interaction containing a nonpositive-frequency leg
vanishes.  Harmonic ordered frequencies are nonnegative, so failure of the
strict positive filter identifies a zero-frequency leg. -/
theorem harmonicOrderedNormalizedInteractionWeight_eq_zero_of_not_positive
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) (hnot : ¬ IsPositiveOrderedTriple m modes) :
    harmonicOrderedNormalizedInteractionWeight m modes = 0 := by
  simp only [IsPositiveOrderedTriple, mem_orderedPositiveModeIndices_iff,
    not_forall] at hnot
  obtain ⟨r, hr⟩ := hnot
  have hfrequency :
      orderedModeFrequency (harmonicHermitian m) (modes r) = 0 :=
    le_antisymm (not_lt.mp hr) (Real.sqrt_nonneg _)
  have hinverse :
      (2 * orderedModeFrequency (harmonicHermitian m) (modes r))⁻¹ = 0 := by
    simp [hfrequency]
  have hproduct :
      (∏ s, (2 * orderedModeFrequency
        (harmonicHermitian m) (modes s))⁻¹) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ r) hinverse
  unfold harmonicOrderedNormalizedInteractionWeight
  rw [hproduct, mul_zero]

/-- Fourier transform of the finite positive-mode coupling-weighted mismatch
measure, written as its defining filtered sum. -/
def positiveWeightedMismatchFourierSum {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (t : Real) : Complex := by
  classical
  exact ∑ modes : OrderedModeTriple N,
    if IsPositiveOrderedTriple m modes then
      (harmonicOrderedNormalizedInteractionWeight m modes : Complex) *
        Complex.exp (Complex.I *
          ((t * orderedThreeWaveMismatch m sign modes : Real) : Complex))
    else 0

/-- The explicit positive-mode filter can be removed because every excluded
normalized tuple has zero weight. -/
theorem positiveWeightedMismatchFourierSum_eq_unfiltered
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (t : Real) :
    positiveWeightedMismatchFourierSum m sign t =
      ∑ modes : OrderedModeTriple N,
        (harmonicOrderedNormalizedInteractionWeight m modes : Complex) *
          Complex.exp (Complex.I *
            ((t * orderedThreeWaveMismatch m sign modes : Real) : Complex)) := by
  unfold positiveWeightedMismatchFourierSum
  apply Finset.sum_congr rfl
  intro modes _hmodes
  by_cases hpositive : IsPositiveOrderedTriple m modes
  · rw [if_pos hpositive]
  · rw [if_neg hpositive,
      harmonicOrderedNormalizedInteractionWeight_eq_zero_of_not_positive
        m modes hpositive]
    simp

/-- Exact one-leg spectral-kernel representation of the finite positive-mode
coupling-weighted mismatch Fourier transform. -/
theorem positiveWeightedMismatchFourierSum_factorization
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (t : Real) :
    positiveWeightedMismatchFourierSum m sign t =
      ∑ j, ∑ l, ∏ r,
        complexWeightedProjectedBondKernel (massWeightedDifferenceMatrix m)
          (harmonicHermitian m) (orderedNormalizedPhaseLeg m sign t r) j l := by
  rw [positiveWeightedMismatchFourierSum_eq_unfiltered]
  exact complex_normalized_phase_sum_factorization m sign t

end


end ArchonPhysics.ThreeWaveCollisionFourierFactorization
