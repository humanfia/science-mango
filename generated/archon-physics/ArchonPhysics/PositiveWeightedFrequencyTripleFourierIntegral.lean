import ArchonPhysics.PositiveWeightedMismatchFourierIntegral

/-!
# Joint frequency-triple Fourier integrals

The scalar mismatch measure records only one signed linear combination of a
three-wave frequency triple.  Here the same nonnegative normalized collision
weights define a finite measure on the fixed space `Fin 3 -> Real`, retaining
all three ordered frequencies.  Its Fourier transform accepts an independent
real parameter on every leg and factors exactly into the three existing
one-leg complex spectral-projector kernels.

Pushing this joint measure through a signed frequency sum recovers the scalar
mismatch measure.  Equivalently, restricting the joint Fourier parameter to
`time * sign.coefficient` recovers the existing mismatch Fourier sum.  All
statements are fixed-volume identities; no joint weak limit is asserted.
-/

open scoped Matrix

namespace ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral

open ArchonPhysics
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.ThreeWaveCollisionFourierFactorization
open MeasureTheory

noncomputable section

/-- The three ordered frequencies carried by one ordered interaction tuple. -/
def orderedFrequencyTriple {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (modes : OrderedModeTriple N) : Fin 3 -> Real :=
  fun r => orderedModeFrequency (harmonicHermitian m) (modes r)

/-- The signed scalar mismatch as a linear observable of a frequency triple. -/
def frequencyTripleMismatch
    (sign : Fin 3 -> InteractionSign) (frequency : Fin 3 -> Real) : Real :=
  ∑ r, (sign r).coefficient * frequency r

theorem frequencyTripleMismatch_orderedFrequencyTriple
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 -> InteractionSign) (modes : OrderedModeTriple N) :
    frequencyTripleMismatch sign (orderedFrequencyTriple m modes) =
      orderedThreeWaveMismatch m sign modes := by
  rfl

theorem measurable_frequencyTripleMismatch
    (sign : Fin 3 -> InteractionSign) :
    Measurable (frequencyTripleMismatch sign) := by
  unfold frequencyTripleMismatch
  fun_prop

/-- Positive normalized collision weight placed at each complete ordered
frequency triple. -/
def positiveWeightedFrequencyTripleMeasure
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    Measure (Fin 3 -> Real) := by
  classical
  exact ∑ modes : OrderedModeTriple N,
    if IsPositiveOrderedTriple m modes then
      ENNReal.ofReal (harmonicOrderedNormalizedInteractionWeight m modes) •
        Measure.dirac (orderedFrequencyTriple m modes)
    else 0

/-- Joint Fourier character with one independent real parameter per leg. -/
def frequencyTripleFourierCharacter
    (parameter frequency : Fin 3 -> Real) : Complex :=
  Complex.exp (Complex.I *
    (((∑ r, parameter r * frequency r) : Real) : Complex))

/-- Explicit finite joint Fourier sum of the weighted frequency-triple
measure. -/
def positiveWeightedFrequencyTripleFourierSum
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (parameter : Fin 3 -> Real) : Complex := by
  classical
  exact ∑ modes : OrderedModeTriple N,
    if IsPositiveOrderedTriple m modes then
      (harmonicOrderedNormalizedInteractionWeight m modes : Complex) *
        frequencyTripleFourierCharacter parameter
          (orderedFrequencyTriple m modes)
    else 0

/-- Joint Fourier characters are integrable against the finite weighted
frequency-triple measure. -/
theorem integrable_frequencyTripleFourierCharacter
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (parameter : Fin 3 -> Real) :
    Integrable (frequencyTripleFourierCharacter parameter)
      (positiveWeightedFrequencyTripleMeasure m) := by
  classical
  unfold positiveWeightedFrequencyTripleMeasure
  rw [integrable_finsetSum_measure]
  intro modes _hmodes
  by_cases hpositive : IsPositiveOrderedTriple m modes
  · rw [if_pos hpositive]
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · rw [if_neg hpositive]
    exact integrable_zero_measure

/-- The joint measure Fourier integral equals its explicit filtered finite
sum. -/
theorem integral_positiveWeightedFrequencyTripleMeasure_eq_fourierSum
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (parameter : Fin 3 -> Real) :
    (∫ frequency : Fin 3 -> Real,
        frequencyTripleFourierCharacter parameter frequency
      ∂positiveWeightedFrequencyTripleMeasure m) =
      positiveWeightedFrequencyTripleFourierSum m parameter := by
  classical
  unfold positiveWeightedFrequencyTripleMeasure
    positiveWeightedFrequencyTripleFourierSum
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro modes _hmodes
    by_cases hpositive : IsPositiveOrderedTriple m modes
    · simp only [if_pos hpositive, integral_smul_measure, integral_dirac]
      rw [ENNReal.toReal_ofReal
        (harmonicOrderedNormalizedInteractionWeight_nonneg m modes)]
      rw [Complex.real_smul]
    · simp only [if_neg hpositive, integral_zero_measure]
  · intro modes _hmodes
    by_cases hpositive : IsPositiveOrderedTriple m modes
    · rw [if_pos hpositive]
      exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
    · rw [if_neg hpositive]
      exact integrable_zero_measure

/-- The scalar positive mismatch measure is exactly the pushforward of the
joint frequency-triple measure by the signed frequency sum. -/
theorem map_positiveWeightedFrequencyTripleMeasure_eq_mismatchMeasure
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 -> InteractionSign) :
    (positiveWeightedFrequencyTripleMeasure m).map
        (frequencyTripleMismatch sign) =
      positiveWeightedMismatchMeasure m sign := by
  classical
  unfold positiveWeightedFrequencyTripleMeasure
    positiveWeightedMismatchMeasure
  rw [Measure.map_finset_sum'
    (measurable_frequencyTripleMismatch sign).aemeasurable]
  apply Finset.sum_congr rfl
  intro modes _hmodes
  by_cases hpositive : IsPositiveOrderedTriple m modes
  · simp only [if_pos hpositive, Measure.map_smul,
      Measure.map_dirac' (measurable_frequencyTripleMismatch sign)]
    rw [frequencyTripleMismatch_orderedFrequencyTriple]
  · simp [hpositive]

/-- On the signed diagonal of joint Fourier parameters, the joint transform
is exactly the existing scalar mismatch Fourier sum. -/
theorem positiveWeightedFrequencyTripleFourierSum_signedDiagonal
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 -> InteractionSign) (time : Real) :
    positiveWeightedFrequencyTripleFourierSum m
        (fun r => time * (sign r).coefficient) =
      positiveWeightedMismatchFourierSum m sign time := by
  classical
  unfold positiveWeightedFrequencyTripleFourierSum
    positiveWeightedMismatchFourierSum
  apply Finset.sum_congr rfl
  intro modes _hmodes
  by_cases hpositive : IsPositiveOrderedTriple m modes
  · simp only [if_pos hpositive]
    congr 1
    unfold frequencyTripleFourierCharacter orderedFrequencyTriple
      orderedThreeWaveMismatch
    congr 2
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _hr
    ring
  · simp [hpositive]

/-- Oscillatory factor of one independently tested ordered-frequency leg. -/
def orderedJointFrequencyPhaseLeg
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (parameter : Fin 3 -> Real) (r : Fin 3)
    (k : OrderedModeIndex N) : Complex :=
  Complex.exp (Complex.I *
    ((parameter r * orderedModeFrequency (harmonicHermitian m) k : Real) :
      Complex))

/-- Physical inverse-frequency normalization times one independent joint
Fourier phase leg. -/
def orderedJointFrequencyNormalizedPhaseLeg
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (parameter : Fin 3 -> Real) (r : Fin 3)
    (k : OrderedModeIndex N) : Complex :=
  ((2 * orderedModeFrequency (harmonicHermitian m) k)⁻¹ : Real) *
    orderedJointFrequencyPhaseLeg m parameter r k

/-- On signed-diagonal parameters, the independent joint phase leg is the
existing mismatch phase leg. -/
theorem orderedJointFrequencyPhaseLeg_signedDiagonal
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 -> InteractionSign) (time : Real)
    (r : Fin 3) (k : OrderedModeIndex N) :
    orderedJointFrequencyPhaseLeg m
        (fun s => time * (sign s).coefficient) r k =
      orderedPhaseLeg m sign time r k := by
  unfold orderedJointFrequencyPhaseLeg orderedPhaseLeg
  congr 2

/-- The physical inverse-frequency normalization also agrees exactly on the
signed diagonal. -/
theorem orderedJointFrequencyNormalizedPhaseLeg_signedDiagonal
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 -> InteractionSign) (time : Real)
    (r : Fin 3) (k : OrderedModeIndex N) :
    orderedJointFrequencyNormalizedPhaseLeg m
        (fun s => time * (sign s).coefficient) r k =
      orderedNormalizedPhaseLeg m sign time r k := by
  unfold orderedJointFrequencyNormalizedPhaseLeg
    orderedNormalizedPhaseLeg
  rw [orderedJointFrequencyPhaseLeg_signedDiagonal]

/-- The product of independent one-leg phases is the joint Fourier
character of the complete ordered frequency triple. -/
theorem prod_orderedJointFrequencyPhaseLeg_eq_character
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (parameter : Fin 3 -> Real) (modes : OrderedModeTriple N) :
    (∏ r, orderedJointFrequencyPhaseLeg m parameter r (modes r)) =
      frequencyTripleFourierCharacter parameter
        (orderedFrequencyTriple m modes) := by
  unfold orderedJointFrequencyPhaseLeg frequencyTripleFourierCharacter
    orderedFrequencyTriple
  rw [← Complex.exp_sum]
  congr 2
  push_cast
  rw [Finset.mul_sum]

/-- The explicit positive-mode filter can be removed from the joint transform
because every excluded normalized tuple has zero weight. -/
theorem positiveWeightedFrequencyTripleFourierSum_eq_unfiltered
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (parameter : Fin 3 -> Real) :
    positiveWeightedFrequencyTripleFourierSum m parameter =
      ∑ modes : OrderedModeTriple N,
        (harmonicOrderedNormalizedInteractionWeight m modes : Complex) *
          frequencyTripleFourierCharacter parameter
            (orderedFrequencyTriple m modes) := by
  unfold positiveWeightedFrequencyTripleFourierSum
  apply Finset.sum_congr rfl
  intro modes _hmodes
  by_cases hpositive : IsPositiveOrderedTriple m modes
  · rw [if_pos hpositive]
  · rw [if_neg hpositive,
      harmonicOrderedNormalizedInteractionWeight_eq_zero_of_not_positive
        m modes hpositive]
    simp

/-- Exact three-leg spectral-projector factorization of the joint
frequency-triple Fourier sum. -/
theorem positiveWeightedFrequencyTripleFourierSum_factorization
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (parameter : Fin 3 -> Real) :
    positiveWeightedFrequencyTripleFourierSum m parameter =
      ∑ j, ∑ l, ∏ r,
        complexWeightedProjectedBondKernel (massWeightedDifferenceMatrix m)
          (harmonicHermitian m)
          (orderedJointFrequencyNormalizedPhaseLeg m parameter r) j l := by
  rw [positiveWeightedFrequencyTripleFourierSum_eq_unfiltered,
    ← complexWeightedInteractionMoment_factorization]
  unfold complexWeightedInteractionMoment
    orderedJointFrequencyNormalizedPhaseLeg
    harmonicOrderedNormalizedInteractionWeight
    harmonicOrderedInteractionWeightSq
  apply Finset.sum_congr rfl
  intro modes _hmodes
  rw [Finset.prod_mul_distrib,
    prod_orderedJointFrequencyPhaseLeg_eq_character]
  push_cast
  ring

/-- Integral form of the exact joint frequency-triple projector-kernel
factorization. -/
theorem integral_positiveWeightedFrequencyTripleMeasure_factorization
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (parameter : Fin 3 -> Real) :
    (∫ frequency : Fin 3 -> Real,
        frequencyTripleFourierCharacter parameter frequency
      ∂positiveWeightedFrequencyTripleMeasure m) =
      ∑ j, ∑ l, ∏ r,
        complexWeightedProjectedBondKernel (massWeightedDifferenceMatrix m)
          (harmonicHermitian m)
          (orderedJointFrequencyNormalizedPhaseLeg m parameter r) j l := by
  rw [integral_positiveWeightedFrequencyTripleMeasure_eq_fourierSum]
  exact positiveWeightedFrequencyTripleFourierSum_factorization m parameter

end

end ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral
