import ArchonPhysics.PositiveWeightedMismatchFourierIntegral
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Normalized collision Fourier transforms and weak convergence

The finite coupling-weighted mismatch measure is bundled as a finite measure
and normalized to a probability measure.  When its total mass is nonzero, its
characteristic function is exactly the inverse mass times the existing finite
Fourier sum, hence inverse mass times the three-leg one-leg kernel product.

The final theorem is a direct Levy bridge for sequences at fixed finite site
type: pointwise convergence of those normalized kernel products to the
characteristic function of a supplied target probability measure implies weak
convergence.  The pointwise convergence and every nonzero-mass condition are
explicit hypotheses; no model limit is asserted.
-/

open scoped Topology

namespace ArchonPhysics.CollisionFourierWeakLimitBridge

open ArchonPhysics
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PositiveWeightedMismatchFourierIntegral
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ThreeWaveCollisionFourierFactorization
open Filter
open MeasureTheory

noncomputable section

/-- The finite positive-mode sum of weighted Dirac masses has finite total
mass for every realization and sign channel. -/
theorem positiveWeightedMismatchMeasure_isFinite
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) :
    IsFiniteMeasure (positiveWeightedMismatchMeasure m sign) := by
  constructor
  unfold positiveWeightedMismatchMeasure
  classical
  simp only [Measure.coe_finsetSum, Finset.sum_apply, ENNReal.sum_lt_top,
    Finset.mem_univ, forall_const]
  intro modes
  by_cases hpositive : IsPositiveOrderedTriple m modes
  · simp [hpositive]
  · simp [hpositive]

/-- The genuine positive weighted mismatch measure, bundled with its finite
mass proof. -/
def positiveWeightedMismatchFiniteMeasure
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) : FiniteMeasure Real :=
  ⟨positiveWeightedMismatchMeasure m sign,
    positiveWeightedMismatchMeasure_isFinite m sign⟩

/-- Probability normalization of the finite collision measure.  Mathlib's
definition uses a Dirac fallback only in the zero-mass case; all formulas
below explicitly exclude that case. -/
def normalizedPositiveWeightedMismatchMeasure
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) : ProbabilityMeasure Real :=
  (positiveWeightedMismatchFiniteMeasure m sign).normalize

/-- At nonzero total mass, the characteristic function of the normalized
collision measure is inverse mass times the genuine measure Fourier sum. -/
theorem charFun_normalizedPositiveWeightedMismatchMeasure_eq_fourierSum
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (t : Real)
    (hmass : (positiveWeightedMismatchFiniteMeasure m sign).mass ≠ 0) :
    charFun (normalizedPositiveWeightedMismatchMeasure m sign : Measure Real) t =
      ((positiveWeightedMismatchFiniteMeasure m sign).mass⁻¹ : Real) *
        positiveWeightedMismatchFourierSum m sign t := by
  have hmeasure : positiveWeightedMismatchFiniteMeasure m sign ≠ 0 :=
    (positiveWeightedMismatchFiniteMeasure m sign).mass_nonzero_iff.mp hmass
  have hintegral :
      (∫ x : Real, Complex.exp
          ((t : Complex) * (x : Complex) * Complex.I)
        ∂positiveWeightedMismatchMeasure m sign) =
        positiveWeightedMismatchFourierSum m sign t := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      integral_positiveWeightedMismatchMeasure_eq_fourierSum m sign t
  rw [charFun_apply_real]
  unfold normalizedPositiveWeightedMismatchMeasure
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ hmeasure]
  rw [integral_smul_nnreal_measure]
  change (positiveWeightedMismatchFiniteMeasure m sign).mass⁻¹ •
      (∫ x : Real, Complex.exp
          ((t : Complex) * (x : Complex) * Complex.I)
        ∂positiveWeightedMismatchMeasure m sign) = _
  rw [hintegral]
  rfl

/-- Rewriting the finite Fourier sum gives the exact normalized one-leg
spectral-kernel product formula for the characteristic function. -/
theorem charFun_normalizedPositiveWeightedMismatchMeasure_factorization
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign) (t : Real)
    (hmass : (positiveWeightedMismatchFiniteMeasure m sign).mass ≠ 0) :
    charFun (normalizedPositiveWeightedMismatchMeasure m sign : Measure Real) t =
      ((positiveWeightedMismatchFiniteMeasure m sign).mass⁻¹ : Real) *
        (∑ j, ∑ l, ∏ r,
          complexWeightedProjectedBondKernel (massWeightedDifferenceMatrix m)
            (harmonicHermitian m)
            (orderedNormalizedPhaseLeg m sign t r) j l) := by
  rw [charFun_normalizedPositiveWeightedMismatchMeasure_eq_fourierSum
    m sign t hmass, positiveWeightedMismatchFourierSum_factorization]

/-- Levy weak-convergence bridge at fixed finite site type.  The only
asymptotic input is the explicitly supplied pointwise convergence of the
normalized one-leg kernel products to the target characteristic function. -/
theorem tendsto_normalizedPositiveWeightedMismatchMeasure_of_kernelProduct
    {N : Nat} [NeZero N] (m : Nat → Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign)
    (hmass : ∀ n, (positiveWeightedMismatchFiniteMeasure (m n) sign).mass ≠ 0)
    (target : ProbabilityMeasure Real)
    (hkernel : ∀ t : Real,
      Tendsto
        (fun n ↦
          ((positiveWeightedMismatchFiniteMeasure (m n) sign).mass⁻¹ : Real) *
            (∑ j, ∑ l, ∏ r,
              complexWeightedProjectedBondKernel
                (massWeightedDifferenceMatrix (m n))
                (harmonicHermitian (m n))
                (orderedNormalizedPhaseLeg (m n) sign t r) j l))
        atTop (𝓝 (charFun (target : Measure Real) t))) :
    Tendsto (fun n ↦ normalizedPositiveWeightedMismatchMeasure (m n) sign)
      atTop (𝓝 target) := by
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
  intro t
  have hrewrite :
      (fun n ↦ charFun
        (normalizedPositiveWeightedMismatchMeasure (m n) sign : Measure Real) t) =
      (fun n ↦
        ((positiveWeightedMismatchFiniteMeasure (m n) sign).mass⁻¹ : Real) *
          (∑ j, ∑ l, ∏ r,
            complexWeightedProjectedBondKernel
              (massWeightedDifferenceMatrix (m n))
              (harmonicHermitian (m n))
              (orderedNormalizedPhaseLeg (m n) sign t r) j l)) := by
    funext n
    exact charFun_normalizedPositiveWeightedMismatchMeasure_factorization
      (m n) sign t (hmass n)
  rw [hrewrite]
  exact hkernel t


/-- If, in addition to the normalized kernel-product convergence, the total
collision masses converge, then the original unnormalized finite measures
converge weakly.  This retains both the probability shape and its amplitude. -/
theorem tendsto_positiveWeightedMismatchFiniteMeasure_of_mass_and_kernelProduct
    {N : Nat} [NeZero N] (m : Nat → Lattice.PositiveMassConfig N)
    (sign : Fin 3 → InteractionSign)
    (hmass : ∀ n, (positiveWeightedMismatchFiniteMeasure (m n) sign).mass ≠ 0)
    (target : FiniteMeasure Real)
    (hmassLimit : Tendsto
      (fun n ↦ (positiveWeightedMismatchFiniteMeasure (m n) sign).mass)
      atTop (𝓝 target.mass))
    (hkernel : ∀ t : Real,
      Tendsto
        (fun n ↦
          ((positiveWeightedMismatchFiniteMeasure (m n) sign).mass⁻¹ : Real) *
            (∑ j, ∑ l, ∏ r,
              complexWeightedProjectedBondKernel
                (massWeightedDifferenceMatrix (m n))
                (harmonicHermitian (m n))
                (orderedNormalizedPhaseLeg (m n) sign t r) j l))
        atTop (𝓝 (charFun (target.normalize : Measure Real) t))) :
    Tendsto (fun n ↦ positiveWeightedMismatchFiniteMeasure (m n) sign)
      atTop (𝓝 target) := by
  apply FiniteMeasure.tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass
  · simpa [normalizedPositiveWeightedMismatchMeasure] using
      tendsto_normalizedPositiveWeightedMismatchMeasure_of_kernelProduct
        m sign hmass target.normalize hkernel
  · exact hmassLimit

/-- Thermodynamic-size Levy bridge: the finite site count and hence every
internal mode and bond index type may vary with the sequence index, while the
normalized collision measures all live on `Real`. -/
theorem tendsto_varyingSize_normalizedPositiveWeightedMismatchMeasure_of_kernelProduct
    (N : Nat → Nat) [hN : ∀ n, NeZero (N n)]
    (m : ∀ n, Lattice.PositiveMassConfig (N n))
    (sign : Fin 3 → InteractionSign)
    (hmass : ∀ n, (positiveWeightedMismatchFiniteMeasure (m n) sign).mass ≠ 0)
    (target : ProbabilityMeasure Real)
    (hkernel : ∀ t : Real,
      Tendsto
        (fun n ↦
          ((positiveWeightedMismatchFiniteMeasure (m n) sign).mass⁻¹ : Real) *
            (∑ j, ∑ l, ∏ r,
              complexWeightedProjectedBondKernel
                (massWeightedDifferenceMatrix (m n))
                (harmonicHermitian (m n))
                (orderedNormalizedPhaseLeg (m n) sign t r) j l))
        atTop (𝓝 (charFun (target : Measure Real) t))) :
    Tendsto (fun n ↦ normalizedPositiveWeightedMismatchMeasure (m n) sign)
      atTop (𝓝 target) := by
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
  intro t
  simpa only [charFun_normalizedPositiveWeightedMismatchMeasure_factorization
    (m := m _) (sign := sign) (t := t) (hmass _)] using hkernel t

/-- Dependent-size mass-plus-shape bridge.  Pointwise normalized kernel
convergence and total-mass convergence together imply weak convergence of the
original unnormalized collision finite measures. -/
theorem tendsto_varyingSize_positiveWeightedMismatchFiniteMeasure_of_mass_and_kernelProduct
    (N : Nat → Nat) [hN : ∀ n, NeZero (N n)]
    (m : ∀ n, Lattice.PositiveMassConfig (N n))
    (sign : Fin 3 → InteractionSign)
    (hmass : ∀ n, (positiveWeightedMismatchFiniteMeasure (m n) sign).mass ≠ 0)
    (target : FiniteMeasure Real)
    (hmassLimit : Tendsto
      (fun n ↦ (positiveWeightedMismatchFiniteMeasure (m n) sign).mass)
      atTop (𝓝 target.mass))
    (hkernel : ∀ t : Real,
      Tendsto
        (fun n ↦
          ((positiveWeightedMismatchFiniteMeasure (m n) sign).mass⁻¹ : Real) *
            (∑ j, ∑ l, ∏ r,
              complexWeightedProjectedBondKernel
                (massWeightedDifferenceMatrix (m n))
                (harmonicHermitian (m n))
                (orderedNormalizedPhaseLeg (m n) sign t r) j l))
        atTop (𝓝 (charFun (target.normalize : Measure Real) t))) :
    Tendsto (fun n ↦ positiveWeightedMismatchFiniteMeasure (m n) sign)
      atTop (𝓝 target) := by
  apply FiniteMeasure.tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass
  · simpa [normalizedPositiveWeightedMismatchMeasure] using
      tendsto_varyingSize_normalizedPositiveWeightedMismatchMeasure_of_kernelProduct
        N m sign hmass target.normalize hkernel
  · exact hmassLimit
end

end ArchonPhysics.CollisionFourierWeakLimitBridge
