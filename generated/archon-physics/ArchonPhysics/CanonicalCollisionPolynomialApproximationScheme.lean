import ArchonPhysics.ComplexThreeLegWeierstrassApproximation
import ArchonPhysics.NormalizedPhaseEffectiveWeightBound
import ArchonPhysics.VanishingUniformApproximationLimit

/-!
# Canonical vanishing-error polynomial scheme for collision legs

This file fixes one countable family of simultaneous three-leg polynomial
approximations with tolerance `1 / (k + 1)`.  It also records the explicit
volume-uniform three-leg replacement error and proves that this error tends
to zero.
-/

namespace ArchonPhysics.CanonicalCollisionPolynomialApproximationScheme

open ArchonPhysics
open ArchonPhysics.ComplexThreeLegWeierstrassApproximation
open ArchonPhysics.ComplexHarmonicPolynomialMomentFactorization
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedPhaseEffectiveWeightBound
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RegularizedMarkedLegPolynomialLocality
open ArchonPhysics.ThreeWaveCollisionFourierFactorization
open Filter Topology

noncomputable section

/-- Positive scalar accuracy used by the countable approximation family. -/
def collisionApproximationTolerance (k : Nat) : Real :=
  1 / ((k : Real) + 1)

theorem collisionApproximationTolerance_pos (k : Nat) :
    0 < collisionApproximationTolerance k := by
  unfold collisionApproximationTolerance
  positivity

theorem collisionApproximationTolerance_tendsto_zero :
    Tendsto collisionApproximationTolerance atTop (𝓝 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- A chosen simultaneous approximation at every positive tolerance.  Its
coefficients and common radius depend on `k`, time, and sign, but not on
volume or on a mass sample. -/
def collisionPolynomialApproximation
    (sign : Fin 3 -> InteractionSign) (time : Real) (k : Nat) :
    ComplexThreeLegPolynomialApproximation sign time
      (collisionApproximationTolerance k) :=
  Classical.choice (exists_complexThreeLegPolynomialApproximation sign time
    (collisionApproximationTolerance_pos k))

/-- The one chosen object simultaneously carries all six scalar
approximations and a common propagation radius. -/
theorem collisionPolynomialApproximation_spec
    (sign : Fin 3 -> InteractionSign) (time : Real) (k : Nat) :
    (forall r,
      (collisionPolynomialApproximation sign time k).cosineDegree r + 1 <=
        (collisionPolynomialApproximation sign time k).windowRadius) ∧
    (forall r,
      (collisionPolynomialApproximation sign time k).sineDegree r + 1 <=
        (collisionPolynomialApproximation sign time k).windowRadius) ∧
    (forall r lambda, lambda ∈ Set.Icc (0 : Real) 5 ->
      abs ((∑ n ∈ Finset.range
          ((collisionPolynomialApproximation sign time k).cosineDegree r + 1),
        (collisionPolynomialApproximation sign time k).cosineCoefficient r n *
          lambda ^ (n + 1)) -
        regularizedCosineLegWeight time (sign r).coefficient lambda) <
          collisionApproximationTolerance k ∧
      abs ((∑ n ∈ Finset.range
          ((collisionPolynomialApproximation sign time k).sineDegree r + 1),
        (collisionPolynomialApproximation sign time k).sineCoefficient r n *
          lambda ^ (n + 1)) -
        regularizedSineLegWeight time (sign r).coefficient lambda) <
          collisionApproximationTolerance k) := by
  let approximation := collisionPolynomialApproximation sign time k
  exact ⟨approximation.cosineDegree_le_radius,
    approximation.sineDegree_le_radius,
    fun r lambda hlambda ↦
      ⟨approximation.cosine_error r lambda hlambda,
        approximation.sine_error r lambda hlambda⟩⟩

/-- Uniform norm bound for the exact effective normalized phase weight. -/
def collisionPhysicalEffectiveBound : Real := Real.sqrt 5 / 2

theorem collisionPhysicalEffectiveBound_nonneg :
    0 <= collisionPhysicalEffectiveBound := by
  unfold collisionPhysicalEffectiveBound
  positivity

/-- `collisionPhysicalEffectiveBound` really bounds every exact effective
normalized phase leg on the frozen spectral band. -/
theorem norm_collisionPhysicalEffectiveWeight_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hband : forall q, orderedEigenvalue (harmonicHermitian m) q <= 5)
    (sign : Fin 3 -> InteractionSign) (time : Real)
    (r : Fin 3) (q : OrderedModeIndex N) :
    ‖(orderedEigenvalue (harmonicHermitian m) q : Complex) *
        orderedNormalizedPhaseLeg m sign time r q‖ <=
      collisionPhysicalEffectiveBound := by
  exact
    norm_eigenvalue_mul_orderedNormalizedPhaseLeg_le_sqrtFive_div_two
      m hband sign time r q

/-- Effective-weight error supplied by the real/imaginary approximation. -/
def collisionComplexEffectiveError (k : Nat) : Real :=
  2 * collisionApproximationTolerance k

theorem collisionComplexEffectiveError_nonneg (k : Nat) :
    0 <= collisionComplexEffectiveError k := by
  unfold collisionComplexEffectiveError
  exact mul_nonneg (by norm_num) (collisionApproximationTolerance_pos k).le

theorem collisionComplexEffectiveError_tendsto_zero :
    Tendsto collisionComplexEffectiveError atTop (𝓝 0) := by
  change Tendsto (fun k => 2 * collisionApproximationTolerance k)
    atTop (𝓝 0)
  simpa only [mul_zero] using
    collisionApproximationTolerance_tendsto_zero.const_mul 2

/-- Triangle-inequality bound for each polynomial effective weight. -/
def collisionPolynomialEffectiveBound (k : Nat) : Real :=
  collisionPhysicalEffectiveBound + collisionComplexEffectiveError k

theorem collisionPolynomialEffectiveBound_nonneg (k : Nat) :
    0 <= collisionPolynomialEffectiveBound k := by
  unfold collisionPolynomialEffectiveBound
  exact add_nonneg collisionPhysicalEffectiveBound_nonneg
    (collisionComplexEffectiveError_nonneg k)

/-- The chosen polynomial effective leg is bounded by `M + delta_k`, where
`M` is the physical bound and `delta_k = 2 * epsilon_k` is its complex
approximation error. -/
theorem norm_collisionPolynomialEffectiveWeight_le
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hband : forall q,
      orderedEigenvalue (harmonicHermitian m) q ∈ Set.Icc (0 : Real) 5)
    (sign : Fin 3 -> InteractionSign) (time : Real) (k : Nat)
    (r : Fin 3) (q : OrderedModeIndex N) :
    ‖(orderedEigenvalue (harmonicHermitian m) q : Complex) *
        complexSpectralPolynomialLegWeight (harmonicHermitian m)
          ((collisionPolynomialApproximation sign time k).cosineDegree r)
          ((collisionPolynomialApproximation sign time k).sineDegree r)
          ((collisionPolynomialApproximation sign time k).cosineCoefficient r)
          ((collisionPolynomialApproximation sign time k).sineCoefficient r)
          q‖ <= collisionPolynomialEffectiveBound k := by
  let approximation := collisionPolynomialApproximation sign time k
  let physical : Complex :=
    (orderedEigenvalue (harmonicHermitian m) q : Complex) *
      orderedNormalizedPhaseLeg m sign time r q
  let polynomial : Complex :=
    (orderedEigenvalue (harmonicHermitian m) q : Complex) *
      complexSpectralPolynomialLegWeight (harmonicHermitian m)
        (approximation.cosineDegree r) (approximation.sineDegree r)
        (approximation.cosineCoefficient r)
        (approximation.sineCoefficient r) q
  have hdifference : ‖physical - polynomial‖ <=
      collisionComplexEffectiveError k := by
    unfold collisionComplexEffectiveError
    exact
      (approximation.harmonic_complex_effectiveWeight_error
        m hband r q).le
  have hphysical : ‖physical‖ <= collisionPhysicalEffectiveBound := by
    exact norm_collisionPhysicalEffectiveWeight_le m
      (fun q ↦ (hband q).2) sign time r q
  change ‖polynomial‖ <= collisionPolynomialEffectiveBound k
  calc
    ‖polynomial‖ = ‖(polynomial - physical) + physical‖ := by
      rw [sub_add_cancel]
    _ <= ‖polynomial - physical‖ + ‖physical‖ := norm_add_le _ _
    _ <= collisionComplexEffectiveError k +
        collisionPhysicalEffectiveBound := by
      exact add_le_add (by simpa [norm_sub_rev] using hdifference) hphysical
    _ = collisionPolynomialEffectiveBound k := by
      unfold collisionPolynomialEffectiveBound
      ring

theorem collisionPolynomialEffectiveBound_tendsto :
    Tendsto collisionPolynomialEffectiveBound atTop
      (𝓝 collisionPhysicalEffectiveBound) := by
  change Tendsto (fun k => collisionPhysicalEffectiveBound +
    collisionComplexEffectiveError k) atTop
      (𝓝 collisionPhysicalEffectiveBound)
  simpa only [add_zero] using
    tendsto_const_nhds.add collisionComplexEffectiveError_tendsto_zero

/-- Explicit per-site three-leg error obtained from telescoping the three
complex projected kernels. -/
def collisionThreeLegReplacementError (k : Nat) : Real :=
  collisionComplexEffectiveError k * collisionPhysicalEffectiveBound *
      collisionPhysicalEffectiveBound +
    collisionComplexEffectiveError k * collisionPolynomialEffectiveBound k *
      collisionPhysicalEffectiveBound +
    collisionComplexEffectiveError k * collisionPolynomialEffectiveBound k *
      collisionPolynomialEffectiveBound k

theorem collisionThreeLegReplacementError_nonneg (k : Nat) :
    0 <= collisionThreeLegReplacementError k := by
  unfold collisionThreeLegReplacementError
  have hdelta := collisionComplexEffectiveError_nonneg k
  have hphysical := collisionPhysicalEffectiveBound_nonneg
  have hpolynomial := collisionPolynomialEffectiveBound_nonneg k
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (mul_nonneg hdelta hphysical) hphysical)
      (mul_nonneg (mul_nonneg hdelta hpolynomial) hphysical))
    (mul_nonneg (mul_nonneg hdelta hpolynomial) hpolynomial)

/-- The deterministic volume-uniform replacement error vanishes. -/
theorem collisionThreeLegReplacementError_tendsto_zero :
    Tendsto collisionThreeLegReplacementError atTop (𝓝 0) := by
  have hdelta := collisionComplexEffectiveError_tendsto_zero
  have hphysical : Tendsto (fun _ : Nat => collisionPhysicalEffectiveBound)
      atTop (𝓝 collisionPhysicalEffectiveBound) := tendsto_const_nhds
  have hpolynomial := collisionPolynomialEffectiveBound_tendsto
  have hfirst := (hdelta.mul hphysical).mul hphysical
  have hsecond := (hdelta.mul hpolynomial).mul hphysical
  have hthird := (hdelta.mul hpolynomial).mul hpolynomial
  change Tendsto (fun k =>
    collisionComplexEffectiveError k * collisionPhysicalEffectiveBound *
        collisionPhysicalEffectiveBound +
      collisionComplexEffectiveError k * collisionPolynomialEffectiveBound k *
        collisionPhysicalEffectiveBound +
      collisionComplexEffectiveError k * collisionPolynomialEffectiveBound k *
        collisionPolynomialEffectiveBound k) atTop (𝓝 0)
  simpa only [zero_mul, zero_add] using
    (hfirst.add hsecond).add hthird

end

end ArchonPhysics.CanonicalCollisionPolynomialApproximationScheme
