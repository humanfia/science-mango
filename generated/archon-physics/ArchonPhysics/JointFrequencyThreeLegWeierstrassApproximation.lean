import ArchonPhysics.ComplexThreeLegWeierstrassApproximation
import ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral

/-!
# Joint-frequency three-leg Weierstrass approximation

The three normalized legs of the joint frequency transform carry independent
real parameters.  Six zero-constant polynomials approximate their cosine and
sine effective weights on the common spectral band [0, 5].  One radius
controls all six degrees, independently of the harmonic volume and frozen
mass realization.

This is a fixed-volume approximation bridge.  No joint thermodynamic limit is
asserted.
-/

namespace ArchonPhysics.JointFrequencyThreeLegWeierstrassApproximation

open ArchonPhysics
open ArchonPhysics.ComplexHarmonicPolynomialMomentFactorization
open ArchonPhysics.ComplexRegularizedMarkedLegBridge
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PositiveWeightedFrequencyTripleFourierIntegral
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RegularizedMarkedLegPolynomialLocality
open ArchonPhysics.RegularizedMarkedLegWeierstrass
open ArchonPhysics.ThreeWaveCollisionFourierFactorization
open Set

noncomputable section

/-- Six zero-constant polynomial approximants for three independently
parameterized complex legs, together with one common locality radius. -/
structure JointFrequencyThreeLegPolynomialApproximation
    (parameter : Fin 3 -> Real) (epsilon : Real) where
  windowRadius : Nat
  cosineDegree : Fin 3 -> Nat
  sineDegree : Fin 3 -> Nat
  cosineCoefficient : Fin 3 -> Nat -> Real
  sineCoefficient : Fin 3 -> Nat -> Real
  cosineDegree_le_radius : forall r, cosineDegree r + 1 <= windowRadius
  sineDegree_le_radius : forall r, sineDegree r + 1 <= windowRadius
  cosine_error : forall r lambda, lambda ∈ Icc (0 : Real) 5 ->
    abs ((∑ n ∈ Finset.range (cosineDegree r + 1),
      cosineCoefficient r n * lambda ^ (n + 1)) -
        regularizedCosineLegWeight (parameter r) 1 lambda) < epsilon
  sine_error : forall r lambda, lambda ∈ Icc (0 : Real) 5 ->
    abs ((∑ n ∈ Finset.range (sineDegree r + 1),
      sineCoefficient r n * lambda ^ (n + 1)) -
        regularizedSineLegWeight (parameter r) 1 lambda) < epsilon

/-- The six scalar approximations can be chosen before a volume or frozen
sample is introduced, and their six degrees share one common radius. -/
theorem exists_jointFrequencyThreeLegPolynomialApproximation
    (parameter : Fin 3 -> Real) {epsilon : Real} (hepsilon : 0 < epsilon) :
    Nonempty
      (JointFrequencyThreeLegPolynomialApproximation parameter epsilon) := by
  have hcos : forall r : Fin 3,
      ∃ (degree : Nat) (coefficient : Nat -> Real),
        forall lambda, lambda ∈ Icc (0 : Real) 5 ->
          abs ((∑ n ∈ Finset.range (degree + 1),
            coefficient n * lambda ^ (n + 1)) -
              regularizedCosineLegWeight (parameter r) 1 lambda) <
            epsilon := fun r =>
    exists_regularizedCosineLeg_zeroConstantCoefficientSum
      (parameter r) 1 hepsilon
  choose cosineDegree cosineCoefficient hcosine using hcos
  have hsin : forall r : Fin 3,
      ∃ (degree : Nat) (coefficient : Nat -> Real),
        forall lambda, lambda ∈ Icc (0 : Real) 5 ->
          abs ((∑ n ∈ Finset.range (degree + 1),
            coefficient n * lambda ^ (n + 1)) -
              regularizedSineLegWeight (parameter r) 1 lambda) <
            epsilon := fun r =>
    exists_regularizedSineLeg_zeroConstantCoefficientSum
      (parameter r) 1 hepsilon
  choose sineDegree sineCoefficient hsine using hsin
  let radius : Nat :=
    ∑ r : Fin 3, (cosineDegree r + sineDegree r + 2)
  have hcosRadius : forall r, cosineDegree r + 1 <= radius := by
    intro r
    fin_cases r <;> simp [radius, Fin.sum_univ_succ] <;> omega
  have hsinRadius : forall r, sineDegree r + 1 <= radius := by
    intro r
    fin_cases r <;> simp [radius, Fin.sum_univ_succ] <;> omega
  exact ⟨{
    windowRadius := radius
    cosineDegree := cosineDegree
    sineDegree := sineDegree
    cosineCoefficient := cosineCoefficient
    sineCoefficient := sineCoefficient
    cosineDegree_le_radius := hcosRadius
    sineDegree_le_radius := hsinRadius
    cosine_error := hcosine
    sine_error := hsine
  }⟩

/-- One joint leg depends only on its own parameter coordinate, so it is the
old scalar normalized leg with positive sign and that coordinate as time. -/
theorem orderedJointFrequencyNormalizedPhaseLeg_eq_plusPhaseLeg
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (parameter : Fin 3 -> Real) (r : Fin 3) (k : OrderedModeIndex N) :
    orderedJointFrequencyNormalizedPhaseLeg m parameter r k =
      orderedNormalizedPhaseLeg m
        (fun _ : Fin 3 => InteractionSign.plus) (parameter r) r k := by
  unfold orderedJointFrequencyNormalizedPhaseLeg
    orderedJointFrequencyPhaseLeg orderedNormalizedPhaseLeg orderedPhaseLeg
  simp

/-- Multiplication by the squared frequency turns the real part of one joint
normalized leg into its continuous regularized cosine weight. -/
theorem orderedJointFrequencyNormalizedPhaseLeg_re_mul_eigenvalue
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (parameter : Fin 3 -> Real) (r : Fin 3) (k : OrderedModeIndex N) :
    (orderedJointFrequencyNormalizedPhaseLeg m parameter r k).re *
        orderedEigenvalue (harmonicHermitian m) k =
      regularizedCosineLegWeight (parameter r) 1
        (orderedEigenvalue (harmonicHermitian m) k) := by
  rw [orderedJointFrequencyNormalizedPhaseLeg_eq_plusPhaseLeg]
  simpa using
    (orderedNormalizedPhaseLeg_re_mul_eigenvalue
      m (fun _ : Fin 3 => InteractionSign.plus) (parameter r) r k)

/-- Imaginary-part counterpart of
`orderedJointFrequencyNormalizedPhaseLeg_re_mul_eigenvalue`. -/
theorem orderedJointFrequencyNormalizedPhaseLeg_im_mul_eigenvalue
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (parameter : Fin 3 -> Real) (r : Fin 3) (k : OrderedModeIndex N) :
    (orderedJointFrequencyNormalizedPhaseLeg m parameter r k).im *
        orderedEigenvalue (harmonicHermitian m) k =
      regularizedSineLegWeight (parameter r) 1
        (orderedEigenvalue (harmonicHermitian m) k) := by
  rw [orderedJointFrequencyNormalizedPhaseLeg_eq_plusPhaseLeg]
  simpa using
    (orderedNormalizedPhaseLeg_im_mul_eigenvalue
      m (fun _ : Fin 3 => InteractionSign.plus) (parameter r) r k)

namespace JointFrequencyThreeLegPolynomialApproximation

variable {parameter : Fin 3 -> Real} {epsilon : Real}
    (approximation :
      JointFrequencyThreeLegPolynomialApproximation parameter epsilon)

/-- Polynomial cosine effective weights approximate each independently
parameterized regularized cosine weight on every spectrum in [0, 5]. -/
theorem cosine_spectralEffectiveWeight_error
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (A : HermitianMatrix iota)
    (hband : forall k, orderedEigenvalue A k ∈ Icc (0 : Real) 5)
    (r : Fin 3) (k : Fin (Fintype.card iota)) :
    abs (orderedEigenvalue A k *
        spectralPolynomialWeight A (approximation.cosineDegree r)
          (approximation.cosineCoefficient r) k -
      regularizedCosineLegWeight (parameter r) 1
        (orderedEigenvalue A k)) < epsilon := by
  rw [orderedEigenvalue_mul_spectralPolynomialWeight_eq]
  exact approximation.cosine_error r _ (hband k)

/-- Sine analogue of `cosine_spectralEffectiveWeight_error`. -/
theorem sine_spectralEffectiveWeight_error
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (A : HermitianMatrix iota)
    (hband : forall k, orderedEigenvalue A k ∈ Icc (0 : Real) 5)
    (r : Fin 3) (k : Fin (Fintype.card iota)) :
    abs (orderedEigenvalue A k *
        spectralPolynomialWeight A (approximation.sineDegree r)
          (approximation.sineCoefficient r) k -
      regularizedSineLegWeight (parameter r) 1
        (orderedEigenvalue A k)) < epsilon := by
  rw [orderedEigenvalue_mul_spectralPolynomialWeight_eq]
  exact approximation.sine_error r _ (hband k)

/-- Uniform real-part effective-weight error for every joint leg, volume,
and frozen harmonic realization whose spectrum lies in [0, 5]. -/
theorem harmonic_re_effectiveWeight_error
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hband : forall k,
      orderedEigenvalue (harmonicHermitian m) k ∈ Icc (0 : Real) 5)
    (r : Fin 3) (k : OrderedModeIndex N) :
    abs (orderedEigenvalue (harmonicHermitian m) k *
        (orderedJointFrequencyNormalizedPhaseLeg m parameter r k).re -
      orderedEigenvalue (harmonicHermitian m) k *
        spectralPolynomialWeight (harmonicHermitian m)
          (approximation.cosineDegree r)
          (approximation.cosineCoefficient r) k) < epsilon := by
  rw [mul_comm (orderedEigenvalue (harmonicHermitian m) k),
    orderedJointFrequencyNormalizedPhaseLeg_re_mul_eigenvalue]
  simpa [abs_sub_comm] using
    approximation.cosine_spectralEffectiveWeight_error
      (harmonicHermitian m) hband r k

/-- Uniform imaginary-part effective-weight error for every joint leg. -/
theorem harmonic_im_effectiveWeight_error
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hband : forall k,
      orderedEigenvalue (harmonicHermitian m) k ∈ Icc (0 : Real) 5)
    (r : Fin 3) (k : OrderedModeIndex N) :
    abs (orderedEigenvalue (harmonicHermitian m) k *
        (orderedJointFrequencyNormalizedPhaseLeg m parameter r k).im -
      orderedEigenvalue (harmonicHermitian m) k *
        spectralPolynomialWeight (harmonicHermitian m)
          (approximation.sineDegree r)
          (approximation.sineCoefficient r) k) < epsilon := by
  rw [mul_comm (orderedEigenvalue (harmonicHermitian m) k),
    orderedJointFrequencyNormalizedPhaseLeg_im_mul_eigenvalue]
  simpa [abs_sub_comm] using
    approximation.sine_spectralEffectiveWeight_error
      (harmonicHermitian m) hband r k

/-- Combining the real and imaginary errors gives one volume-uniform complex
effective-weight estimate for all three independently parameterized legs. -/
theorem harmonic_complex_effectiveWeight_error
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hband : forall k,
      orderedEigenvalue (harmonicHermitian m) k ∈ Icc (0 : Real) 5)
    (r : Fin 3) (k : OrderedModeIndex N) :
    ‖(orderedEigenvalue (harmonicHermitian m) k : Complex) *
          orderedJointFrequencyNormalizedPhaseLeg m parameter r k -
        (orderedEigenvalue (harmonicHermitian m) k : Complex) *
          complexSpectralPolynomialLegWeight (harmonicHermitian m)
            (approximation.cosineDegree r) (approximation.sineDegree r)
            (approximation.cosineCoefficient r)
            (approximation.sineCoefficient r) k‖ < 2 * epsilon := by
  let z : Complex :=
    (orderedEigenvalue (harmonicHermitian m) k : Complex) *
        orderedJointFrequencyNormalizedPhaseLeg m parameter r k -
      (orderedEigenvalue (harmonicHermitian m) k : Complex) *
        complexSpectralPolynomialLegWeight (harmonicHermitian m)
          (approximation.cosineDegree r) (approximation.sineDegree r)
          (approximation.cosineCoefficient r)
          (approximation.sineCoefficient r) k
  have hre : abs z.re < epsilon := by
    simpa [z, complexSpectralPolynomialLegWeight] using
      approximation.harmonic_re_effectiveWeight_error m hband r k
  have him : abs z.im < epsilon := by
    simpa [z, complexSpectralPolynomialLegWeight] using
      approximation.harmonic_im_effectiveWeight_error m hband r k
  calc
    ‖z‖ <= abs z.re + abs z.im := Complex.norm_le_abs_re_add_abs_im z
    _ < epsilon + epsilon := add_lt_add hre him
    _ = 2 * epsilon := by ring

end JointFrequencyThreeLegPolynomialApproximation

end

end ArchonPhysics.JointFrequencyThreeLegWeierstrassApproximation
