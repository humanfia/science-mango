import ArchonPhysics.ComplexHarmonicPolynomialMomentFactorization
import ArchonPhysics.RegularizedMarkedLegWeierstrass

/-!
# Volume-uniform complex three-leg Weierstrass data

The cosine and sine parts of all three regularized collision legs are
approximated on the fixed spectral band `[0, 5]`.  The coefficients and one
common locality radius depend only on the requested accuracy, time, and sign
channel, never on the volume or on a mass realization.
-/

namespace ArchonPhysics.ComplexThreeLegWeierstrassApproximation

open ArchonPhysics
open ArchonPhysics.ComplexHarmonicPolynomialMomentFactorization
open ArchonPhysics.ComplexRegularizedMarkedLegBridge
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RegularizedMarkedLegPolynomialLocality
open ArchonPhysics.RegularizedMarkedLegWeierstrass
open ArchonPhysics.ThreeWaveCollisionFourierFactorization
open Set

noncomputable section

/-- One simultaneous polynomial approximation of the three complex marked
legs, with a common finite-propagation radius. -/
structure ComplexThreeLegPolynomialApproximation
    (sign : Fin 3 -> InteractionSign) (time epsilon : Real) where
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
        regularizedCosineLegWeight time (sign r).coefficient lambda) < epsilon
  sine_error : forall r lambda, lambda ∈ Icc (0 : Real) 5 ->
    abs ((∑ n ∈ Finset.range (sineDegree r + 1),
      sineCoefficient r n * lambda ^ (n + 1)) -
        regularizedSineLegWeight time (sign r).coefficient lambda) < epsilon

/-- A common radius can be chosen after the six scalar Weierstrass
approximations, while all coefficients remain independent of volume. -/
theorem exists_complexThreeLegPolynomialApproximation
    (sign : Fin 3 -> InteractionSign) (time : Real)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    Nonempty (ComplexThreeLegPolynomialApproximation sign time epsilon) := by
  have hcos : forall r : Fin 3,
      ∃ (degree : Nat) (coefficient : Nat -> Real),
        forall lambda, lambda ∈ Icc (0 : Real) 5 ->
          abs ((∑ n ∈ Finset.range (degree + 1),
            coefficient n * lambda ^ (n + 1)) -
              regularizedCosineLegWeight time (sign r).coefficient lambda) <
            epsilon := fun r =>
    exists_regularizedCosineLeg_zeroConstantCoefficientSum
      time (sign r).coefficient hepsilon
  choose cosineDegree cosineCoefficient hcosine using hcos
  have hsin : forall r : Fin 3,
      ∃ (degree : Nat) (coefficient : Nat -> Real),
        forall lambda, lambda ∈ Icc (0 : Real) 5 ->
          abs ((∑ n ∈ Finset.range (degree + 1),
            coefficient n * lambda ^ (n + 1)) -
              regularizedSineLegWeight time (sign r).coefficient lambda) <
            epsilon := fun r =>
    exists_regularizedSineLeg_zeroConstantCoefficientSum
      time (sign r).coefficient hepsilon
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

namespace ComplexThreeLegPolynomialApproximation

variable {sign : Fin 3 -> InteractionSign} {time epsilon : Real}
    (approximation : ComplexThreeLegPolynomialApproximation sign time epsilon)

/-- Polynomial cosine effective weights approximate the regularized cosine
weight on every Hermitian spectrum contained in `[0, 5]`. -/
theorem cosine_spectralEffectiveWeight_error
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (A : HermitianMatrix iota)
    (hband : forall k, orderedEigenvalue A k ∈ Icc (0 : Real) 5)
    (r : Fin 3) (k : Fin (Fintype.card iota)) :
    abs (orderedEigenvalue A k *
        spectralPolynomialWeight A (approximation.cosineDegree r)
          (approximation.cosineCoefficient r) k -
      regularizedCosineLegWeight time (sign r).coefficient
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
      regularizedSineLegWeight time (sign r).coefficient
        (orderedEigenvalue A k)) < epsilon := by
  rw [orderedEigenvalue_mul_spectralPolynomialWeight_eq]
  exact approximation.sine_error r _ (hband k)

/-- The real part of the physical normalized phase leg has the same
effective-weight error, uniformly in the volume and realization. -/
theorem harmonic_re_effectiveWeight_error
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hband : forall k,
      orderedEigenvalue (harmonicHermitian m) k ∈ Icc (0 : Real) 5)
    (r : Fin 3) (k : OrderedModeIndex N) :
    abs (orderedEigenvalue (harmonicHermitian m) k *
        (orderedNormalizedPhaseLeg m sign time r k).re -
      orderedEigenvalue (harmonicHermitian m) k *
        spectralPolynomialWeight (harmonicHermitian m)
          (approximation.cosineDegree r)
          (approximation.cosineCoefficient r) k) < epsilon := by
  rw [mul_comm (orderedEigenvalue (harmonicHermitian m) k),
    orderedNormalizedPhaseLeg_re_mul_eigenvalue]
  simpa [abs_sub_comm] using
    approximation.cosine_spectralEffectiveWeight_error
      (harmonicHermitian m) hband r k

/-- Imaginary-part counterpart of
`harmonic_re_effectiveWeight_error`. -/
theorem harmonic_im_effectiveWeight_error
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hband : forall k,
      orderedEigenvalue (harmonicHermitian m) k ∈ Icc (0 : Real) 5)
    (r : Fin 3) (k : OrderedModeIndex N) :
    abs (orderedEigenvalue (harmonicHermitian m) k *
        (orderedNormalizedPhaseLeg m sign time r k).im -
      orderedEigenvalue (harmonicHermitian m) k *
        spectralPolynomialWeight (harmonicHermitian m)
          (approximation.sineDegree r)
          (approximation.sineCoefficient r) k) < epsilon := by
  rw [mul_comm (orderedEigenvalue (harmonicHermitian m) k),
    orderedNormalizedPhaseLeg_im_mul_eigenvalue]
  simpa [abs_sub_comm] using
    approximation.sine_spectralEffectiveWeight_error
      (harmonicHermitian m) hband r k

/-- Combining real and imaginary errors gives a uniform complex effective
weight error. -/
theorem harmonic_complex_effectiveWeight_error
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hband : forall k,
      orderedEigenvalue (harmonicHermitian m) k ∈ Icc (0 : Real) 5)
    (r : Fin 3) (k : OrderedModeIndex N) :
    ‖(orderedEigenvalue (harmonicHermitian m) k : Complex) *
          orderedNormalizedPhaseLeg m sign time r k -
        (orderedEigenvalue (harmonicHermitian m) k : Complex) *
          complexSpectralPolynomialLegWeight (harmonicHermitian m)
            (approximation.cosineDegree r) (approximation.sineDegree r)
            (approximation.cosineCoefficient r)
            (approximation.sineCoefficient r) k‖ < 2 * epsilon := by
  let z : Complex :=
    (orderedEigenvalue (harmonicHermitian m) k : Complex) *
        orderedNormalizedPhaseLeg m sign time r k -
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

end ComplexThreeLegPolynomialApproximation

end

end ArchonPhysics.ComplexThreeLegWeierstrassApproximation
