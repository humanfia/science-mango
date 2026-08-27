import ArchonPhysics.RegularizedMarkedLegPolynomialLocality
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Algebra.Polynomial.Div

/-!
# Zero-constant Weierstrass approximation for marked one-leg kernels

The regularized sine and cosine one-leg weights vanish at the acoustic
endpoint.  This module strengthens ordinary Weierstrass approximation on
`[0, 5]` by preserving that zero: subtract the value of an approximating
polynomial at zero, then factor the result as `X * q`.

The finite coefficient list of `q` is exactly the coefficient interface used
by `matrixPolynomialUpTo` and `zeroConstantMatrixPolynomialUpTo`.  Thus the
analytic approximation obtained here feeds directly into the finite-locality
bridge, without introducing a new functional-calculus assumption.
-/

open scoped Matrix Polynomial

namespace ArchonPhysics.RegularizedMarkedLegWeierstrass

open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.RegularizedMarkedLegPolynomialLocality

noncomputable section

/-- Weierstrass approximation on `[0, 5]` can preserve a prescribed zero at
the acoustic endpoint. -/
theorem exists_zeroConstant_polynomial_near_of_continuousOn
    (f : Real → Real) (hf : ContinuousOn f (Set.Icc 0 5))
    (hf0 : f 0 = 0) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ p : Real[X], p.eval 0 = 0 ∧
      ∀ x ∈ Set.Icc (0 : Real) 5, |p.eval x - f x| < epsilon := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn
    0 5 f hf (epsilon / 2) (half_pos hepsilon)
  let pZero : Real[X] := p - Polynomial.C (p.eval 0)
  refine ⟨pZero, ?_, ?_⟩
  · simp [pZero]
  · intro x hx
    have hp0 := hp 0 (by norm_num : (0 : Real) ∈ Set.Icc 0 5)
    have hp0_bound : |p.eval 0| < epsilon / 2 := by
      simpa [hf0] using hp0
    have hpZero_eval :
        pZero.eval x - f x = (p.eval x - f x) - p.eval 0 := by
      simp [pZero]
      ring
    rw [hpZero_eval]
    calc
      |(p.eval x - f x) - p.eval 0| ≤
          |p.eval x - f x| + |p.eval 0| := abs_sub _ _
      _ < epsilon / 2 + epsilon / 2 := add_lt_add (hp x hx) hp0_bound
      _ = epsilon := by ring

/-- A zero-constant approximating polynomial is `X * q`.  This form exposes
the one spectral factor which removes the inverse-square-root singularity. -/
theorem exists_X_mul_polynomial_near_of_continuousOn
    (f : Real → Real) (hf : ContinuousOn f (Set.Icc 0 5))
    (hf0 : f 0 = 0) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ q : Real[X], ∀ x ∈ Set.Icc (0 : Real) 5,
      |x * q.eval x - f x| < epsilon := by
  obtain ⟨p, hp0, hp⟩ :=
    exists_zeroConstant_polynomial_near_of_continuousOn
      f hf hf0 hepsilon
  have hpCoeff : p.coeff 0 = 0 := by
    rw [p.coeff_zero_eq_eval_zero]
    exact hp0
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr hpCoeff
  refine ⟨q, ?_⟩
  intro x hx
  simpa [hq] using hp x hx

/-- Evaluating `X * q` is the finite zero-constant coefficient sum used by
`zeroConstantMatrixPolynomialUpTo`. -/
theorem eval_X_mul_eq_zeroConstantCoefficientSum (q : Real[X]) (x : Real) :
    (Polynomial.X * q).eval x =
      ∑ n ∈ Finset.range (q.natDegree + 1),
        q.coeff n * x ^ (n + 1) := by
  rw [Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [pow_succ]
  ring

/-- Coefficient form of zero-preserving Weierstrass approximation.  The
witnesses `degree` and `coefficient` can be passed unchanged to the matrix
polynomial locality API. -/
theorem exists_zeroConstantCoefficientSum_near_of_continuousOn
    (f : Real → Real) (hf : ContinuousOn f (Set.Icc 0 5))
    (hf0 : f 0 = 0) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ (degree : Nat) (coefficient : Nat → Real),
      ∀ x ∈ Set.Icc (0 : Real) 5,
        abs (
          (∑ n ∈ Finset.range (degree + 1),
            coefficient n * x ^ (n + 1)) - f x
        ) < epsilon := by
  obtain ⟨q, hq⟩ :=
    exists_X_mul_polynomial_near_of_continuousOn f hf hf0 hepsilon
  refine ⟨q.natDegree, q.coeff, ?_⟩
  intro x hx
  rw [← eval_X_mul_eq_zeroConstantCoefficientSum q x]
  simpa using hq x hx

variable {iota : Type*} [Fintype iota] [DecidableEq iota]

/-- The same finite coefficient list defines `M * q(M)` and the existing
zero-constant matrix polynomial. -/
theorem zeroConstantMatrixPolynomialUpTo_eq_mul_matrixPolynomialUpTo
    (degree : Nat) (coefficient : Nat → Real)
    (M : Matrix iota iota Real) :
    zeroConstantMatrixPolynomialUpTo degree coefficient M =
      M * matrixPolynomialUpTo degree coefficient M := by
  unfold zeroConstantMatrixPolynomialUpTo matrixPolynomialUpTo
  rw [Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Matrix.mul_smul, pow_succ']

/-- Explicit coefficient approximation for the regularized cosine leg. -/
theorem exists_regularizedCosineLeg_zeroConstantCoefficientSum
    (time sign : Real) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ (degree : Nat) (coefficient : Nat → Real),
      ∀ lambda ∈ Set.Icc (0 : Real) 5,
        abs (
          (∑ n ∈ Finset.range (degree + 1),
            coefficient n * lambda ^ (n + 1)) -
            regularizedCosineLegWeight time sign lambda
        ) < epsilon := by
  apply exists_zeroConstantCoefficientSum_near_of_continuousOn
  · exact (continuous_regularizedCosineLegWeight time sign).continuousOn
  · simp [regularizedCosineLegWeight]
  · exact hepsilon

/-- Explicit coefficient approximation for the regularized sine leg. -/
theorem exists_regularizedSineLeg_zeroConstantCoefficientSum
    (time sign : Real) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ (degree : Nat) (coefficient : Nat → Real),
      ∀ lambda ∈ Set.Icc (0 : Real) 5,
        abs (
          (∑ n ∈ Finset.range (degree + 1),
            coefficient n * lambda ^ (n + 1)) -
            regularizedSineLegWeight time sign lambda
        ) < epsilon := by
  apply exists_zeroConstantCoefficientSum_near_of_continuousOn
  · exact (continuous_regularizedSineLegWeight time sign).continuousOn
  · simp [regularizedSineLegWeight]
  · exact hepsilon

/-- Multiplying the quotient spectral polynomial by its eigenvalue gives the
same zero-constant coefficient sum that acts on the edge Gram matrix. -/
theorem orderedEigenvalue_mul_spectralPolynomialWeight_eq
    (A : HermitianMatrix iota) (degree : Nat)
    (coefficient : Nat → Real) (k : Fin (Fintype.card iota)) :
    orderedEigenvalue A k *
        spectralPolynomialWeight A degree coefficient k =
      ∑ n ∈ Finset.range (degree + 1),
        coefficient n * orderedEigenvalue A k ^ (n + 1) := by
  unfold spectralPolynomialWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [pow_succ]
  ring

/-- On a finite Hermitian spectrum contained in `[0, 5]`, one quotient
polynomial gives an `epsilon`-accurate regularized cosine weight at every
ordered eigenvalue. -/
theorem exists_regularizedCosineLeg_spectralPolynomialWeight
    (A : HermitianMatrix iota)
    (hband : ∀ k, orderedEigenvalue A k ∈ Set.Icc (0 : Real) 5)
    (time sign : Real) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ (degree : Nat) (coefficient : Nat → Real),
      ∀ k : Fin (Fintype.card iota),
        abs (orderedEigenvalue A k *
            spectralPolynomialWeight A degree coefficient k -
          regularizedCosineLegWeight time sign (orderedEigenvalue A k)) <
          epsilon := by
  obtain ⟨degree, coefficient, happrox⟩ :=
    exists_regularizedCosineLeg_zeroConstantCoefficientSum
      time sign hepsilon
  refine ⟨degree, coefficient, ?_⟩
  intro k
  rw [orderedEigenvalue_mul_spectralPolynomialWeight_eq]
  exact happrox _ (hband k)

/-- The corresponding simultaneous ordered-eigenvalue estimate for the
regularized sine weight. -/
theorem exists_regularizedSineLeg_spectralPolynomialWeight
    (A : HermitianMatrix iota)
    (hband : ∀ k, orderedEigenvalue A k ∈ Set.Icc (0 : Real) 5)
    (time sign : Real) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ (degree : Nat) (coefficient : Nat → Real),
      ∀ k : Fin (Fintype.card iota),
        abs (orderedEigenvalue A k *
            spectralPolynomialWeight A degree coefficient k -
          regularizedSineLegWeight time sign (orderedEigenvalue A k)) <
          epsilon := by
  obtain ⟨degree, coefficient, happrox⟩ :=
    exists_regularizedSineLeg_zeroConstantCoefficientSum
      time sign hepsilon
  refine ⟨degree, coefficient, ?_⟩
  intro k
  rw [orderedEigenvalue_mul_spectralPolynomialWeight_eq]
  exact happrox _ (hband k)

end

end ArchonPhysics.RegularizedMarkedLegWeierstrass
