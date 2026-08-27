import ArchonPhysics.OrderedProjectedResolventBridge
import ArchonPhysics.MassWeightedCycleBridge
import ArchonPhysics.RandomMassHarmonicSecondMoment

/-!
# Regularized marked one-leg kernels and polynomial locality

The positive-frequency factor `(2 * sqrt lambda)⁻¹` is singular before the
two discrete gradients in a projected bond kernel are taken into account.
This file records the finite-dimensional algebra that removes that apparent
singularity.  Multiplication by the spectral factor `lambda` changes it into
the continuous weight `sqrt lambda / 2` (and likewise after adding a sine or
cosine phase).

For matrices, a polynomial with zero constant term is represented as
`p(x) = x q(x)`.  The exact Gram identity

`p (B Bᵀ) = B q (Bᵀ B) Bᵀ`

then turns a polynomial approximation to the regularized edge-space kernel
into a site-space spectral-projector sandwich.  A generic walk argument proves
finite propagation of the polynomial matrix kernel.  The final theorem
specializes this to the weighted periodic cycle of the random-mass harmonic
chain.  No infinite-volume limit or polynomial approximation theorem is
asserted here.
-/

open scoped Matrix

namespace ArchonPhysics.RegularizedMarkedLegPolynomialLocality

open ArchonPhysics
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MassWeightedCycleBridge
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedInteractionSpectralFactorization
open ArchonPhysics.OrderedProjectedResolventBridge
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassHarmonicSecondMoment

noncomputable section

/-! ## Scalar removal of the positive-frequency singularity -/

/-- The apparent inverse-square-root singularity is removed by one spectral
factor `lambda`.  The totalized inverse makes the identity valid also at
`lambda = 0`. -/
theorem inverseTwoSqrt_mul_self
    {lambda : Real} (hlambda : 0 ≤ lambda) :
    (2 * Real.sqrt lambda)⁻¹ * lambda = Real.sqrt lambda / 2 := by
  by_cases hlambda0 : lambda = 0
  · simp [hlambda0]
  · have hlambda_pos : 0 < lambda := lt_of_le_of_ne hlambda (Ne.symm hlambda0)
    have hsqrt : Real.sqrt lambda ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hlambda_pos)
    have hlambda_eq : lambda = Real.sqrt lambda * Real.sqrt lambda := by
      simpa [pow_two] using (Real.sq_sqrt hlambda).symm
    calc
      (2 * Real.sqrt lambda)⁻¹ * lambda =
          (2 * Real.sqrt lambda)⁻¹ *
            (Real.sqrt lambda * Real.sqrt lambda) :=
        congrArg (fun x : Real ↦ (2 * Real.sqrt lambda)⁻¹ * x) hlambda_eq
      _ = Real.sqrt lambda / 2 := by field_simp

/-- Real part of the regularized oscillatory one-leg spectral weight. -/
def regularizedCosineLegWeight (time sign lambda : Real) : Real :=
  Real.sqrt lambda / 2 * Real.cos (sign * time * Real.sqrt lambda)

/-- Imaginary part of the regularized oscillatory one-leg spectral weight. -/
def regularizedSineLegWeight (time sign lambda : Real) : Real :=
  Real.sqrt lambda / 2 * Real.sin (sign * time * Real.sqrt lambda)

theorem continuous_regularizedCosineLegWeight (time sign : Real) :
    Continuous (regularizedCosineLegWeight time sign) := by
  unfold regularizedCosineLegWeight
  fun_prop

theorem continuous_regularizedSineLegWeight (time sign : Real) :
    Continuous (regularizedSineLegWeight time sign) := by
  unfold regularizedSineLegWeight
  fun_prop

/-- After the two-gradient spectral factor is exposed, the normalized cosine
weight is exactly the continuous regularized cosine weight. -/
theorem normalizedCosineLeg_mul_eigenvalue
    {lambda time sign : Real} (hlambda : 0 ≤ lambda) :
    ((2 * Real.sqrt lambda)⁻¹ *
        Real.cos (sign * time * Real.sqrt lambda)) * lambda =
      regularizedCosineLegWeight time sign lambda := by
  rw [mul_assoc, mul_comm (Real.cos _) lambda, ← mul_assoc,
    inverseTwoSqrt_mul_self hlambda]
  simp [regularizedCosineLegWeight, mul_comm]

/-- The corresponding exact identity for the sine component. -/
theorem normalizedSineLeg_mul_eigenvalue
    {lambda time sign : Real} (hlambda : 0 ≤ lambda) :
    ((2 * Real.sqrt lambda)⁻¹ *
        Real.sin (sign * time * Real.sqrt lambda)) * lambda =
      regularizedSineLegWeight time sign lambda := by
  rw [mul_assoc, mul_comm (Real.sin _) lambda, ← mul_assoc,
    inverseTwoSqrt_mul_self hlambda]
  simp [regularizedSineLegWeight, mul_comm]

/-! ## Zero-constant polynomial Gram bridge -/

variable {site bond : Type*}
variable [Fintype site] [DecidableEq site]
variable [Fintype bond] [DecidableEq bond]

/-- Matrix polynomial `q(M) = sum_{n=0}^degree coefficient(n) M^n`. -/
def matrixPolynomialUpTo (degree : Nat) (coefficient : Nat → Real)
    (M : Matrix site site Real) : Matrix site site Real :=
  ∑ n ∈ Finset.range (degree + 1), coefficient n • M ^ n

/-- The zero-constant polynomial `p(M) = M q(M)`, written coefficientwise as
`sum coefficient(n) M^(n+1)`. -/
def zeroConstantMatrixPolynomialUpTo (degree : Nat)
    (coefficient : Nat → Real) (M : Matrix site site Real) :
    Matrix site site Real :=
  ∑ n ∈ Finset.range (degree + 1), coefficient n • M ^ (n + 1)

/-- Powers of the edge Gram matrix factor through powers of the site Gram
matrix. -/
theorem selfTranspose_pow_succ (B : Matrix bond site Real) (n : Nat) :
    (B * B.transpose) ^ (n + 1) =
      B * (B.transpose * B) ^ n * B.transpose := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]

/-- Exact matrix form of `p(x) = x q(x)` for a zero-constant polynomial. -/
theorem zeroConstantMatrixPolynomial_selfTranspose
    (B : Matrix bond site Real) (degree : Nat)
    (coefficient : Nat → Real) :
    zeroConstantMatrixPolynomialUpTo degree coefficient (B * B.transpose) =
      B * matrixPolynomialUpTo degree coefficient (B.transpose * B) *
        B.transpose := by
  unfold zeroConstantMatrixPolynomialUpTo matrixPolynomialUpTo
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Matrix.mul_smul, Matrix.smul_mul, selfTranspose_pow_succ]

/-! ## Polynomial ordered-projector functional calculus -/

/-- Scalar evaluation of the coefficientwise matrix polynomial. -/
def spectralPolynomialWeight {iota : Type*} [Fintype iota] [DecidableEq iota]
    (A : HermitianMatrix iota) (degree : Nat) (coefficient : Nat → Real)
    (k : Fin (Fintype.card iota)) : Real :=
  ∑ n ∈ Finset.range (degree + 1),
    coefficient n * orderedEigenvalue A k ^ n

theorem matrixVal_pow_mulVec_eigenvectorBasis
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (A : HermitianMatrix iota) (n : Nat)
    (r : Fin (Fintype.card iota)) :
    matrixVal A ^ n *ᵥ
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) =
      orderedEigenvalue A r ^ n •
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul,
        matrixVal_mulVec_eigenvectorBasis, smul_smul]
      simp [pow_succ]

theorem matrixPolynomialUpTo_mulVec_eigenvectorBasis
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (A : HermitianMatrix iota) (degree : Nat) (coefficient : Nat → Real)
    (r : Fin (Fintype.card iota)) :
    matrixPolynomialUpTo degree coefficient (matrixVal A) *ᵥ
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) =
      spectralPolynomialWeight A degree coefficient r •
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) := by
  unfold matrixPolynomialUpTo spectralPolynomialWeight
  simp_rw [Matrix.sum_mulVec, Matrix.smul_mulVec,
    matrixVal_pow_mulVec_eigenvectorBasis A, smul_smul]
  rw [Finset.sum_smul]

/-- On simple spectrum, the ordered-projector functional calculus of a
polynomial is exactly the corresponding matrix polynomial. -/
theorem sum_spectralPolynomialWeight_smul_orderedModeProjector
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (A : HermitianMatrix iota) (hsimple : SimpleOrderedSpectrum A)
    (degree : Nat) (coefficient : Nat → Real) :
    (∑ k : Fin (Fintype.card iota),
        spectralPolynomialWeight A degree coefficient k •
          orderedModeProjector A k) =
      matrixPolynomialUpTo degree coefficient (matrixVal A) := by
  apply matrix_eq_of_mulVec_eigenvectorBasis_eq A
  intro r
  rw [Matrix.sum_mulVec]
  simp [Matrix.smul_mulVec,
    orderedModeProjector_mulVec_eigenvectorBasis A hsimple,
    matrixPolynomialUpTo_mulVec_eigenvectorBasis A degree coefficient r]

omit [Fintype bond] [DecidableEq bond] in
/-- A polynomially weighted projected-bond kernel is the exact polynomial
matrix sandwich. -/
theorem weightedProjectedBondKernel_spectralPolynomial
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (B : Matrix bond iota Real) (A : HermitianMatrix iota)
    (hsimple : SimpleOrderedSpectrum A) (degree : Nat)
    (coefficient : Nat → Real) :
    weightedProjectedBondKernel B A
        (spectralPolynomialWeight A degree coefficient) =
      B * matrixPolynomialUpTo degree coefficient (matrixVal A) *
        B.transpose := by
  rw [weightedProjectedBondKernel_eq_projectorSumSandwich,
    sum_spectralPolynomialWeight_smul_orderedModeProjector A hsimple]

/-- If `A = Bᵀ B`, the same polynomially weighted spectral kernel is a
zero-constant polynomial of the edge Gram matrix `B Bᵀ`. -/
theorem weightedProjectedBondKernel_spectralPolynomial_eq_edgePolynomial
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (B : Matrix bond iota Real) (A : HermitianMatrix iota)
    (hsimple : SimpleOrderedSpectrum A)
    (hgram : matrixVal A = B.transpose * B)
    (degree : Nat) (coefficient : Nat → Real) :
    weightedProjectedBondKernel B A
        (spectralPolynomialWeight A degree coefficient) =
      zeroConstantMatrixPolynomialUpTo degree coefficient
        (B * B.transpose) := by
  rw [weightedProjectedBondKernel_spectralPolynomial B A hsimple,
    hgram, ← zeroConstantMatrixPolynomial_selfTranspose]

/-! ## Generic finite propagation -/

/-- A matrix walk of exactly `n` steps in a prescribed support relation. -/
def MatrixWalk {iota : Type*} (step : iota → iota → Prop) :
    Nat → iota → iota → Prop
  | 0, i, j => i = j
  | n + 1, i, j => ∃ k, MatrixWalk step n i k ∧ step k j

/-- Reachability by at most `degree` matrix-support steps. -/
def MatrixReachableWithin {iota : Type*} (step : iota → iota → Prop)
    (degree : Nat) (i j : iota) : Prop :=
  ∃ n, n ≤ degree ∧ MatrixWalk step n i j

/-- Every nonzero matrix entry is supported on `step`. -/
def MatrixSupportedOn {iota : Type*} [Fintype iota]
    (step : iota → iota → Prop) (M : Matrix iota iota Real) : Prop :=
  ∀ i j, M i j ≠ 0 → step i j

theorem matrix_pow_apply_eq_zero_of_not_walk
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    {step : iota → iota → Prop} {M : Matrix iota iota Real}
    (hM : MatrixSupportedOn step M) {n : Nat} {i j : iota}
    (hwalk : ¬ MatrixWalk step n i j) :
    (M ^ n) i j = 0 := by
  induction n generalizing j with
  | zero =>
      simp [MatrixWalk] at hwalk
      simp [hwalk]
  | succ n ih =>
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro k hk
      by_cases hik : MatrixWalk step n i k
      · have hkj : ¬ step k j := by
          intro hstep
          exact hwalk ⟨k, hik, hstep⟩
        have hzero : M k j = 0 := by
          by_contra hne
          exact hkj (hM k j hne)
        rw [hzero, mul_zero]
      · rw [ih hik, zero_mul]

/-- A degree-`degree` polynomial matrix has no entries beyond
`degree` support steps. -/
theorem matrixPolynomialUpTo_apply_eq_zero_of_not_reachableWithin
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    {step : iota → iota → Prop} {M : Matrix iota iota Real}
    (hM : MatrixSupportedOn step M) (degree : Nat)
    (coefficient : Nat → Real) {i j : iota}
    (hreach : ¬ MatrixReachableWithin step degree i j) :
    matrixPolynomialUpTo degree coefficient M i j = 0 := by
  unfold matrixPolynomialUpTo
  rw [Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro n hn
  have hnle : n ≤ degree := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  have hnwalk : ¬ MatrixWalk step n i j := by
    intro hwalk
    exact hreach ⟨n, hnle, hwalk⟩
  rw [Matrix.smul_apply, matrix_pow_apply_eq_zero_of_not_walk hM hnwalk]
  simp

/-- A zero-constant polynomial with quotient degree `degree` propagates at
most `degree + 1` steps. -/
theorem zeroConstantMatrixPolynomialUpTo_apply_eq_zero_of_not_reachableWithin
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    {step : iota → iota → Prop} {M : Matrix iota iota Real}
    (hM : MatrixSupportedOn step M) (degree : Nat)
    (coefficient : Nat → Real) {i j : iota}
    (hreach : ¬ MatrixReachableWithin step (degree + 1) i j) :
    zeroConstantMatrixPolynomialUpTo degree coefficient M i j = 0 := by
  unfold zeroConstantMatrixPolynomialUpTo
  rw [Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro n hn
  have hnle : n + 1 ≤ degree + 1 :=
    Nat.succ_le_succ (Nat.le_of_lt_succ (Finset.mem_range.mp hn))
  have hnwalk : ¬ MatrixWalk step (n + 1) i j := by
    intro hwalk
    exact hreach ⟨n + 1, hnle, hwalk⟩
  rw [Matrix.smul_apply, matrix_pow_apply_eq_zero_of_not_walk hM hnwalk]
  simp

/-- Equality of an entry of a matrix power only uses matrix entries along
walks of smaller length starting at its left endpoint.  This is the finite
window extensionality interface used to turn polynomial kernels into local
random observables. -/
theorem matrix_pow_apply_eq_of_walkLocalAgreement
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    {step : iota → iota → Prop} {M M' : Matrix iota iota Real}
    (hM : MatrixSupportedOn step M) (hM' : MatrixSupportedOn step M')
    {n : Nat} {i j : iota}
    (hagree : ∀ r, r < n → ∀ u v,
      MatrixWalk step r i u → step u v → M u v = M' u v) :
    (M ^ n) i j = (M' ^ n) i j := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hik : MatrixWalk step n i k
      · have hpow : (M ^ n) i k = (M' ^ n) i k :=
          ih (fun r hr u v hwalk hstep ↦
            hagree r (lt_trans hr (Nat.lt_succ_self n)) u v hwalk hstep)
        have hentry : M k j = M' k j := by
          by_cases hstep : step k j
          · exact hagree n (Nat.lt_succ_self n) k j hik hstep
          · have hzero : M k j = 0 := by
              by_contra hne
              exact hstep (hM k j hne)
            have hzero' : M' k j = 0 := by
              by_contra hne
              exact hstep (hM' k j hne)
            rw [hzero, hzero']
        rw [hpow, hentry]
      · rw [matrix_pow_apply_eq_zero_of_not_walk hM hik,
          matrix_pow_apply_eq_zero_of_not_walk hM' hik]
        simp

/-- Consequently, one row entry of a degree-bounded polynomial kernel depends
only on support edges leaving vertices reachable in fewer than degree steps. -/
theorem matrixPolynomialUpTo_apply_eq_of_walkLocalAgreement
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    {step : iota → iota → Prop} {M M' : Matrix iota iota Real}
    (hM : MatrixSupportedOn step M) (hM' : MatrixSupportedOn step M')
    (degree : Nat) (coefficient : Nat → Real) {i j : iota}
    (hagree : ∀ r, r < degree → ∀ u v,
      MatrixWalk step r i u → step u v → M u v = M' u v) :
    matrixPolynomialUpTo degree coefficient M i j =
      matrixPolynomialUpTo degree coefficient M' i j := by
  unfold matrixPolynomialUpTo
  rw [Matrix.sum_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  have hnle : n ≤ degree := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  have hpow : (M ^ n) i j = (M' ^ n) i j :=
    matrix_pow_apply_eq_of_walkLocalAgreement hM hM'
      (fun r hr u v hwalk hstep ↦
        hagree r (lt_of_lt_of_le hr hnle) u v hwalk hstep)
  simp only [Matrix.smul_apply]
  rw [hpow]

/-! ## Periodic weighted-cycle specialization -/

/-- One diagonal or nearest-neighbour step on the periodic chain. -/
def periodicCycleStep {N : Nat} (i j : Lattice.Site N) : Prop :=
  j = i ∨ j = i + 1 ∨ j = i - 1

theorem weightedCycleLaplacian_supportedOn_periodicCycleStep
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    (w : Lattice.Configuration N) :
    MatrixSupportedOn periodicCycleStep (weightedCycleLaplacian w) := by
  intro i j hne
  rw [weightedCycleLaplacian_apply_piecewise hN w i] at hne
  by_cases hzero : j = i
  · exact Or.inl hzero
  · by_cases hnext : j = i + 1
    · exact Or.inr (Or.inl hnext)
    · by_cases hprev : j = i - 1
      · exact Or.inr (Or.inr hprev)
      · simp [hzero, hnext, hprev] at hne

/-- Exact polynomial one-leg bridge for one positive-mass periodic chain.
The right side is a polynomial in the local edge-space weighted-cycle
Laplacian and has zero constant term. -/
theorem harmonicWeightedProjectedBondKernel_spectralPolynomial_eq_weightedCycle
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (degree : Nat) (coefficient : Nat → Real) :
    weightedProjectedBondKernel (massWeightedDifferenceMatrix m)
        (harmonicHermitian m)
        (spectralPolynomialWeight (harmonicHermitian m) degree coefficient) =
      zeroConstantMatrixPolynomialUpTo degree coefficient
        (weightedCycleLaplacian (fun i ↦ (m.mass i)⁻¹)) := by
  rw [weightedProjectedBondKernel_spectralPolynomial_eq_edgePolynomial
    (massWeightedDifferenceMatrix m) (harmonicHermitian m) hsimple]
  · rw [massWeighted_selfTranspose_eq_weightedCycleLaplacian]
  · rfl

/-- Terminal locality theorem: a quotient polynomial of degree `degree`
produces a marked one-leg bond kernel supported within `degree + 1` periodic
nearest-neighbour steps. -/
theorem harmonicWeightedProjectedBondKernel_spectralPolynomial_eq_zero_of_far
    {N : Nat} [NeZero N] (hN : 3 ≤ N)
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (degree : Nat) (coefficient : Nat → Real)
    {j l : Lattice.Site N}
    (hfar : ¬ MatrixReachableWithin periodicCycleStep (degree + 1) j l) :
    weightedProjectedBondKernel (massWeightedDifferenceMatrix m)
        (harmonicHermitian m)
        (spectralPolynomialWeight (harmonicHermitian m) degree coefficient)
        j l = 0 := by
  rw [harmonicWeightedProjectedBondKernel_spectralPolynomial_eq_weightedCycle
    m hsimple]
  exact zeroConstantMatrixPolynomialUpTo_apply_eq_zero_of_not_reachableWithin
    (weightedCycleLaplacian_supportedOn_periodicCycleStep hN
      (fun i ↦ (m.mass i)⁻¹)) degree coefficient hfar

end

end ArchonPhysics.RegularizedMarkedLegPolynomialLocality
