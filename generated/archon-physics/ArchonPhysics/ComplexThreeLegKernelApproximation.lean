import ArchonPhysics.ThreeLegKernelApproximationAlgebra

/-!
# Complex projected-kernel approximation bounds

A real orthonormal frame diagonalizes complex weighted projected-bond kernels
as well: their Frobenius square is the sum of squared norms of the complex
effective weights.  This module supplies entrywise and Frobenius estimates
that feed directly into the three-leg telescoping algebra.
-/

open scoped BigOperators

namespace ArchonPhysics.ComplexThreeLegKernelApproximation

open ArchonPhysics.MeasurableOrderedModeCoupling
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedInteractionSpectralFactorization
open ArchonPhysics.ThreeLegKernelApproximationAlgebra
open ArchonPhysics.ThreeWaveCollisionFourierFactorization

noncomputable section

variable {mode bond : Type*} [Fintype mode] [DecidableEq mode]
  [Fintype bond]

def complexSpectralKernel (u : mode → bond → Real)
    (w : mode → Complex) : bond → bond → Complex :=
  fun j l ↦ ∑ k, w k * (u k j : Complex) * (u k l : Complex)

omit [DecidableEq mode] [Fintype bond] in
theorem complexSpectralKernel_re
    (u : mode → bond → Real) (w : mode → Complex) (j l : bond) :
    (complexSpectralKernel u w j l).re =
      spectralKernel u (fun k ↦ (w k).re) j l := by
  simp [complexSpectralKernel, spectralKernel, Complex.mul_re]

omit [DecidableEq mode] [Fintype bond] in
theorem complexSpectralKernel_im
    (u : mode → bond → Real) (w : mode → Complex) (j l : bond) :
    (complexSpectralKernel u w j l).im =
      spectralKernel u (fun k ↦ (w k).im) j l := by
  simp [complexSpectralKernel, spectralKernel, Complex.mul_im]

theorem frobeniusSq_eq_realFrobeniusSq_re_add_im
    (K : bond → bond → Complex) :
    frobeniusSq K =
      realFrobeniusSq (fun j l ↦ (K j l).re) +
        realFrobeniusSq (fun j l ↦ (K j l).im) := by
  unfold frobeniusSq realFrobeniusSq
  simp_rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [pow_two]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [← Finset.sum_add_distrib]

theorem complexSpectralKernel_frobeniusSq_eq
    (u : mode → bond → Real) (w : mode → Complex)
    (horth : ∀ k q, ∑ j, u k j * u q j = if k = q then 1 else 0) :
    frobeniusSq (complexSpectralKernel u w) = ∑ k, ‖w k‖ ^ 2 := by
  rw [frobeniusSq_eq_realFrobeniusSq_re_add_im]
  simp_rw [complexSpectralKernel_re, complexSpectralKernel_im]
  rw [spectralKernel_frobeniusSq_eq u (fun k ↦ (w k).re) horth,
    spectralKernel_frobeniusSq_eq u (fun k ↦ (w k).im) horth,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring


omit [DecidableEq mode] [Fintype bond] in
theorem complexSpectralKernel_sub_entry_norm_le
    (u : mode → bond → Real) (w w' : mode → Complex)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (hrow : ∀ j, rowEnergy u j ≤ 1)
    (hweight : ∀ k, ‖w k - w' k‖ ≤ epsilon)
    (j l : bond) :
    ‖complexSpectralKernel u w j l - complexSpectralKernel u w' j l‖ ≤
      epsilon := by
  have hrow_nonneg (a : bond) : 0 ≤ rowEnergy u a :=
    Finset.sum_nonneg fun k _hk ↦ sq_nonneg _
  calc
    ‖complexSpectralKernel u w j l - complexSpectralKernel u w' j l‖ =
        ‖∑ k, (w k - w' k) * (u k j : Complex) * (u k l : Complex)‖ := by
      unfold complexSpectralKernel
      rw [← Finset.sum_sub_distrib]
      apply congrArg norm
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    _ ≤ ∑ k, ‖(w k - w' k) * (u k j : Complex) * (u k l : Complex)‖ :=
      norm_sum_le _ _
    _ = ∑ k, ‖w k - w' k‖ * |u k j| * |u k l| := by
      apply Finset.sum_congr rfl
      intro k _hk
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ epsilon * ∑ k, |u k j| * |u k l| := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k _hk
      simpa [mul_assoc] using
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hweight k) (abs_nonneg (u k j)))
          (abs_nonneg (u k l)))
    _ ≤ epsilon *
        (Real.sqrt (rowEnergy u j) * Real.sqrt (rowEnergy u l)) := by
      gcongr
      simpa [rowEnergy, sq_abs] using
        (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
          (fun k ↦ |u k j|) (fun k ↦ |u k l|))
    _ ≤ epsilon * (1 * 1) := by
      gcongr
      · simpa using Real.sqrt_le_one.mpr (hrow j)
      · simpa using Real.sqrt_le_one.mpr (hrow l)
    _ = epsilon := by ring

theorem sqrt_frobeniusSq_complexSpectralKernel_le
    (u : mode → bond → Real) (w : mode → Complex)
    (horth : ∀ k q, ∑ j, u k j * u q j = if k = q then 1 else 0)
    (bound : Real) (hbound : 0 ≤ bound)
    (hweight : ∀ k, ‖w k‖ ≤ bound) :
    Real.sqrt (frobeniusSq (complexSpectralKernel u w)) ≤
      Real.sqrt (Fintype.card mode : Real) * bound := by
  have hsum : (∑ k, ‖w k‖ ^ 2) ≤
      (Fintype.card mode : Real) * bound ^ 2 := by
    calc
      (∑ k, ‖w k‖ ^ 2) ≤ ∑ _k : mode, bound ^ 2 := by
        apply Finset.sum_le_sum
        intro k _hk
        nlinarith [norm_nonneg (w k), hweight k]
      _ = (Fintype.card mode : Real) * bound ^ 2 := by simp
  rw [complexSpectralKernel_frobeniusSq_eq u w horth]
  calc
    Real.sqrt (∑ k, ‖w k‖ ^ 2) ≤
        Real.sqrt ((Fintype.card mode : Real) * bound ^ 2) :=
      Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (Fintype.card mode : Real) * bound := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hbound]

variable {iota : Type*} [Fintype iota] [DecidableEq iota]

omit [Fintype bond] in
theorem complexWeightedProjectedBondKernel_eq_complexSpectralKernel_effective
    (B : Matrix bond iota Real) (A : HermitianMatrix iota)
    (u : Fin (Fintype.card iota) → bond → Real)
    (hfactor : ∀ k j l, projectedBondKernel B A k j l =
      orderedEigenvalue A k * u k j * u k l)
    (weight : Fin (Fintype.card iota) → Complex) :
    complexWeightedProjectedBondKernel B A weight =
      complexSpectralKernel u
        (fun k ↦ (orderedEigenvalue A k : Complex) * weight k) := by
  ext j l
  unfold complexWeightedProjectedBondKernel complexSpectralKernel
  apply Finset.sum_congr rfl
  intro k _hk
  rw [hfactor]
  push_cast
  ring

omit [Fintype bond] in
theorem complexWeightedProjectedBondKernel_sub_entry_norm_le_of_effectiveWeight
    (B : Matrix bond iota Real) (A : HermitianMatrix iota)
    (u : Fin (Fintype.card iota) → bond → Real)
    (hfactor : ∀ k j l, projectedBondKernel B A k j l =
      orderedEigenvalue A k * u k j * u k l)
    (hrow : ∀ j, rowEnergy u j ≤ 1)
    (weight weight' : Fin (Fintype.card iota) → Complex)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (hweight : ∀ k,
      ‖(orderedEigenvalue A k : Complex) * weight k -
        (orderedEigenvalue A k : Complex) * weight' k‖ ≤ epsilon)
    (j l : bond) :
    ‖complexWeightedProjectedBondKernel B A weight j l -
      complexWeightedProjectedBondKernel B A weight' j l‖ ≤ epsilon := by
  rw [complexWeightedProjectedBondKernel_eq_complexSpectralKernel_effective
      B A u hfactor weight,
    complexWeightedProjectedBondKernel_eq_complexSpectralKernel_effective
      B A u hfactor weight']
  exact complexSpectralKernel_sub_entry_norm_le u _ _ epsilon hepsilon
    hrow hweight j l

omit [Fintype bond] in
theorem complexWeightedProjectedBondKernel_entry_norm_le_of_effectiveWeight
    (B : Matrix bond iota Real) (A : HermitianMatrix iota)
    (u : Fin (Fintype.card iota) → bond → Real)
    (hfactor : ∀ k j l, projectedBondKernel B A k j l =
      orderedEigenvalue A k * u k j * u k l)
    (hrow : ∀ j, rowEnergy u j ≤ 1)
    (weight : Fin (Fintype.card iota) → Complex)
    (bound : Real) (hbound : 0 ≤ bound)
    (hweight : ∀ k,
      ‖(orderedEigenvalue A k : Complex) * weight k‖ ≤ bound)
    (j l : bond) :
    ‖complexWeightedProjectedBondKernel B A weight j l‖ ≤ bound := by
  simpa [complexWeightedProjectedBondKernel] using
    (complexWeightedProjectedBondKernel_sub_entry_norm_le_of_effectiveWeight
      B A u hfactor hrow weight (fun _k ↦ 0) bound hbound
      (by simpa using hweight) j l)

theorem complexWeightedProjectedBondKernel_sqrt_frobeniusSq_le_of_effectiveWeight
    (B : Matrix bond iota Real) (A : HermitianMatrix iota)
    (u : Fin (Fintype.card iota) → bond → Real)
    (hfactor : ∀ k j l, projectedBondKernel B A k j l =
      orderedEigenvalue A k * u k j * u k l)
    (horth : ∀ k q, ∑ j, u k j * u q j = if k = q then 1 else 0)
    (weight : Fin (Fintype.card iota) → Complex)
    (bound : Real) (hbound : 0 ≤ bound)
    (hweight : ∀ k,
      ‖(orderedEigenvalue A k : Complex) * weight k‖ ≤ bound) :
    Real.sqrt (frobeniusSq (complexWeightedProjectedBondKernel B A weight)) ≤
      Real.sqrt (Fintype.card iota : Real) * bound := by
  rw [complexWeightedProjectedBondKernel_eq_complexSpectralKernel_effective
    B A u hfactor weight]
  simpa using
    (sqrt_frobeniusSq_complexSpectralKernel_le u _ horth bound hbound hweight)

end
end ArchonPhysics.ComplexThreeLegKernelApproximation
