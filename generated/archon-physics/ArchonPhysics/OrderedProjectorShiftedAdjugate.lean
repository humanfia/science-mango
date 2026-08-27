import ArchonPhysics.OrderedProjectorLagrangeNumerator

/-!
# Shifted adjugates for ordered projector numerators

This module identifies the denominator-free Lagrange numerator of a simple
ordered spectral projector with an adjugate of the shifted Hermitian matrix.
The adjugate has polynomial entries in the matrix coefficients and one
spectral parameter, which is the correct bridge toward elimination and
resultant certificates for the actual random-mass projector minor.
-/

open scoped Matrix BigOperators

namespace ArchonPhysics.OrderedProjectorShiftedAdjugate

open ArchonPhysics
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedProjectorLagrangeNumerator
open ArchonPhysics.OrderedSingleModeProjector

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Adjugation commutes with conjugation by a matrix with a supplied
two-sided inverse, including when the middle matrix is singular. -/
theorem adjugate_conj_of_twoSidedInverse
    (S R D : Matrix ι ι Real)
    (hSR : S * R = 1) (hRS : R * S = 1) :
    (S * D * R).adjugate = S * D.adjugate * R := by
  have hadjR : R.adjugate = R.det • S := by
    calc
      R.adjugate = 1 * R.adjugate := by simp
      _ = (S * R) * R.adjugate := by rw [hSR]
      _ = S * (R * R.adjugate) := by rw [Matrix.mul_assoc]
      _ = S * (R.det • (1 : Matrix ι ι Real)) := by
        rw [Matrix.mul_adjugate]
      _ = R.det • S := by simp
  have hadjS : S.adjugate = S.det • R := by
    calc
      S.adjugate = 1 * S.adjugate := by simp
      _ = (R * S) * S.adjugate := by rw [hRS]
      _ = R * (S * S.adjugate) := by rw [Matrix.mul_assoc]
      _ = R * (S.det • (1 : Matrix ι ι Real)) := by
        rw [Matrix.mul_adjugate]
      _ = S.det • R := by simp
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib,
    hadjR, hadjS]
  have hdet : R.det * S.det = 1 := by
    rw [← Matrix.det_mul, hRS, Matrix.det_one]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_comm S.det R.det, hdet, one_smul]
  simp [Matrix.mul_assoc]

/-- The real unitary whose columns are the Hermitian eigenvectors. -/
def orderedEigenvectorUnitaryMatrix (A : HermitianMatrix ι) :
    Matrix ι ι Real :=
  (A.2.eigenvectorUnitary : Matrix ι ι Real)

/-- The diagonal shift by one selected ordered eigenvalue. -/
def orderedEigenvalueShiftDiagonal (A : HermitianMatrix ι)
    (k : Fin (Fintype.card ι)) : Matrix ι ι Real :=
  Matrix.diagonal fun i =>
    orderedEigenvalue A k - A.2.eigenvalues i

/-- The characteristic matrix evaluated at one selected ordered eigenvalue. -/
def orderedEigenvalueShiftedMatrix (A : HermitianMatrix ι)
    (k : Fin (Fintype.card ι)) : Matrix ι ι Real :=
  orderedEigenvalue A k • (1 : Matrix ι ι Real) - matrixVal A

theorem orderedEigenvectorUnitaryMatrix_mul_star_eq_one
    (A : HermitianMatrix ι) :
    orderedEigenvectorUnitaryMatrix A *
        star (orderedEigenvectorUnitaryMatrix A) = 1 := by
  exact Unitary.coe_mul_star_self A.2.eigenvectorUnitary

theorem star_orderedEigenvectorUnitaryMatrix_mul_eq_one
    (A : HermitianMatrix ι) :
    star (orderedEigenvectorUnitaryMatrix A) *
        orderedEigenvectorUnitaryMatrix A = 1 := by
  exact Unitary.coe_star_mul_self A.2.eigenvectorUnitary

/-- Spectral conjugation of the selected characteristic matrix. -/
theorem orderedEigenvalueShiftedMatrix_eq_spectralConjugation
    (A : HermitianMatrix ι) (k : Fin (Fintype.card ι)) :
    orderedEigenvalueShiftedMatrix A k =
      orderedEigenvectorUnitaryMatrix A *
          orderedEigenvalueShiftDiagonal A k *
        star (orderedEigenvectorUnitaryMatrix A) := by
  let U := orderedEigenvectorUnitaryMatrix A
  let R := star U
  let D : Matrix ι ι Real := Matrix.diagonal A.2.eigenvalues
  have hUR : U * R = 1 := by
    simpa [U, R] using
      orderedEigenvectorUnitaryMatrix_mul_star_eq_one A
  have hA : matrixVal A = U * D * R := by
    have hval : matrixVal A = (fun i j => A.1 i j) := rfl
    rw [hval]
    simpa [U, R, D, orderedEigenvectorUnitaryMatrix,
      Unitary.conjStarAlgAut_apply, Function.comp_def] using
        A.2.spectral_theorem
  have hshift : orderedEigenvalueShiftDiagonal A k =
      orderedEigenvalue A k • (1 : Matrix ι ι Real) - D := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [orderedEigenvalueShiftDiagonal, D]
    · simp [orderedEigenvalueShiftDiagonal, D, hij]
  unfold orderedEigenvalueShiftedMatrix
  rw [hA, hshift, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUR]

/-- The shifted adjugate is the spectral conjugate of an explicit diagonal
adjugate. -/
theorem orderedEigenvalueShiftedMatrix_adjugate_eq_spectralConjugation
    (A : HermitianMatrix ι) (k : Fin (Fintype.card ι)) :
    (orderedEigenvalueShiftedMatrix A k).adjugate =
      orderedEigenvectorUnitaryMatrix A *
          (orderedEigenvalueShiftDiagonal A k).adjugate *
        star (orderedEigenvectorUnitaryMatrix A) := by
  rw [orderedEigenvalueShiftedMatrix_eq_spectralConjugation]
  exact adjugate_conj_of_twoSidedInverse _ _ _
    (orderedEigenvectorUnitaryMatrix_mul_star_eq_one A)
    (star_orderedEigenvectorUnitaryMatrix_mul_eq_one A)

/-- Product of all shifted eigenvalues except the indicated eigenbasis
coordinate. -/
def orderedShiftedAdjugateGap (A : HermitianMatrix ι)
    (k r : Fin (Fintype.card ι)) : Real :=
  ∏ j ∈ Finset.univ.erase (orderedIndexEquiv r),
    (orderedEigenvalue A k - A.2.eigenvalues j)

/-- Exact action of the shifted adjugate on every ordered eigenvector. -/
theorem orderedEigenvalueShiftedMatrix_adjugate_mulVec_eigenvectorBasis
    (A : HermitianMatrix ι)
    (k r : Fin (Fintype.card ι)) :
    (orderedEigenvalueShiftedMatrix A k).adjugate *ᵥ
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) =
      orderedShiftedAdjugateGap A k r •
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) := by
  rw [orderedEigenvalueShiftedMatrix_adjugate_eq_spectralConjugation,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [show star (orderedEigenvectorUnitaryMatrix A) *ᵥ
      ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) =
        Pi.single (orderedIndexEquiv r) 1 by
      exact A.2.star_eigenvectorUnitary_mulVec (orderedIndexEquiv r)]
  unfold orderedEigenvalueShiftDiagonal
  rw [Matrix.adjugate_diagonal, Matrix.diagonal_mulVec_single,
    ← smul_eq_mul, Pi.single_smul', Matrix.mulVec_smul]
  rw [show orderedEigenvectorUnitaryMatrix A *ᵥ
      Pi.single (orderedIndexEquiv r) 1 =
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) by
      exact A.2.eigenvectorUnitary_mulVec (orderedIndexEquiv r)]
  rfl

theorem orderedShiftedAdjugateGap_self_eq_gapProduct
    (A : HermitianMatrix ι) (k : Fin (Fintype.card ι)) :
    orderedShiftedAdjugateGap A k k = orderedModeGapProduct A k := by
  unfold orderedShiftedAdjugateGap orderedModeGapProduct
  symm
  apply Finset.prod_equiv orderedIndexEquiv
  · intro j
    simp
  · intro j _hj
    rw [orderedEigenvalue_equiv]

theorem orderedShiftedAdjugateGap_eq_zero_of_ne
    (A : HermitianMatrix ι)
    {k r : Fin (Fintype.card ι)} (hrk : r ≠ k) :
    orderedShiftedAdjugateGap A k r = 0 := by
  unfold orderedShiftedAdjugateGap
  apply Finset.prod_eq_zero
  · exact Finset.mem_erase.mpr
      ⟨orderedIndexEquiv.injective.ne hrk.symm, Finset.mem_univ _⟩
  · rw [orderedEigenvalue_equiv]
    exact sub_self _

/-- The shifted adjugate and the Lagrange numerator have identical action on
the complete ordered eigenbasis. -/
theorem orderedEigenvalueShiftedMatrix_adjugate_mulVec_eq_ite
    (A : HermitianMatrix ι)
    (k r : Fin (Fintype.card ι)) :
    (orderedEigenvalueShiftedMatrix A k).adjugate *ᵥ
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) =
      if r = k then
        orderedModeGapProduct A k •
          ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r))
      else 0 := by
  rw [orderedEigenvalueShiftedMatrix_adjugate_mulVec_eigenvectorBasis]
  split_ifs with hrk
  · subst r
    rw [orderedShiftedAdjugateGap_self_eq_gapProduct]
  · rw [orderedShiftedAdjugateGap_eq_zero_of_ne A hrk, zero_smul]

/-- The denominator-free ordered Lagrange numerator is exactly the adjugate
of the characteristic matrix at the selected eigenvalue. -/
theorem orderedModeProjectorNumerator_eq_shiftedAdjugate
    (A : HermitianMatrix ι) (k : Fin (Fintype.card ι)) :
    orderedModeProjectorNumerator A k =
      (orderedEigenvalueShiftedMatrix A k).adjugate := by
  apply matrix_eq_of_mulVec_eigenvectorBasis_eq A
  intro r
  rw [orderedModeProjectorNumerator_mulVec_eigenvectorBasis,
    orderedEigenvalueShiftedMatrix_adjugate_mulVec_eq_ite]

/-- Quadratic weights of the three shifted adjugates.  Every entry is now an
adjugate evaluation rather than a rational spectral projector. -/
def orderedShiftedAdjugateWeightMatrix
    (A : HermitianMatrix ι)
    (modes : Fin 3 → Fin (Fintype.card ι))
    (directions : Fin 3 → ι → Real) :
    Matrix (Fin 3) (Fin 3) Real :=
  fun r s => directions s ⬝ᵥ
    ((orderedEigenvalueShiftedMatrix A (modes r)).adjugate *ᵥ
      directions s)

theorem orderedProjectorNumeratorWeightMatrix_eq_shiftedAdjugateWeightMatrix
    (A : HermitianMatrix ι)
    (modes : Fin 3 → Fin (Fintype.card ι))
    (directions : Fin 3 → ι → Real) :
    orderedProjectorNumeratorWeightMatrix A modes directions =
      orderedShiftedAdjugateWeightMatrix A modes directions := by
  ext r s
  unfold orderedProjectorNumeratorWeightMatrix
    orderedShiftedAdjugateWeightMatrix
  rw [orderedModeProjectorNumerator_eq_shiftedAdjugate]

/-- Actual random-mass projector-minor degeneracy, on simple spectrum, is
exactly the zero set of three shifted-adjugate quadratic forms.  This is the
general-volume polynomial-in-matrix-entries representation used by the next
inverse-mass polynomial layer. -/
theorem actualThreeMassProjectorMinor_eq_zero_iff_shiftedAdjugate
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (triple : ThreeParameterSpectralAveragingDensity.MassTriple)
    (hsimple : SimpleOrderedSpectrum
      (ActualThreeMassProjectorWeightJacobian.actualThreeMassDualHermitian
        fixed site₀ site₁ site₂ triple)) :
    (ActualThreeMassProjectorWeightJacobian.actualThreeMassProjectorWeightMatrix
        fixed site₀ site₁ site₂ modes triple).det = 0 ↔
      (orderedShiftedAdjugateWeightMatrix
        (ActualThreeMassProjectorWeightJacobian.actualThreeMassDualHermitian
          fixed site₀ site₁ site₂ triple)
        modes
        (ActualThreeMassProjectorWeightJacobian.actualThreeMassCycleDirection
          site₀ site₁ site₂)).det = 0 := by
  rw [← orderedProjectorNumeratorWeightMatrix_eq_shiftedAdjugateWeightMatrix]
  exact actualThreeMassProjectorMinor_eq_zero_iff_numerator
    fixed site₀ site₁ site₂ modes triple hsimple

end


end ArchonPhysics.OrderedProjectorShiftedAdjugate
