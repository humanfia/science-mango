import ArchonPhysics.ActualThreeMassProjectorWeightJacobian

/-!
# Denominator-free Lagrange numerators for ordered spectral projectors

At simple spectrum, multiplying an ordered Lagrange projector by the exact
product of its spectral gaps removes every inverse denominator.  Applied row
by row, this clears the three projector-minor denominators without changing
its zero locus.  The resulting matrix is still algebraic through the ordered
eigenvalues; identifying it with an adjugate evaluation is the next bridge to
a polynomial/resultant certificate.
-/

open scoped Matrix BigOperators

namespace ArchonPhysics.OrderedProjectorLagrangeNumerator

open ArchonPhysics
open ArchonPhysics.ActualThreeMassProjectorWeightJacobian
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.ThreeParameterProjectorWeightJacobian

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- One denominator-free factor in the Lagrange numerator. -/
def orderedModeNumeratorFactor (A : HermitianMatrix ι)
    (j : Fin (Fintype.card ι)) : Matrix ι ι Real :=
  matrixVal A - orderedEigenvalue A j • (1 : Matrix ι ι Real)

/-- Exact product of the nonselected ordered spectral gaps. -/
def orderedModeGapProduct (A : HermitianMatrix ι)
    (k : Fin (Fintype.card ι)) : Real :=
  ∏ j ∈ Finset.univ.erase k,
    (orderedEigenvalue A k - orderedEigenvalue A j)

/-- Denominator-free numerator of the ordered Lagrange projector. -/
def orderedModeProjectorNumerator (A : HermitianMatrix ι)
    (k : Fin (Fintype.card ι)) : Matrix ι ι Real :=
  ((Finset.univ.erase k).toList.map
    (orderedModeNumeratorFactor A)).prod

theorem orderedModeNumeratorFactor_mulVec_eigenvectorBasis
    (A : HermitianMatrix ι)
    (j r : Fin (Fintype.card ι)) :
    orderedModeNumeratorFactor A j *ᵥ
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) =
      (orderedEigenvalue A r - orderedEigenvalue A j) •
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) := by
  have heigen : matrixVal A *ᵥ
      ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) =
        orderedEigenvalue A r •
          ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) := by
    have hval : matrixVal A = (fun i j => A.1 i j) := rfl
    rw [hval]
    simpa [orderedEigenvalue_equiv] using
      A.2.mulVec_eigenvectorBasis (orderedIndexEquiv r)
  rw [orderedModeNumeratorFactor, Matrix.sub_mulVec, heigen,
    Matrix.smul_mulVec, Matrix.one_mulVec]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem listProduct_orderedModeNumeratorFactor_mulVec_eigenvectorBasis
    (A : HermitianMatrix ι) (r : Fin (Fintype.card ι)) :
    ∀ L : List (Fin (Fintype.card ι)),
      (L.map (orderedModeNumeratorFactor A)).prod *ᵥ
          ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) =
        (L.map (fun j =>
          orderedEigenvalue A r - orderedEigenvalue A j)).prod •
            ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r))
  | [] => by simp
  | j :: L => by
      rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec,
        listProduct_orderedModeNumeratorFactor_mulVec_eigenvectorBasis A r L,
        Matrix.mulVec_smul,
        orderedModeNumeratorFactor_mulVec_eigenvectorBasis,
        List.map_cons, List.prod_cons, smul_smul]
      simp only [mul_comm]

theorem orderedModeProjectorNumerator_mulVec_eigenvectorBasis
    (A : HermitianMatrix ι)
    (k r : Fin (Fintype.card ι)) :
    orderedModeProjectorNumerator A k *ᵥ
        ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r)) =
      if r = k then
        orderedModeGapProduct A k •
          ⇑(A.2.eigenvectorBasis (orderedIndexEquiv r))
      else 0 := by
  rw [orderedModeProjectorNumerator,
    listProduct_orderedModeNumeratorFactor_mulVec_eigenvectorBasis]
  split_ifs with hrk
  · subst r
    congr 1
    simp [orderedModeGapProduct]
  · have hrmem : r ∈ (Finset.univ.erase k).toList := by
      simp [hrk]
    have hzero : orderedEigenvalue A r - orderedEigenvalue A r = 0 := sub_self _
    have hzmem : (0 : Real) ∈
        ((Finset.univ.erase k).toList.map
          (fun j => orderedEigenvalue A r - orderedEigenvalue A j)) :=
      List.mem_map.mpr ⟨r, hrmem, hzero⟩
    rw [List.prod_eq_zero hzmem, zero_smul]

/-- The gap product times the totalized projector is exactly the
denominator-free numerator at every simple spectrum. -/
theorem orderedModeGapProduct_smul_projector_eq_numerator
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (k : Fin (Fintype.card ι)) :
    orderedModeGapProduct A k • orderedModeProjector A k =
      orderedModeProjectorNumerator A k := by
  apply matrix_eq_of_mulVec_eigenvectorBasis_eq A
  intro r
  rw [Matrix.smul_mulVec,
    orderedModeProjector_mulVec_eigenvectorBasis A hsimple,
    orderedModeProjectorNumerator_mulVec_eigenvectorBasis]
  by_cases hrk : r = k
  · simp [hrk]
  · simp [hrk]

theorem orderedModeGapProduct_ne_zero
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (k : Fin (Fintype.card ι)) :
    orderedModeGapProduct A k ≠ 0 := by
  unfold orderedModeGapProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hjk : j ≠ k := by simpa using hj
  exact sub_ne_zero.mpr (hsimple.ne hjk.symm)

/-- Quadratic weights of the denominator-free projector numerators. -/
def orderedProjectorNumeratorWeightMatrix
    (A : HermitianMatrix ι)
    (modes : Fin 3 → Fin (Fintype.card ι))
    (directions : Fin 3 → ι → Real) :
    Matrix (Fin 3) (Fin 3) Real :=
  fun r s => directions s ⬝ᵥ
    (orderedModeProjectorNumerator A (modes r) *ᵥ directions s)

/-- Clearing the row denominators factors the numerator minor exactly. -/
theorem orderedProjectorNumeratorWeightMatrix_det
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (modes : Fin 3 → Fin (Fintype.card ι))
    (directions : Fin 3 → ι → Real) :
    (orderedProjectorNumeratorWeightMatrix A modes directions).det =
      (∏ r, orderedModeGapProduct A (modes r)) *
        (orderedProjectorWeightMatrix A modes directions).det := by
  have hmatrix : orderedProjectorNumeratorWeightMatrix A modes directions =
      rowColumnScaledMatrix
        (fun r => orderedModeGapProduct A (modes r))
        (fun _s => 1)
        (orderedProjectorWeightMatrix A modes directions) := by
    ext r s
    rw [orderedProjectorNumeratorWeightMatrix,
      rowColumnScaledMatrix, orderedProjectorWeightMatrix,
      ← orderedModeGapProduct_smul_projector_eq_numerator A hsimple,
      Matrix.smul_mulVec, dotProduct_smul]
    simp
  rw [hmatrix, det_rowColumnScaledMatrix]
  simp

/-- On simple spectrum, the denominator-free numerator minor has precisely
the same zero locus as the genuine ordered projector-weight minor. -/
theorem orderedProjectorNumeratorWeightMatrix_det_eq_zero_iff
    (A : HermitianMatrix ι) (hsimple : SimpleOrderedSpectrum A)
    (modes : Fin 3 → Fin (Fintype.card ι))
    (directions : Fin 3 → ι → Real) :
    (orderedProjectorNumeratorWeightMatrix A modes directions).det = 0 ↔
      (orderedProjectorWeightMatrix A modes directions).det = 0 := by
  rw [orderedProjectorNumeratorWeightMatrix_det A hsimple]
  have hgap : (∏ r, orderedModeGapProduct A (modes r)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun r _hr =>
      orderedModeGapProduct_ne_zero A hsimple (modes r)
  simp [hgap]

/-- Actual random-mass specialization of denominator clearing.  It is valid
for every finite volume and does not impose a false pointwise nondegeneracy
claim. -/
theorem actualThreeMassProjectorMinor_eq_zero_iff_numerator
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (triple : ThreeParameterSpectralAveragingDensity.MassTriple)
    (hsimple : SimpleOrderedSpectrum
      (actualThreeMassDualHermitian fixed site₀ site₁ site₂ triple)) :
    (actualThreeMassProjectorWeightMatrix
        fixed site₀ site₁ site₂ modes triple).det = 0 ↔
      (orderedProjectorNumeratorWeightMatrix
        (actualThreeMassDualHermitian fixed site₀ site₁ site₂ triple)
        modes (actualThreeMassCycleDirection site₀ site₁ site₂)).det = 0 := by
  symm
  exact orderedProjectorNumeratorWeightMatrix_det_eq_zero_iff
    (actualThreeMassDualHermitian fixed site₀ site₁ site₂ triple)
    hsimple modes (actualThreeMassCycleDirection site₀ site₁ site₂)

end

end ArchonPhysics.OrderedProjectorLagrangeNumerator
