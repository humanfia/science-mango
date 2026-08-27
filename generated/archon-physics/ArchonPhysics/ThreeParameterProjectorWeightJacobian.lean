import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Matrix.ToLin
import ArchonPhysics.OrderedEigenvalueHellmannFeynman
import ArchonPhysics.ThreeFrequencyLiftedJacobianFactorization

/-!
# Three-parameter projector-weight Jacobian

This module fixes the canonical three coordinates on `MassTriple` and proves
that the intrinsic determinant of a continuous linear map assembled from
three row functionals is exactly the determinant of its `Fin 3` coordinate
matrix.  It then factors row and column scalings from the genuine ordered
spectral-projector weight matrix.

For a random-mass dual cycle, Hellmann--Feynman supplies the row scale
`1 / (2 * omega_r)`, the column scale `-m_s⁻²`, and the unscaled entry
`v_s dot P_r v_s`.  The remaining nondegeneracy question is therefore the
explicit determinant of this actual mode-by-site weight matrix.
-/

open scoped Matrix

namespace ArchonPhysics.ThreeParameterProjectorWeightJacobian

open ArchonPhysics
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.ThreeFrequencyLiftedJacobianFactorization
open ArchonPhysics.ThreeParameterSpectralAveragingDensity

noncomputable section

/-- The canonical ordered basis `((1,0),0), ((0,1),0), ((0,0),1)` of
`MassTriple = (Real × Real) × Real`. -/
def massTripleBasis : Module.Basis (Fin 3) Real MassTriple :=
  ((Module.Basis.finTwoProd Real).prod
    (Module.Basis.singleton (Fin 1) Real)).reindex finSumFinEquiv

@[simp] theorem massTripleBasis_zero :
    massTripleBasis 0 = ((1, 0), 0) := by
  change massTripleBasis ((0 : Fin 2).castAdd 1) = _
  rw [massTripleBasis, Module.Basis.reindex_apply,
    finSumFinEquiv_symm_apply_castAdd, Module.Basis.prod_apply]
  simp

@[simp] theorem massTripleBasis_one :
    massTripleBasis 1 = ((0, 1), 0) := by
  change massTripleBasis ((1 : Fin 2).castAdd 1) = _
  rw [massTripleBasis, Module.Basis.reindex_apply,
    finSumFinEquiv_symm_apply_castAdd, Module.Basis.prod_apply]
  simp

@[simp] theorem massTripleBasis_two :
    massTripleBasis 2 = ((0, 0), 1) := by
  change massTripleBasis ((0 : Fin 1).natAdd 2) = _
  rw [massTripleBasis, Module.Basis.reindex_apply,
    finSumFinEquiv_symm_apply_natAdd, Module.Basis.prod_apply]
  ext <;> simp

@[simp] theorem massTripleBasis_repr_zero (x : MassTriple) :
    massTripleBasis.repr x 0 = x.1.1 := by
  change massTripleBasis.repr x ((0 : Fin 2).castAdd 1) = _
  rw [massTripleBasis, Module.Basis.repr_reindex_apply,
    finSumFinEquiv_symm_apply_castAdd, Module.Basis.prod_repr_inl]
  rfl

@[simp] theorem massTripleBasis_repr_one (x : MassTriple) :
    massTripleBasis.repr x 1 = x.1.2 := by
  change massTripleBasis.repr x ((1 : Fin 2).castAdd 1) = _
  rw [massTripleBasis, Module.Basis.repr_reindex_apply,
    finSumFinEquiv_symm_apply_castAdd, Module.Basis.prod_repr_inl]
  rfl

@[simp] theorem massTripleBasis_repr_two (x : MassTriple) :
    massTripleBasis.repr x 2 = x.2 := by
  change massTripleBasis.repr x ((0 : Fin 1).natAdd 2) = _
  rw [massTripleBasis, Module.Basis.repr_reindex_apply,
    finSumFinEquiv_symm_apply_natAdd, Module.Basis.prod_repr_inr]
  simp

def massTripleCoordinateZero : MassTriple →L[Real] Real :=
  (ContinuousLinearMap.fst Real Real Real) ∘L
    (ContinuousLinearMap.fst Real (Real × Real) Real)

def massTripleCoordinateOne : MassTriple →L[Real] Real :=
  (ContinuousLinearMap.snd Real Real Real) ∘L
    (ContinuousLinearMap.fst Real (Real × Real) Real)

def massTripleCoordinateTwo : MassTriple →L[Real] Real :=
  ContinuousLinearMap.snd Real (Real × Real) Real

/-- The continuous linear functional with coefficients `a 0, a 1, a 2`
in the canonical mass-triple coordinates. -/
def massTripleLinearFunctional (a : Fin 3 → Real) :
    MassTriple →L[Real] Real :=
  a 0 • massTripleCoordinateZero + a 1 • massTripleCoordinateOne +
    a 2 • massTripleCoordinateTwo

/-- Repackage a `3 × 3` real matrix as an endomorphism of `MassTriple`,
with matrix rows in the canonical nested-product coordinates. -/
def massTripleLinearMapOfMatrix
    (M : Matrix (Fin 3) (Fin 3) Real) : MassTriple →L[Real] MassTriple :=
  ((massTripleLinearFunctional (M 0)).prod
    (massTripleLinearFunctional (M 1))).prod
      (massTripleLinearFunctional (M 2))

@[simp] theorem massTripleLinearFunctional_apply
    (a : Fin 3 → Real) (x : MassTriple) :
    massTripleLinearFunctional a x =
      a 0 * x.1.1 + a 1 * x.1.2 + a 2 * x.2 := by
  simp [massTripleLinearFunctional, massTripleCoordinateZero,
    massTripleCoordinateOne, massTripleCoordinateTwo]

@[simp] theorem massTripleLinearMapOfMatrix_apply
    (M : Matrix (Fin 3) (Fin 3) Real) (x : MassTriple) :
    massTripleLinearMapOfMatrix M x =
      ((M 0 0 * x.1.1 + M 0 1 * x.1.2 + M 0 2 * x.2,
        M 1 0 * x.1.1 + M 1 1 * x.1.2 + M 1 2 * x.2),
        M 2 0 * x.1.1 + M 2 1 * x.1.2 + M 2 2 * x.2) := by
  simp [massTripleLinearMapOfMatrix]

theorem toMatrix_massTripleLinearMapOfMatrix
    (M : Matrix (Fin 3) (Fin 3) Real) :
    (LinearMap.toMatrix massTripleBasis massTripleBasis)
      (massTripleLinearMapOfMatrix M).toLinearMap = M := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  fin_cases i <;> fin_cases j <;> simp

/-- Intrinsic continuous-linear determinant agrees exactly with the ordinary
`Fin 3` determinant in the canonical mass coordinates. -/
theorem det_massTripleLinearMapOfMatrix
    (M : Matrix (Fin 3) (Fin 3) Real) :
    (massTripleLinearMapOfMatrix M).det = M.det := by
  rw [ContinuousLinearMap.det]
  rw [← LinearMap.det_toMatrix massTripleBasis
    (massTripleLinearMapOfMatrix M).toLinearMap]
  rw [toMatrix_massTripleLinearMapOfMatrix]

theorem frequencyTripleDerivative_eq_massTripleLinearMapOfMatrix
    (derivative : Fin 3 → MassTriple →L[Real] Real)
    (M : Matrix (Fin 3) (Fin 3) Real)
    (hrow : ∀ r x,
      derivative r x = massTripleLinearFunctional (M r) x) :
    frequencyTripleDerivative derivative = massTripleLinearMapOfMatrix M := by
  apply ContinuousLinearMap.ext
  intro x
  change ((derivative 0 x, derivative 1 x), derivative 2 x) =
    ((massTripleLinearFunctional (M 0) x,
      massTripleLinearFunctional (M 1) x),
      massTripleLinearFunctional (M 2) x)
  apply Prod.ext
  · exact Prod.ext (hrow 0 x) (hrow 1 x)
  · exact hrow 2 x

theorem frequencyTripleDerivative_det_eq_matrix_det
    (derivative : Fin 3 → MassTriple →L[Real] Real)
    (M : Matrix (Fin 3) (Fin 3) Real)
    (hrow : ∀ r x,
      derivative r x = massTripleLinearFunctional (M r) x) :
    (frequencyTripleDerivative derivative).det = M.det := by
  rw [frequencyTripleDerivative_eq_massTripleLinearMapOfMatrix
    derivative M hrow, det_massTripleLinearMapOfMatrix]

/-- Scale the rows and columns of a three-by-three matrix independently. -/
def rowColumnScaledMatrix (row column : Fin 3 → Real)
    (M : Matrix (Fin 3) (Fin 3) Real) :
    Matrix (Fin 3) (Fin 3) Real :=
  fun r s => row r * M r s * column s

theorem rowColumnScaledMatrix_eq
    (row column : Fin 3 → Real)
    (M : Matrix (Fin 3) (Fin 3) Real) :
    rowColumnScaledMatrix row column M =
      Matrix.diagonal row * M * Matrix.diagonal column := by
  ext r s
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

/-- Exact determinant factorization into row scales, the unscaled minor, and
column scales. -/
theorem det_rowColumnScaledMatrix
    (row column : Fin 3 → Real)
    (M : Matrix (Fin 3) (Fin 3) Real) :
    (rowColumnScaledMatrix row column M).det =
      (∏ r, row r) * M.det * (∏ s, column s) := by
  rw [rowColumnScaledMatrix_eq, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, Matrix.det_diagonal]

theorem det_rowColumnScaledMatrix_ne_zero_iff
    (row column : Fin 3 → Real)
    (M : Matrix (Fin 3) (Fin 3) Real)
    (hrow : ∀ r, row r ≠ 0)
    (hcolumn : ∀ s, column s ≠ 0) :
    (rowColumnScaledMatrix row column M).det ≠ 0 ↔ M.det ≠ 0 := by
  rw [det_rowColumnScaledMatrix]
  have hrowProd : (∏ r, row r) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun r _hr => hrow r)
  have hcolumnProd : (∏ s, column s) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun s _hs => hcolumn s)
  simp [hrowProd, hcolumnProd]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual basis-free mode-by-direction matrix.  Its `(r,s)` entry is
the quadratic weight of direction `s` in ordered spectral mode `r`. -/
def orderedProjectorWeightMatrix
    (A : HermitianMatrix ι)
    (modes : Fin 3 → Fin (Fintype.card ι))
    (directions : Fin 3 → ι → Real) :
    Matrix (Fin 3) (Fin 3) Real :=
  fun r s => directions s ⬝ᵥ
    (orderedModeProjector A (modes r) *ᵥ directions s)

/-- The matrix obtained after multiplying the projector weights by the
frequency row scales and physical-coordinate column scales. -/
def scaledOrderedProjectorWeightMatrix
    (A : HermitianMatrix ι)
    (modes : Fin 3 → Fin (Fintype.card ι))
    (directions : Fin 3 → ι → Real)
    (row column : Fin 3 → Real) :
    Matrix (Fin 3) (Fin 3) Real :=
  rowColumnScaledMatrix row column
    (orderedProjectorWeightMatrix A modes directions)

theorem det_scaledOrderedProjectorWeightMatrix
    (A : HermitianMatrix ι)
    (modes : Fin 3 → Fin (Fintype.card ι))
    (directions : Fin 3 → ι → Real)
    (row column : Fin 3 → Real) :
    (scaledOrderedProjectorWeightMatrix
      A modes directions row column).det =
      (∏ r, row r) *
        (orderedProjectorWeightMatrix A modes directions).det *
          (∏ s, column s) := by
  exact det_rowColumnScaledMatrix row column _

/-- Once all physical and frequency scales are nonzero, the three-frequency
Jacobian is nondegenerate exactly when the genuine projector-weight minor is
nonzero. -/
theorem det_scaledOrderedProjectorWeightMatrix_ne_zero_iff
    (A : HermitianMatrix ι)
    (modes : Fin 3 → Fin (Fintype.card ι))
    (directions : Fin 3 → ι → Real)
    (row column : Fin 3 → Real)
    (hrow : ∀ r, row r ≠ 0)
    (hcolumn : ∀ s, column s ≠ 0) :
    (scaledOrderedProjectorWeightMatrix
      A modes directions row column).det ≠ 0 ↔
      (orderedProjectorWeightMatrix A modes directions).det ≠ 0 := by
  exact det_rowColumnScaledMatrix_ne_zero_iff row column _ hrow hcolumn

end

end ArchonPhysics.ThreeParameterProjectorWeightJacobian
