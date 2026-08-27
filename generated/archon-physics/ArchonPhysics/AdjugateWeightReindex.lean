import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Reindex invariance of adjugate quadratic weights

The actual weighted-cycle matrix is successively reindexed from cyclic sites
to finite coordinates and then to a left/right sum.  This file proves once and
for all that the denominator-free adjugate quadratic forms, and hence their
three-by-three determinant, are unchanged when matrices and directions are
transported along the same equivalence.
-/

open scoped BigOperators Matrix

namespace ArchonPhysics.AdjugateWeightReindex

variable {ι κ R : Type*}
variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable [CommRing R]

/-- Transport a coordinate vector along an index equivalence. -/
def reindexVector (e : ι ≃ κ) (v : ι → R) : κ → R :=
  v ∘ e.symm

omit [DecidableEq ι] [DecidableEq κ] in
/-- Matrix-vector multiplication commutes with simultaneous reindexing. -/
theorem reindex_mulVec (e : ι ≃ κ) (A : Matrix ι ι R) (v : ι → R) :
    Matrix.reindex e e A *ᵥ reindexVector e v =
      reindexVector e (A *ᵥ v) := by
  funext x
  change (∑ y : κ, A (e.symm x) (e.symm y) * v (e.symm y)) =
    ∑ y : ι, A (e.symm x) y * v y
  exact e.symm.sum_comp (fun y => A (e.symm x) y * v y)

omit [DecidableEq ι] [DecidableEq κ] in
/-- Dot products are unchanged by transport along an equivalence. -/
theorem dotProduct_reindexVector (e : ι ≃ κ) (v w : ι → R) :
    reindexVector e v ⬝ᵥ reindexVector e w = v ⬝ᵥ w := by
  change (∑ i : κ, v (e.symm i) * w (e.symm i)) =
    ∑ i : ι, v i * w i
  exact e.symm.sum_comp (fun i => v i * w i)

/-- A quadratic adjugate weight is invariant under simultaneous reindexing of
the matrix and its direction. -/
theorem reindexVector_dotProduct_adjugate_reindex_mulVec
    (e : ι ≃ κ) (A : Matrix ι ι R) (v : ι → R) :
    reindexVector e v ⬝ᵥ
        ((Matrix.reindex e e A).adjugate *ᵥ reindexVector e v) =
      v ⬝ᵥ (A.adjugate *ᵥ v) := by
  rw [Matrix.adjugate_reindex, reindex_mulVec,
    dotProduct_reindexVector]

/-- The determinant of three adjugate weights is invariant under the same
reindexing. -/
theorem det_adjugateWeightMatrix_reindex
    (e : ι ≃ κ) (A : Fin 3 → Matrix ι ι R)
    (directions : Fin 3 → ι → R) :
    Matrix.det (fun r s => reindexVector e (directions s) ⬝ᵥ
      ((Matrix.reindex e e (A r)).adjugate *ᵥ
        reindexVector e (directions s))) =
      Matrix.det (fun r s => directions s ⬝ᵥ
        ((A r).adjugate *ᵥ directions s)) := by
  congr 1
  ext r s
  exact reindexVector_dotProduct_adjugate_reindex_mulVec
    e (A r) (directions s)

end ArchonPhysics.AdjugateWeightReindex
