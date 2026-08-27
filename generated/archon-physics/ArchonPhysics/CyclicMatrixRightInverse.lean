import Mathlib.Data.Matrix.Mul

/-!
# Right inverses from a cyclic column

For a matrix commuting with a cyclic family of coordinate operators, it is
enough to certify one inverse column.  The remaining columns are obtained by
applying the coordinate operators to that one vector.  This avoids expanding
a large matrix-by-matrix product in native certificates.
-/

open scoped Matrix BigOperators

namespace ArchonPhysics.CyclicMatrixRightInverse

/-- The candidate right inverse obtained by transporting one inverse column
through a family of coordinate operators. -/
def cyclicRightInverse
    {R ι : Type*} [CommSemiring R] [Fintype ι]
    (operator : ι → Matrix ι ι R) (inverseOrigin : ι → R) :
    Matrix ι ι R :=
  fun i a => (operator a *ᵥ inverseOrigin) i

/-- A checked inverse image of one cyclic basis vector produces an explicit
right inverse, provided the target matrix commutes with the operators that
generate all other basis vectors from it. -/
theorem rightInverse_of_cyclic_column
    {R ι : Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (operator : ι → Matrix ι ι R)
    (origin : ι) (inverseOrigin : ι → R)
    (hcommute : ∀ a, M * operator a = operator a * M)
    (hcyclic : ∀ a i, operator a i origin = (1 : Matrix ι ι R) i a)
    (hinverse : M *ᵥ inverseOrigin = fun i => (1 : Matrix ι ι R) i origin) :
    M * cyclicRightInverse operator inverseOrigin = 1 := by
  ext i a
  change (M *ᵥ (operator a *ᵥ inverseOrigin)) i =
    (1 : Matrix ι ι R) i a
  rw [Matrix.mulVec_mulVec, hcommute a, ← Matrix.mulVec_mulVec, hinverse]
  calc
    (operator a *ᵥ fun j => (1 : Matrix ι ι R) j origin) i =
        operator a i origin := by
      classical
      simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
    _ = (1 : Matrix ι ι R) i a := hcyclic a i

end ArchonPhysics.CyclicMatrixRightInverse
