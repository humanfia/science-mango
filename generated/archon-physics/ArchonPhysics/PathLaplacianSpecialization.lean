import ArchonPhysics.GenericSpectrumResultant

/-!
# The broken-cycle path specialization

The specialization sets the weight at site `0` to zero and every other
weight to one.  The resulting weighted cycle matrix is the ordinary path
Laplacian in cyclic coordinates with the edge between the last and first
coordinates removed.
-/

namespace ArchonPhysics.PathLaplacianSpecialization

open ArchonPhysics.HarmonicModes
open ArchonPhysics.GenericSpectrumResultant

noncomputable section

/-- One broken weight and unit weights elsewhere. -/
def pathWeight {N : Nat} : Lattice.Site N → Real :=
  fun i ↦ if i = 0 then 0 else 1

/-- Coordinate vector for the broken-cycle specialization. -/
def pathWeightCoordinates (N : Nat) [NeZero N] : Fin N → Real :=
  fun k ↦ pathWeight ((siteEquivFin N).symm k)

theorem weightsOfCoordinates_pathWeightCoordinates
    (N : Nat) [NeZero N] :
    weightsOfCoordinates (pathWeightCoordinates N) = pathWeight := by
  ext i
  simp [weightsOfCoordinates, pathWeightCoordinates]

theorem transpose_differenceMatrix_mulVec {N : Nat} [NeZero N]
    (q : Lattice.Configuration N) :
    Matrix.mulVec (Matrix.transpose differenceMatrix) q =
      fun i ↦ q (i - 1) - q i := by
  ext i
  simp only [Matrix.mulVec, dotProduct, differenceMatrix, Matrix.transpose_apply,
    sub_mul]
  rw [Finset.sum_sub_distrib]
  have hshift (j : Lattice.Site N) : i = j + 1 ↔ j = i - 1 := by
    constructor
    · intro h
      rw [h]
      simp
    · intro h
      rw [h]
      simp
  simp_rw [hshift]
  simp

/-- Pointwise action of a weighted cycle Laplacian. -/
theorem weightedCycleLaplacian_mulVec {N : Nat} [NeZero N]
    (w q : Lattice.Configuration N) :
    Matrix.mulVec (weightedCycleLaplacian w) q =
      fun i ↦
        w (i + 1) * (q i - q (i + 1)) +
          w i * (q i - q (i - 1)) := by
  rw [weightedCycleLaplacian, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, transpose_differenceMatrix_mulVec]
  have hdiag :
      Matrix.mulVec (Matrix.diagonal w) (fun i ↦ q (i - 1) - q i) =
        fun i ↦ w i * (q (i - 1) - q i) := by
    ext i
    simp [Matrix.mulVec_diagonal]
  rw [hdiag, differenceMatrix_mulVec]
  ext i
  simp only [Lattice.forwardDifference]
  ring_nf

end

end ArchonPhysics.PathLaplacianSpecialization
