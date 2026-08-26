import ArchonPhysics.GramMultiplicityTransfer

/-!
# From inverse masses to the polynomial weighted-cycle matrix

This file identifies the edge-space Gram matrix of the mass-weighted
difference operator with the weighted cycle Laplacian whose weights are the
inverse masses.  Thus all its entries and its characteristic resultant are
polynomial in the inverse-mass coordinates.
-/

namespace ArchonPhysics.MassWeightedCycleBridge

open ArchonPhysics.HarmonicModes
open ArchonPhysics.GenericSpectrumResultant

noncomputable section

theorem inv_sqrt_mul_inv_sqrt {x : Real} (hx : 0 < x) :
    (Real.sqrt x)⁻¹ * (Real.sqrt x)⁻¹ = x⁻¹ := by
  rw [← mul_inv, ← sq]
  rw [Real.sq_sqrt hx.le]

/-- The edge-space Gram matrix is the weighted cycle Laplacian with
inverse-mass edge weights. -/
theorem massWeighted_selfTranspose_eq_weightedCycleLaplacian
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    massWeightedDifferenceMatrix m *
        Matrix.transpose (massWeightedDifferenceMatrix m) =
      weightedCycleLaplacian (fun i ↦ (m.mass i)⁻¹) := by
  let S : Matrix (Lattice.Site N) (Lattice.Site N) Real :=
    Matrix.diagonal (fun i ↦ (Real.sqrt (m.mass i))⁻¹)
  let W : Matrix (Lattice.Site N) (Lattice.Site N) Real :=
    Matrix.diagonal (fun i ↦ (m.mass i)⁻¹)
  have hSW : S * S = W := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [S, W, inv_sqrt_mul_inv_sqrt (m.mass_pos i)]
    · simp [S, W, hij]
  change (differenceMatrix * S) * Matrix.transpose (differenceMatrix * S) =
    differenceMatrix * W * Matrix.transpose differenceMatrix
  calc
    (differenceMatrix * S) * Matrix.transpose (differenceMatrix * S) =
        (differenceMatrix * S) * (S * Matrix.transpose differenceMatrix) := by
      rw [Matrix.transpose_mul]
      simp [S]
    _ = differenceMatrix * (S * S) * Matrix.transpose differenceMatrix := by
      simp [Matrix.mul_assoc]
    _ = differenceMatrix * W * Matrix.transpose differenceMatrix := by rw [hSW]

end

end ArchonPhysics.MassWeightedCycleBridge
