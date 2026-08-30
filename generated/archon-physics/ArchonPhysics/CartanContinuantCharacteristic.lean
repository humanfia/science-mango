import ArchonPhysics.AdjacentUnitFiberContinuantResultant
import ArchonPhysics.OddVolumePathTwoToOneResultant
import Mathlib.LinearAlgebra.Matrix.Cartan

/-!
# Type-A Cartan characteristic polynomial as the adjacent-fiber continuant

This file closes the matrix bridge for the abstract continuant used in
`AdjacentUnitFiberContinuantResultant`.  We prove the characteristic-polynomial
recurrence for Mathlib's type-A Cartan matrix by two Laplace expansions, then
identify its characteristic polynomial with `cartanContinuant` in every rank.

Combining this bridge with the existing broken-cycle path factorization also
identifies the actual path-weighted cycle characteristic polynomial and its
zero-mode quotient with this continuant.  No canonical two-site slice or
vertical-partial identification is asserted here.
-/

namespace ArchonPhysics.CartanContinuantCharacteristic

open ArchonPhysics.AdjacentUnitFiberContinuantResultant
open ArchonPhysics.OddVolumePathTwoToOneResultant
open ArchonPhysics.PathLaplacianSpecialization
open ArchonPhysics.PeriodicWeightedCycleBlockGluing
open Polynomial

noncomputable section

/-- Taking a principal submatrix along an injective index map commutes with
forming the characteristic matrix. -/
theorem charmatrix_submatrix_same_of_injective
    {R : Type*} [CommRing R]
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (e : m → n) (he : Function.Injective e) :
    A.charmatrix.submatrix e e = (A.submatrix e e).charmatrix := by
  ext i j : 1
  by_cases hij : i = j
  · subst j
    simp [Matrix.submatrix_apply]
  · have heij : e i ≠ e j := by
      intro h
      exact hij (he h)
    simp [Matrix.submatrix_apply, hij, heij]

/-- Deleting the first row and column of `A_{n+1}` gives `A_n`. -/
theorem cartanMatrix_A_drop_first (n : Nat) :
    (CartanMatrix.A (n + 1)).submatrix Fin.succ Fin.succ =
      CartanMatrix.A n := by
  ext i j
  simp only [CartanMatrix.A, Matrix.submatrix_apply, Matrix.of_apply,
    Fin.val_succ]
  grind

/-- Deleting the first two rows and columns of `A_{n+2}` gives `A_n`. -/
theorem cartanMatrix_A_drop_first_two (n : Nat) :
    (CartanMatrix.A (n + 2)).submatrix
        (fun i : Fin n ↦ i.succ.succ) (fun j : Fin n ↦ j.succ.succ) =
      CartanMatrix.A n := by
  ext i j
  simp only [CartanMatrix.A, Matrix.submatrix_apply, Matrix.of_apply,
    Fin.val_succ]
  grind

/-- The characteristic polynomial of the type-A Cartan matrix obeys the
standard continuant recurrence. -/
theorem cartanMatrix_A_charpoly_add_two (n : Nat) :
    (CartanMatrix.A (n + 2)).charpoly =
      (X - C 2) * (CartanMatrix.A (n + 1)).charpoly -
        (CartanMatrix.A n).charpoly := by
  let M := (CartanMatrix.A (n + 2)).charmatrix
  have hminor0 :
      M.submatrix Fin.succ Fin.succ =
        (CartanMatrix.A (n + 1)).charmatrix := by
    calc
      M.submatrix Fin.succ Fin.succ =
          ((CartanMatrix.A (n + 2)).submatrix Fin.succ Fin.succ).charmatrix := by
        simpa [M] using charmatrix_submatrix_same_of_injective
          (CartanMatrix.A (n + 2)) Fin.succ (fun _ _ h ↦ Fin.succ_inj.mp h)
      _ = (CartanMatrix.A (n + 1)).charmatrix := by
        rw [cartanMatrix_A_drop_first]
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial Int) :=
    M.submatrix Fin.succ (Fin.succAbove 1)
  have hBminor :
      B.submatrix Fin.succ Fin.succ = (CartanMatrix.A n).charmatrix := by
    calc
      B.submatrix Fin.succ Fin.succ =
          M.submatrix (fun i : Fin n ↦ i.succ.succ)
            (fun j : Fin n ↦ j.succ.succ) := by
        ext i j
        simp [B, Matrix.submatrix_apply]
      _ = ((CartanMatrix.A (n + 2)).submatrix
          (fun i : Fin n ↦ i.succ.succ)
          (fun j : Fin n ↦ j.succ.succ)).charmatrix := by
        simpa [M] using charmatrix_submatrix_same_of_injective
          (CartanMatrix.A (n + 2)) (fun i : Fin n ↦ i.succ.succ)
            (fun _ _ h ↦ Fin.succ_inj.mp (Fin.succ_inj.mp h))
      _ = (CartanMatrix.A n).charmatrix := by
        rw [cartanMatrix_A_drop_first_two]
  have hBdet : B.det = ((CartanMatrix.A n).charmatrix).det := by
    rw [Matrix.det_succ_column_zero]
    simp only [Fin.sum_univ_succ, Fin.succAbove_zero]
    rw [hBminor]
    simp [B, M, CartanMatrix.A, Fin.ext_iff]
  have hdiag : M 0 0 = X - C 2 := by
    simp [M, CartanMatrix.A]
  have hoff : M 0 (Fin.succ 0) = 1 := by
    simp [M, CartanMatrix.A, Fin.ext_iff]
  have hfar (i : Fin n) : M 0 i.succ.succ = 0 := by
    simp [M, CartanMatrix.A, Fin.ext_iff]
  change M.det =
    (X - C 2) * ((CartanMatrix.A (n + 1)).charmatrix).det -
      ((CartanMatrix.A n).charmatrix).det
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.succAbove_zero]
  rw [hminor0]
  have hminor1 :
      M.submatrix Fin.succ (Fin.succ 0).succAbove = B := by
    rfl
  rw [hminor1, hBdet, hdiag, hoff]
  simp_rw [hfar]
  simp only [mul_zero]
  simp
  ring

/-- The abstract adjacent-fiber continuant is exactly the characteristic
polynomial of Mathlib's type-A Cartan matrix. -/
theorem cartanContinuant_eq_cartanMatrix_A_charpoly (n : Nat) :
    cartanContinuant n = (CartanMatrix.A n).charpoly := by
  induction n using Nat.twoStepInduction with
  | zero => simp [Matrix.charpoly, CartanMatrix.A]
  | one =>
      simp [Matrix.charpoly, Matrix.charmatrix, CartanMatrix.A]
  | more n hn hn1 =>
      rw [cartanContinuant_add_two, cartanMatrix_A_charpoly_add_two, hn, hn1]


/-- The actual periodic weighted-cycle matrix with one edge broken has
characteristic polynomial `X` times the mapped adjacent continuant. -/
theorem finWeightedCycleLaplacian_path_charpoly_eq_cartanContinuant (n : Nat) :
    (finWeightedCycleLaplacian (pathWeightCoordinates (n + 1))).charpoly =
      X * (cartanContinuant n).map (Int.castRingHom Real) := by
  rw [finWeightedCycleLaplacian_path_charpoly_eq]
  simp only [unitPathIntegerPositiveCharacteristic]
  rw [← cartanContinuant_eq_cartanMatrix_A_charpoly]

/-- After removing its translational zero mode, the same broken-cycle path
matrix has exactly the mapped adjacent continuant as characteristic
polynomial. -/
theorem finWeightedCycleLaplacian_path_charpoly_divX_eq_cartanContinuant
    (n : Nat) :
    (finWeightedCycleLaplacian
      (pathWeightCoordinates (n + 1))).charpoly.divX =
      (cartanContinuant n).map (Int.castRingHom Real) := by
  rw [finWeightedCycleLaplacian_path_charpoly_divX_eq]
  simp only [unitPathIntegerPositiveCharacteristic]
  rw [← cartanContinuant_eq_cartanMatrix_A_charpoly]

end

end ArchonPhysics.CartanContinuantCharacteristic
