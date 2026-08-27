import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Modular certificates for rational matrix nonsingularity

This module packages the elementary bridge used by exact finite-dimensional
collision certificates.  A right inverse after reduction modulo a prime
forces the determinant of the cleared integer matrix to be nonzero.  If that
integer matrix is a nonzero scalar multiple of a rational matrix, the
original rational determinant is nonzero as well.
-/

open scoped Matrix

namespace ArchonPhysics.ModularMatrixDeterminantCertificate

/-- A square matrix with a right inverse has nonzero determinant. -/
theorem det_ne_zero_of_mul_eq_one
    {R ι : Type*} [CommRing R] [Nontrivial R]
    [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι R} (h : A * B = 1) : A.det ≠ 0 := by
  intro hzero
  have hdet := congrArg Matrix.det h
  rw [Matrix.det_mul, hzero, zero_mul, Matrix.det_one] at hdet
  exact zero_ne_one hdet

/-- A modular right inverse certifies that the determinant of the original
integer matrix is nonzero.  Injectivity of reduction is not required: a zero
integer determinant would necessarily reduce to zero. -/
theorem int_det_ne_zero_of_modular_right_inverse
    {p : Nat} [Nontrivial (ZMod p)] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι Int) (B : Matrix ι ι (ZMod p))
    (h : A.map (Int.castRingHom (ZMod p)) * B = 1) :
    A.det ≠ 0 := by
  have hmod :
      (A.map (Int.castRingHom (ZMod p))).det ≠ 0 :=
    det_ne_zero_of_mul_eq_one h
  intro hzero
  apply hmod
  have hmap := (Int.castRingHom (ZMod p)).map_det A
  simpa only [RingHom.mapMatrix_apply, hzero, map_zero] using hmap.symm

/-- If an integer matrix casts to a nonzero scalar multiple of a rational
matrix, nonvanishing of the integer determinant transfers to the rational
matrix. -/
theorem rat_det_ne_zero_of_cleared
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι Rat) (Aint : Matrix ι ι Int) (d : Rat)
    (_hd : d ≠ 0)
    (hclear : Aint.map (Int.castRingHom Rat) = d • A)
    (hint : Aint.det ≠ 0) :
    A.det ≠ 0 := by
  intro hzero
  have hcast : ((Aint.det : Int) : Rat) ≠ 0 := by
    exact_mod_cast hint
  apply hcast
  calc
    ((Aint.det : Int) : Rat) =
        (Aint.map (Int.castRingHom Rat)).det := by
          simpa only [RingHom.mapMatrix_apply, Int.coe_castRingHom] using
            (Int.castRingHom Rat).map_det Aint
    _ = (d • A).det := by rw [hclear]
    _ = d ^ Fintype.card ι * A.det := Matrix.det_smul A d
    _ = 0 := by rw [hzero, mul_zero]

/-- Combined modular-to-rational nonsingularity certificate. -/
theorem rat_det_ne_zero_of_modular_right_inverse
    {p : Nat} [Nontrivial (ZMod p)] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι Rat) (Aint : Matrix ι ι Int)
    (B : Matrix ι ι (ZMod p)) (d : Rat)
    (hd : d ≠ 0)
    (hclear : Aint.map (Int.castRingHom Rat) = d • A)
    (hmod : Aint.map (Int.castRingHom (ZMod p)) * B = 1) :
    A.det ≠ 0 :=
  rat_det_ne_zero_of_cleared A Aint d hd hclear
    (int_det_ne_zero_of_modular_right_inverse Aint B hmod)

end ArchonPhysics.ModularMatrixDeterminantCertificate
