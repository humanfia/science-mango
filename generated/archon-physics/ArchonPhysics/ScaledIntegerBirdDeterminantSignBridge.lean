import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Correctness
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Scaled integer and Bird determinant sign certificates

This module transfers exact determinant signs from an integer clearing of a
rational shifted matrix to the rational determinant and then to the
characteristic polynomial of the corresponding real matrix. It also exposes
the flat row-major `Array Int` interface certified by Bird's algorithm.
-/

open scoped Matrix

namespace ArchonPhysics.ScaledIntegerBirdDeterminantSignBridge

/-- A negative determinant of a positive integer clearing forces the original
rational shifted determinant to be negative. -/
theorem rat_shifted_det_neg_of_scaled_int_det_neg
    {n : Nat} (C : Nat) (hC : 0 < C)
    (K : Matrix (Fin n) (Fin n) Int)
    (A : Matrix (Fin n) (Fin n) Rat) (q : Rat)
    (hclear : K.map (Int.castRingHom Rat) =
      (C : Rat) • (Matrix.scalar (Fin n) q - A))
    (hdet : K.det < 0) :
    (Matrix.scalar (Fin n) q - A).det < 0 := by
  have hdetEq : (K.det : Rat) =
      (C : Rat) ^ n * (Matrix.scalar (Fin n) q - A).det := by
    calc
      (K.det : Rat) = (K.map (Int.castRingHom Rat)).det := by
        simpa only [RingHom.mapMatrix_apply, Int.coe_castRingHom] using
          (Int.castRingHom Rat).map_det K
      _ = ((C : Rat) • (Matrix.scalar (Fin n) q - A)).det := by rw [hclear]
      _ = (C : Rat) ^ n * (Matrix.scalar (Fin n) q - A).det := by
        simp
  have hdetRat : (K.det : Rat) < 0 := by exact_mod_cast hdet
  have hCrat : (0 : Rat) < C := by exact_mod_cast hC
  have hpow : (0 : Rat) < (C : Rat) ^ n := pow_pos hCrat _
  rw [hdetEq] at hdetRat
  nlinarith

/-- A positive determinant of a positive integer clearing forces the original
rational shifted determinant to be positive. -/
theorem rat_shifted_det_pos_of_scaled_int_det_pos
    {n : Nat} (C : Nat) (hC : 0 < C)
    (K : Matrix (Fin n) (Fin n) Int)
    (A : Matrix (Fin n) (Fin n) Rat) (q : Rat)
    (hclear : K.map (Int.castRingHom Rat) =
      (C : Rat) • (Matrix.scalar (Fin n) q - A))
    (hdet : 0 < K.det) :
    0 < (Matrix.scalar (Fin n) q - A).det := by
  have hdetEq : (K.det : Rat) =
      (C : Rat) ^ n * (Matrix.scalar (Fin n) q - A).det := by
    calc
      (K.det : Rat) = (K.map (Int.castRingHom Rat)).det := by
        simpa only [RingHom.mapMatrix_apply, Int.coe_castRingHom] using
          (Int.castRingHom Rat).map_det K
      _ = ((C : Rat) • (Matrix.scalar (Fin n) q - A)).det := by rw [hclear]
      _ = (C : Rat) ^ n * (Matrix.scalar (Fin n) q - A).det := by
        simp
  have hdetRat : (0 : Rat) < K.det := by exact_mod_cast hdet
  have hCrat : (0 : Rat) < C := by exact_mod_cast hC
  have hpow : (0 : Rat) < (C : Rat) ^ n := pow_pos hCrat _
  rw [hdetEq] at hdetRat
  nlinarith

/-- A negative scaled integer determinant gives the same sign for the real
characteristic polynomial at the mapped rational evaluation point. -/
theorem real_charpoly_eval_neg_of_scaled_int_det_neg
    {n : Nat} (C : Nat) (hC : 0 < C)
    (K : Matrix (Fin n) (Fin n) Int)
    (A : Matrix (Fin n) (Fin n) Rat) (q : Rat)
    (hclear : K.map (Int.castRingHom Rat) =
      (C : Rat) • (Matrix.scalar (Fin n) q - A))
    (hdet : K.det < 0) :
    (A.map (Rat.castHom Real)).charpoly.eval (q : Real) < 0 := by
  have hrat : A.charpoly.eval q < 0 := by
    rw [Matrix.eval_charpoly]
    exact rat_shifted_det_neg_of_scaled_int_det_neg C hC K A q hclear hdet
  have hcast : ((A.charpoly.eval q : Rat) : Real) < 0 := by
    exact_mod_cast hrat
  change (A.map (Rat.castHom Real)).charpoly.eval
    ((Rat.castHom Real) q) < 0
  rw [Matrix.charpoly_map, Polynomial.eval_map_apply]
  exact hcast

/-- A positive scaled integer determinant gives the same sign for the real
characteristic polynomial at the mapped rational evaluation point. -/
theorem real_charpoly_eval_pos_of_scaled_int_det_pos
    {n : Nat} (C : Nat) (hC : 0 < C)
    (K : Matrix (Fin n) (Fin n) Int)
    (A : Matrix (Fin n) (Fin n) Rat) (q : Rat)
    (hclear : K.map (Int.castRingHom Rat) =
      (C : Rat) • (Matrix.scalar (Fin n) q - A))
    (hdet : 0 < K.det) :
    0 < (A.map (Rat.castHom Real)).charpoly.eval (q : Real) := by
  have hrat : 0 < A.charpoly.eval q := by
    rw [Matrix.eval_charpoly]
    exact rat_shifted_det_pos_of_scaled_int_det_pos C hC K A q hclear hdet
  have hcast : (0 : Real) < ((A.charpoly.eval q : Rat) : Real) := by
    exact_mod_cast hrat
  change 0 < (A.map (Rat.castHom Real)).charpoly.eval
    ((Rat.castHom Real) q)
  rw [Matrix.charpoly_map, Polynomial.eval_map_apply]
  exact hcast

/-- Bird's exact negative array output is a negative determinant certificate
for the integer matrix represented by that row-major array. -/
theorem int_ofArray_det_neg_of_birdDet_neg
    {n : Nat} (data : Array Int) (hsize : data.size = n * n)
    (hbird : BirdDet.birdDet n data < 0) :
    (Matrix.ofArray data hsize).det < 0 := by
  rw [BirdDet.det_eq_birdDet data hsize]
  exact hbird

/-- Bird's exact positive array output is a positive determinant certificate
for the integer matrix represented by that row-major array. -/
theorem int_ofArray_det_pos_of_birdDet_pos
    {n : Nat} (data : Array Int) (hsize : data.size = n * n)
    (hbird : 0 < BirdDet.birdDet n data) :
    0 < (Matrix.ofArray data hsize).det := by
  rw [BirdDet.det_eq_birdDet data hsize]
  exact hbird

/-- Direct flat-array Bird certificate for a negative real characteristic
polynomial value. -/
theorem real_charpoly_eval_neg_of_scaled_int_birdDet_neg
    {n : Nat} (C : Nat) (hC : 0 < C)
    (data : Array Int) (hsize : data.size = n * n)
    (A : Matrix (Fin n) (Fin n) Rat) (q : Rat)
    (hclear : (Matrix.ofArray data hsize).map (Int.castRingHom Rat) =
      (C : Rat) • (Matrix.scalar (Fin n) q - A))
    (hbird : BirdDet.birdDet n data < 0) :
    (A.map (Rat.castHom Real)).charpoly.eval (q : Real) < 0 :=
  real_charpoly_eval_neg_of_scaled_int_det_neg C hC
    (Matrix.ofArray data hsize) A q hclear
      (int_ofArray_det_neg_of_birdDet_neg data hsize hbird)

/-- Direct flat-array Bird certificate for a positive real characteristic
polynomial value. -/
theorem real_charpoly_eval_pos_of_scaled_int_birdDet_pos
    {n : Nat} (C : Nat) (hC : 0 < C)
    (data : Array Int) (hsize : data.size = n * n)
    (A : Matrix (Fin n) (Fin n) Rat) (q : Rat)
    (hclear : (Matrix.ofArray data hsize).map (Int.castRingHom Rat) =
      (C : Rat) • (Matrix.scalar (Fin n) q - A))
    (hbird : 0 < BirdDet.birdDet n data) :
    0 < (A.map (Rat.castHom Real)).charpoly.eval (q : Real) :=
  real_charpoly_eval_pos_of_scaled_int_det_pos C hC
    (Matrix.ofArray data hsize) A q hclear
      (int_ofArray_det_pos_of_birdDet_pos data hsize hbird)

end ArchonPhysics.ScaledIntegerBirdDeterminantSignBridge
