import ArchonPhysics.ScaledIntegerBirdDeterminantSignBridge

/-!
# Consumer: scaled integer Bird determinant sign certificates

A row-major integer Bird computation, together with an exact positive clearing
identity, certifies the sign of a real characteristic-polynomial evaluation.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.ScaledIntegerBirdDeterminantSignBridge

/-- Consumer-facing negative-sign certificate from exact Bird output. -/
theorem problem_real_charpoly_eval_neg_of_scaled_integer_birdDet
    {n : Nat} (C : Nat) (hC : 0 < C)
    (data : Array Int) (hsize : data.size = n * n)
    (A : Matrix (Fin n) (Fin n) Rat) (q : Rat)
    (hclear : (Matrix.ofArray data hsize).map (Int.castRingHom Rat) =
      (C : Rat) • (Matrix.scalar (Fin n) q - A))
    (hbird : BirdDet.birdDet n data < 0) :
    (A.map (Rat.castHom Real)).charpoly.eval (q : Real) < 0 :=
  real_charpoly_eval_neg_of_scaled_int_birdDet_neg
    C hC data hsize A q hclear hbird

/-- Consumer-facing positive-sign certificate from exact Bird output. -/
theorem problem_real_charpoly_eval_pos_of_scaled_integer_birdDet
    {n : Nat} (C : Nat) (hC : 0 < C)
    (data : Array Int) (hsize : data.size = n * n)
    (A : Matrix (Fin n) (Fin n) Rat) (q : Rat)
    (hclear : (Matrix.ofArray data hsize).map (Int.castRingHom Rat) =
      (C : Rat) • (Matrix.scalar (Fin n) q - A))
    (hbird : 0 < BirdDet.birdDet n data) :
    0 < (A.map (Rat.castHom Real)).charpoly.eval (q : Real) :=
  real_charpoly_eval_pos_of_scaled_int_birdDet_pos
    C hC data hsize A q hclear hbird

#print axioms rat_shifted_det_neg_of_scaled_int_det_neg
#print axioms real_charpoly_eval_neg_of_scaled_int_birdDet_neg
#print axioms problem_real_charpoly_eval_neg_of_scaled_integer_birdDet
#print axioms problem_real_charpoly_eval_pos_of_scaled_integer_birdDet

end ArchonPhysicsConsumers.Thermalization
