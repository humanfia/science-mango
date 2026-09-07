import Family8Grounding.Family8FiniteRandomRigidMotionJohnRefinementProducerV1
import Family8Grounding.Family8PolynomialJohnFrameBoxCardPowerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped NNReal

namespace Family8FiniteRandomRigidMotionJohnJointTailV1

open Family8PolynomialJohnFrameBoxTestNetV1
open Family8PolynomialJohnFrameBoxCardPowerV1
open Family8FiniteRandomRigidMotionJohnJointSelectionV1

noncomputable section

/-!
# Explicit polynomial size of the joint rigid/John test family

The conflict part has exactly `#motionChoice * #iota` possible anchors.  The
John part has the previously proved fifteenth-power bound.  Consequently the
single union bound used by the joint selector has a directly consumable
polynomial upper bound, with no floor expression or catalogue callback.
-/

/-- Explicit real cardinality bound for the complete joint test type. -/
theorem card_rigidJohnJointTest_real_le_polynomial
    {motionChoice iota : Type}
    [Fintype motionChoice] [Fintype iota]
    (delta : NNReal) (hdelta : 0 < delta)
    (hdeltaUpper : delta <= (1 / 2 : NNReal)) :
    (Fintype.card
        (RigidJohnJointTest delta motionChoice iota hdelta) : Real) <=
      (Fintype.card motionChoice : Real) *
          (Fintype.card iota : Real) +
        (46082 / (delta : Real)) ^ 15 := by
  have hcatalogue :=
    card_catalogueIndex_real_le_div_pow delta hdelta hdeltaUpper
  simpa only [RigidJohnJointTest, Fintype.card_sum, Fintype.card_prod,
    Nat.cast_add, Nat.cast_mul] using
    add_le_add_right hcatalogue
      ((Fintype.card motionChoice : Real) * (Fintype.card iota : Real))

/-- A tail inequality using the displayed polynomial upper bound implies the
exact finite-test tail premise of the joint Chernoff selector. -/
theorem rigidJohnJointTailRoom_of_polynomialUpper
    {motionChoice iota : Type}
    [Fintype motionChoice] [Fintype iota]
    (delta : NNReal) (hdelta : 0 < delta)
    (hdeltaUpper : delta <= (1 / 2 : NNReal)) (A : Real)
    (hupper :
      ((Fintype.card motionChoice : Real) *
            (Fintype.card iota : Real) +
          (46082 / (delta : Real)) ^ 15) *
          Real.exp (Real.exp 1 - 1) < Real.exp A) :
    (Fintype.card
        (RigidJohnJointTest delta motionChoice iota hdelta) : Real) *
          Real.exp (Real.exp 1 - 1) < Real.exp A := by
  apply lt_of_le_of_lt _ hupper
  apply mul_le_mul_of_nonneg_right
  · exact card_rigidJohnJointTest_real_le_polynomial
      delta hdelta hdeltaUpper
  · exact (Real.exp_pos _).le

#print axioms card_rigidJohnJointTest_real_le_polynomial
#print axioms rigidJohnJointTailRoom_of_polynomialUpper

end
end Family8FiniteRandomRigidMotionJohnJointTailV1
