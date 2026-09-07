import Family8Grounding.Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyJointSelectorV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyTailNumericsV1

open LeanEval.Analysis.WangZahlKakeya
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRigidMotionOrthogonalScaleOnlyCatalogueScaleV1
open Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyConflictMeanV1
open Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyProductLawV1
open Family8KatzTaoFrostmanPropertiesV1

noncomputable section

/-!
# Canonical tail parameters for the scale-only two-family selector

Each family receives its own logarithmic threshold with a factor-two reserve.
The two reserves add to strictly less than the common product-outcome count,
discharging the selector's asymmetric two-family tail-room premise.
-/

/-- A logarithmic Chernoff threshold with one unit and a factor-two reserve. -/
def scaleOnlyJointTailParameter (testCard : Nat) : Real :=
  max 1 (Real.log
    (2 * (testCard : Real) * Real.exp (Real.exp 1 - 1) + 1))

/-- The canonical threshold for the complete fixed-John catalogue. -/
def scaleOnlyJointJohnTailParameter
    (delta : NNReal) (hdelta : 0 < delta) : Real :=
  scaleOnlyJointTailParameter
    (Fintype.card (ScaleOnlyFixedJohnTest delta hdelta))

/-- The canonical threshold for the internal elongated conflict catalogue. -/
def scaleOnlyJointConflictTailParameter
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) : Real :=
  scaleOnlyJointTailParameter
    (Fintype.card
      (ScaleOnlyFixedJohnElongatedTest D hdelta
        (scaleOnlyOrthogonalCatalogueScale D hdelta)))

theorem one_le_scaleOnlyJointTailParameter (testCard : Nat) :
    1 ≤ scaleOnlyJointTailParameter testCard :=
  le_max_left _ _

theorem two_mul_card_exp_lt_exp_scaleOnlyJointTailParameter
    (testCard : Nat) :
    2 * (testCard : Real) * Real.exp (Real.exp 1 - 1) <
      Real.exp (scaleOnlyJointTailParameter testCard) := by
  let x : Real :=
    2 * (testCard : Real) * Real.exp (Real.exp 1 - 1)
  have hx : 0 ≤ x := by
    dsimp only [x]
    positivity
  have hx1 : 0 < x + 1 := by linarith
  have hxlt : x < Real.exp (Real.log (x + 1)) := by
    rw [Real.exp_log hx1]
    linarith
  have hmono : Real.exp (Real.log (x + 1)) ≤
      Real.exp (max 1 (Real.log (x + 1))) :=
    Real.exp_le_exp.mpr (le_max_right _ _)
  simpa only [scaleOnlyJointTailParameter, x] using hxlt.trans_le hmono

theorem one_le_scaleOnlyJointJohnTailParameter
    (delta : NNReal) (hdelta : 0 < delta) :
    1 ≤ scaleOnlyJointJohnTailParameter delta hdelta :=
  one_le_scaleOnlyJointTailParameter _

theorem scaleOnlyJointTailRoom
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) :
    (Fintype.card (ScaleOnlyFixedJohnTest delta hdelta) : Real) *
          Real.exp (Real.exp 1 - 1) *
          Real.exp (scaleOnlyJointConflictTailParameter D hdelta) +
        (Fintype.card
          (ScaleOnlyFixedJohnElongatedTest D hdelta
            (scaleOnlyOrthogonalCatalogueScale D hdelta)) : Real) *
          Real.exp (Real.exp 1 - 1) *
          Real.exp (scaleOnlyJointJohnTailParameter delta hdelta) <
      Real.exp (scaleOnlyJointJohnTailParameter delta hdelta) *
        Real.exp (scaleOnlyJointConflictTailParameter D hdelta) := by
  let x : Real :=
    (Fintype.card (ScaleOnlyFixedJohnTest delta hdelta) : Real) *
      Real.exp (Real.exp 1 - 1)
  let y : Real :=
    (Fintype.card
      (ScaleOnlyFixedJohnElongatedTest D hdelta
        (scaleOnlyOrthogonalCatalogueScale D hdelta)) : Real) *
      Real.exp (Real.exp 1 - 1)
  let p : Real := Real.exp (scaleOnlyJointJohnTailParameter delta hdelta)
  let q : Real := Real.exp (scaleOnlyJointConflictTailParameter D hdelta)
  have hx : 2 * x < p := by
    simpa only [x, p, scaleOnlyJointJohnTailParameter, mul_assoc] using
      two_mul_card_exp_lt_exp_scaleOnlyJointTailParameter
        (Fintype.card (ScaleOnlyFixedJohnTest delta hdelta))
  have hy : 2 * y < q := by
    simpa only [y, q, scaleOnlyJointConflictTailParameter, mul_assoc] using
      two_mul_card_exp_lt_exp_scaleOnlyJointTailParameter
        (Fintype.card
          (ScaleOnlyFixedJohnElongatedTest D hdelta
            (scaleOnlyOrthogonalCatalogueScale D hdelta)))
  have hxq : 2 * (x * q) < p * q := by
    calc
      2 * (x * q) = (2 * x) * q := by ring
      _ < p * q := mul_lt_mul_of_pos_right hx (Real.exp_pos _)
  have hyp : 2 * (y * p) < p * q := by
    calc
      2 * (y * p) = (2 * y) * p := by ring
      _ < q * p := mul_lt_mul_of_pos_right hy (Real.exp_pos _)
      _ = p * q := by ring
  dsimp only [x, y, p, q] at hxq hyp ⊢
  nlinarith

#print axioms scaleOnlyJointTailParameter
#print axioms scaleOnlyJointJohnTailParameter
#print axioms scaleOnlyJointConflictTailParameter
#print axioms one_le_scaleOnlyJointTailParameter
#print axioms two_mul_card_exp_lt_exp_scaleOnlyJointTailParameter
#print axioms one_le_scaleOnlyJointJohnTailParameter
#print axioms scaleOnlyJointTailRoom

end
end Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyTailNumericsV1
