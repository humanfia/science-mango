import Family8Grounding.Family8FiniteRandomRigidMotionPaperElongatedCoordinateContainmentV1
import Family8Grounding.Family8CommonPointTubePackingV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal InnerProductSpace Matrix

namespace Family8FiniteRandomRigidMotionPaperCommonPointElongatedBudgetV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionPaperElongatedFrameTestV1
open Family8FiniteRandomRigidMotionPaperElongatedCoordinateContainmentV1

noncomputable section

/-!
# Common-point input for the elongated coordinate budget

Once two small-radius tubes share a point, both midpoint residuals are
`O(rho)` transversely and bounded longitudinally.  Thus only an unoriented
angular estimate is needed to put one tube in the other's side-six elongated
test body.
-/

/-- A common carrier point plus `90 rho` transverse direction coordinates
supplies all three scalar budgets for the side-six elongated body. -/
theorem midpointDirectionBudget_of_commonPoint
    {rho : NNReal} (T U : Tube rho) (x : Space)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (hframe : frame 2 = T.axis.direction)
    (hrho : rho ≤ (1 / 100 : NNReal))
    (hxT : x ∈ T.carrier) (hxU : x ∈ U.carrier)
    (htrans : ∀ k : Fin 3, k ≠ 2 →
      |⟪frame k, U.axis.direction⟫_ℝ| ≤ 90 * (rho : Real)) :
    ∀ k : Fin 3,
      (rho : Real) +
          |⟪frame k, tubeAxisMidpoint U - tubeAxisMidpoint T⟫_ℝ| +
          (2 : Real)⁻¹ * |⟪frame k, U.axis.direction⟫_ℝ| ≤
        ((paperElongatedSides rho k : NNReal) : Real) / 2 := by
  let aT := Family8CommonPointTubePackingV1.tubePointLongitudinal x T
  let aU := Family8CommonPointTubePackingV1.tubePointLongitudinal x U
  let eT := Family8CommonPointTubePackingV1.tubePointTransverse x T
  let eU := Family8CommonPointTubePackingV1.tubePointTransverse x U
  have haT : |aT| ≤ (51 : Real) / 100 := by
    exact Family8CommonPointTubePackingV1.abs_tubePointLongitudinal_le
      T hrho hxT
  have haU : |aU| ≤ (51 : Real) / 100 := by
    exact Family8CommonPointTubePackingV1.abs_tubePointLongitudinal_le
      U hrho hxU
  have heT : ‖eT‖ ≤ 2 * (rho : Real) := by
    exact Family8CommonPointTubePackingV1.norm_tubePointTransverse_le_two_mul
      T hxT
  have heU : ‖eU‖ ≤ 2 * (rho : Real) := by
    exact Family8CommonPointTubePackingV1.norm_tubePointTransverse_le_two_mul
      U hxU
  have hmid :
      tubeAxisMidpoint U - tubeAxisMidpoint T =
        aU • U.axis.direction - aT • T.axis.direction + (eU - eT) := by
    dsimp only [aT, aU, eT, eU]
    simp only [Family8CommonPointTubePackingV1.tubePointTransverse,
      Family8CommonPointTubePackingV1.tubePointLongitudinal,
      Family8CommonPointTubePackingV1.tubeAxisMidpoint,
      tubeAxisMidpoint]
    module
  have heres : ‖eU - eT‖ ≤ 4 * (rho : Real) := by
    calc
      ‖eU - eT‖ ≤ ‖eU‖ + ‖eT‖ := norm_sub_le _ _
      _ ≤ 2 * (rho : Real) + 2 * (rho : Real) := add_le_add heU heT
      _ = 4 * (rho : Real) := by ring
  have hmidnorm :
      ‖tubeAxisMidpoint U - tubeAxisMidpoint T‖ ≤
        (102 : Real) / 100 + 4 * (rho : Real) := by
    rw [hmid]
    calc
      ‖aU • U.axis.direction - aT • T.axis.direction + (eU - eT)‖ ≤
          ‖aU • U.axis.direction - aT • T.axis.direction‖ +
            ‖eU - eT‖ := norm_add_le _ _
      _ ≤ (‖aU • U.axis.direction‖ +
            ‖aT • T.axis.direction‖) + 4 * (rho : Real) :=
        add_le_add (norm_sub_le _ _) heres
      _ = |aU| + |aT| + 4 * (rho : Real) := by
        simp [norm_smul, U.axis.norm_direction, T.axis.norm_direction,
          Real.norm_eq_abs]
      _ ≤ (51 : Real) / 100 + (51 : Real) / 100 +
          4 * (rho : Real) := by gcongr
      _ = (102 : Real) / 100 + 4 * (rho : Real) := by ring
  have hmidcoordAll (k : Fin 3) :
      |⟪frame k, tubeAxisMidpoint U - tubeAxisMidpoint T⟫_ℝ| ≤
        (102 : Real) / 100 + 4 * (rho : Real) := by
    have hinner := abs_real_inner_le_norm
      (frame k) (tubeAxisMidpoint U - tubeAxisMidpoint T)
    rw [frame.norm_eq_one, one_mul] at hinner
    exact hinner.trans hmidnorm
  have htransMid (k : Fin 3) (hk : k ≠ 2) :
      |⟪frame k, tubeAxisMidpoint U - tubeAxisMidpoint T⟫_ℝ| ≤
        (51 : Real) / 100 * (90 * (rho : Real)) +
          4 * (rho : Real) := by
    have horth : ⟪frame k, T.axis.direction⟫_ℝ = 0 := by
      rw [← hframe]
      exact frame.inner_eq_zero hk
    have heinner : |⟪frame k, eU - eT⟫_ℝ| ≤ 4 * (rho : Real) := by
      have hinner := abs_real_inner_le_norm (frame k) (eU - eT)
      rw [frame.norm_eq_one, one_mul] at hinner
      exact hinner.trans heres
    have hinnerEq :
        ⟪frame k, tubeAxisMidpoint U - tubeAxisMidpoint T⟫_ℝ =
          aU * ⟪frame k, U.axis.direction⟫_ℝ +
            ⟪frame k, eU - eT⟫_ℝ := by
      rw [hmid, inner_add_right, inner_sub_right,
        inner_smul_right, inner_smul_right, horth, mul_zero, sub_zero]
    rw [hinnerEq]
    calc
      |aU * ⟪frame k, U.axis.direction⟫_ℝ +
          ⟪frame k, eU - eT⟫_ℝ| ≤
        |aU * ⟪frame k, U.axis.direction⟫_ℝ| +
          |⟪frame k, eU - eT⟫_ℝ| := abs_add_le _ _
      _ = |aU| * |⟪frame k, U.axis.direction⟫_ℝ| +
          |⟪frame k, eU - eT⟫_ℝ| := by rw [abs_mul]
      _ ≤ (51 : Real) / 100 * (90 * (rho : Real)) +
          4 * (rho : Real) := by
        exact add_le_add
          (mul_le_mul haU (htrans k hk) (abs_nonneg _) (by norm_num))
          heinner
  have hdirAll (k : Fin 3) :
      |⟪frame k, U.axis.direction⟫_ℝ| ≤ 1 := by
    have hinner := abs_real_inner_le_norm (frame k) U.axis.direction
    rw [frame.norm_eq_one, one_mul, U.axis.norm_direction] at hinner
    exact hinner
  have hrhoReal : (rho : Real) ≤ (1 : Real) / 100 := by
    exact_mod_cast hrho
  intro k
  have hmidk := hmidcoordAll k
  have hdirk := hdirAll k
  fin_cases k
  · norm_num [paperElongatedSides] at ⊢
    norm_num at hrhoReal ⊢
    nlinarith [htransMid 0 (by decide), htrans 0 (by decide)]
  · norm_num [paperElongatedSides] at ⊢
    norm_num at hrhoReal ⊢
    nlinarith [htransMid 1 (by decide), htrans 1 (by decide)]
  · norm_num [paperElongatedSides] at ⊢
    norm_num at hrhoReal hmidk hdirk ⊢
    nlinarith

/-- The coordinate budget immediately yields literal carrier containment. -/
theorem carrier_subset_paperElongatedBody_of_commonPoint
    {rho : NNReal} (T U : Tube rho) (x : Space)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (hframe : frame 2 = T.axis.direction)
    (hrho : rho ≤ (1 / 100 : NNReal))
    (hxT : x ∈ T.carrier) (hxU : x ∈ U.carrier)
    (htrans : ∀ k : Fin 3, k ≠ 2 →
      |⟪frame k, U.axis.direction⟫_ℝ| ≤ 90 * (rho : Real)) :
    U.carrier ⊆ (paperElongatedBody T frame : Set Space) := by
  apply carrier_subset_paperElongatedBody_of_midpointDirectionBudget
  exact midpointDirectionBudget_of_commonPoint
    T U x frame hframe hrho hxT hxU htrans

#print axioms midpointDirectionBudget_of_commonPoint
#print axioms carrier_subset_paperElongatedBody_of_commonPoint

end
end Family8FiniteRandomRigidMotionPaperCommonPointElongatedBudgetV1
