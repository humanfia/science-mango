import Family8Grounding.Family8FiniteRandomRigidMotionPaperElongatedFrameTestV1
import Submission.Kakeya.ConvexFactoring.TubeFrameBoxDimensions
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

namespace Family8FiniteRandomRigidMotionPaperElongatedCoordinateContainmentV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.TransverseCoordinateOverlap
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionPaperElongatedFrameTestV1

noncomputable section

/-!
# Scalar-coordinate seam for honest elongated conflict tests

This module reduces containment in the honest elongated frame body to an
explicit one-dimensional budget along each vector of its orthonormal frame.
The remaining geometric task is exactly to derive these three scalar budgets
from failure of essential distinctness.
-/

/-- Coordinate clearance along every axis point puts the entire closed tube
inside the elongated frame body. -/
theorem carrier_subset_paperElongatedBody_of_axisCoordinateBudget
    {rho : NNReal} (T U : Tube rho)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (haxis : ∀ t : Real, t ∈ Set.Icc (0 : Real) 1 → ∀ i : Fin 3,
      |⟪frame i, U.axis.base + t • U.axis.direction⟫_ℝ -
          ⟪frame i, tubeAxisMidpoint T⟫_ℝ| + (rho : Real) ≤
        ((paperElongatedSides rho i : NNReal) : Real) / 2) :
    U.carrier ⊆ (paperElongatedBody T frame : Set Space) := by
  intro x hx
  rw [Tube.carrier,
    U.axis.isCompact_carrier.cthickening_eq_biUnion_closedBall
      (show 0 ≤ (rho : Real) by positivity)] at hx
  simp only [mem_iUnion, Metric.mem_closedBall] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  rw [U.axis.carrier_eq_image] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  rw [coe_paperElongatedBody,
    FrameBox.carrier_eq_centeredCoordinateWindow,
    mem_centeredCoordinateWindow_iff]
  intro i
  have hnear :
      |⟪frame i, x⟫_ℝ -
        ⟪frame i, U.axis.base + t • U.axis.direction⟫_ℝ| ≤
          (rho : Real) :=
    (abs_inner_sub_inner_le_dist_of_norm_eq_one
      (frame i) x (U.axis.base + t • U.axis.direction)
      (frame.norm_eq_one i)).trans hxy
  change |⟪frame i, x⟫_ℝ -
      ⟪frame i, tubeAxisMidpoint T⟫_ℝ| ≤
    ((paperElongatedSides rho i : NNReal) : Real) / 2
  calc
    |⟪frame i, x⟫_ℝ - ⟪frame i, tubeAxisMidpoint T⟫_ℝ| ≤
        |⟪frame i, x⟫_ℝ -
          ⟪frame i, U.axis.base + t • U.axis.direction⟫_ℝ| +
        |⟪frame i, U.axis.base + t • U.axis.direction⟫_ℝ -
          ⟪frame i, tubeAxisMidpoint T⟫_ℝ| := by
            exact abs_sub_le _ _ _
    _ ≤ (rho : Real) +
        |⟪frame i, U.axis.base + t • U.axis.direction⟫_ℝ -
          ⟪frame i, tubeAxisMidpoint T⟫_ℝ| :=
      add_le_add hnear (le_refl _)
    _ = |⟪frame i, U.axis.base + t • U.axis.direction⟫_ℝ -
          ⟪frame i, tubeAxisMidpoint T⟫_ℝ| + (rho : Real) := by ring
    _ ≤ ((paperElongatedSides rho i : NNReal) : Real) / 2 :=
      haxis t ht i

/-- Axis points are the midpoint plus a signed half-parameter displacement. -/
theorem tubeAxisPoint_eq_midpoint_add
    {rho : NNReal} (U : Tube rho) (t : Real) :
    U.axis.base + t • U.axis.direction =
      tubeAxisMidpoint U + (t - (2 : Real)⁻¹) • U.axis.direction := by
  simp only [tubeAxisMidpoint]
  module

/-- A parameter-free sufficient condition: midpoint displacement, direction
projection, and radius fit inside each elongated half-side. -/
theorem carrier_subset_paperElongatedBody_of_midpointDirectionBudget
    {rho : NNReal} (T U : Tube rho)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (hbudget : ∀ i : Fin 3,
      (rho : Real) +
          |⟪frame i, tubeAxisMidpoint U - tubeAxisMidpoint T⟫_ℝ| +
          (2 : Real)⁻¹ * |⟪frame i, U.axis.direction⟫_ℝ| ≤
        ((paperElongatedSides rho i : NNReal) : Real) / 2) :
    U.carrier ⊆ (paperElongatedBody T frame : Set Space) := by
  apply carrier_subset_paperElongatedBody_of_axisCoordinateBudget T U frame
  intro t ht i
  have htcenter : |t - (2 : Real)⁻¹| ≤ (2 : Real)⁻¹ := by
    rw [abs_le]
    constructor <;> norm_num at * <;> linarith [ht.1, ht.2]
  rw [tubeAxisPoint_eq_midpoint_add]
  have hsplit :
      ⟪frame i, tubeAxisMidpoint U +
          (t - (2 : Real)⁻¹) • U.axis.direction⟫_ℝ -
          ⟪frame i, tubeAxisMidpoint T⟫_ℝ =
        ⟪frame i, tubeAxisMidpoint U - tubeAxisMidpoint T⟫_ℝ +
          (t - (2 : Real)⁻¹) * ⟪frame i, U.axis.direction⟫_ℝ := by
    rw [inner_add_right, inner_sub_right, inner_smul_right]
    ring
  rw [hsplit]
  calc
    |⟪frame i, tubeAxisMidpoint U - tubeAxisMidpoint T⟫_ℝ +
        (t - (2 : Real)⁻¹) * ⟪frame i, U.axis.direction⟫_ℝ| +
        (rho : Real) ≤
      |⟪frame i, tubeAxisMidpoint U - tubeAxisMidpoint T⟫_ℝ| +
        |(t - (2 : Real)⁻¹) * ⟪frame i, U.axis.direction⟫_ℝ| +
        (rho : Real) := by gcongr; exact abs_add_le _ _
    _ ≤ |⟪frame i, tubeAxisMidpoint U - tubeAxisMidpoint T⟫_ℝ| +
        (2 : Real)⁻¹ * |⟪frame i, U.axis.direction⟫_ℝ| +
        (rho : Real) := by
      gcongr
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right htcenter (abs_nonneg _)
    _ = (rho : Real) +
          |⟪frame i, tubeAxisMidpoint U - tubeAxisMidpoint T⟫_ℝ| +
          (2 : Real)⁻¹ * |⟪frame i, U.axis.direction⟫_ℝ| := by ring
    _ ≤ ((paperElongatedSides rho i : NNReal) : Real) / 2 := hbudget i

#print axioms carrier_subset_paperElongatedBody_of_axisCoordinateBudget
#print axioms tubeAxisPoint_eq_midpoint_add
#print axioms carrier_subset_paperElongatedBody_of_midpointDirectionBudget

end
end Family8FiniteRandomRigidMotionPaperElongatedCoordinateContainmentV1
