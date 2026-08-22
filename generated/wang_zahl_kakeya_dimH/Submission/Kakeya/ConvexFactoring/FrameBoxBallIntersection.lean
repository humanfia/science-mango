import Submission.Kakeya.ConvexFactoring.FrameBoxCoordinateWindowEquiv
import Submission.Kakeya.ConvexFactoring.FrameBoxThickening

open scoped ENNReal NNReal Pointwise InnerProductSpace Matrix
open MeasureTheory Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya
open TransverseCoordinateOverlap

noncomputable section

/-!
# Ball intersections with thin frame boxes

This module supplies the local volume cap used in a covering-number proof for
induced shadings.  It is a direct coordinate argument, not an assumed
covering estimate.
-/

/-- Keep the frame-box center in the short coordinate and use the ball center
in the other two coordinates. -/
def FrameBox.ballIntersectionCenter (B : FrameBox) (x : Space) : Coord :=
  ![B.coordinateCenter 0, ⟪B.frame 1, x⟫_ℝ, ⟪B.frame 2, x⟫_ℝ]

/-- Half-widths of the coordinate window containing the local intersection. -/
def FrameBox.ballIntersectionHalf (B : FrameBox) (r : ℝ≥0) : Fin 3 → ℝ≥0 :=
  ![B.coordinateHalf 0, r, r]

/-- A frame box cut by a radius-`r` ball lies in a window of full widths
`side 0`, `2r`, and `2r`. -/
theorem FrameBox.carrier_inter_ball_subset_coordinateWindow
    (B : FrameBox) (x : Space) (r : ℝ≥0) :
    B.carrier ∩ Metric.ball x (r : ℝ) ⊆
      centeredCoordinateWindow B.frame (B.ballIntersectionCenter x)
        (B.ballIntersectionHalf r) := by
  intro y hy
  rw [mem_centeredCoordinateWindow_iff]
  intro i
  fin_cases i
  · simpa [FrameBox.ballIntersectionCenter, FrameBox.ballIntersectionHalf,
      FrameBox.coordinateCenter, FrameBox.coordinateHalf] using
      B.centeredCoordinate_abs_le_halfSide hy.1 0
  · change |⟪B.frame 1, y⟫_ℝ - ⟪B.frame 1, x⟫_ℝ| ≤ (r : ℝ)
    exact (abs_inner_sub_inner_le_dist_of_norm_eq_one
      (B.frame 1) y x (B.frame.norm_eq_one 1)).trans
        (Metric.mem_ball.mp hy.2).le
  · change |⟪B.frame 2, y⟫_ℝ - ⟪B.frame 2, x⟫_ℝ| ≤ (r : ℝ)
    exact (abs_inner_sub_inner_le_dist_of_norm_eq_one
      (B.frame 2) y x (B.frame.norm_eq_one 2)).trans
        (Metric.mem_ball.mp hy.2).le

/-- Exact volume of the enclosing local coordinate window. -/
theorem FrameBox.volume_ballIntersectionCoordinateWindow
    (B : FrameBox) (x : Space) (r : ℝ≥0) :
    volume (centeredCoordinateWindow B.frame (B.ballIntersectionCenter x)
      (B.ballIntersectionHalf r)) =
      (2 * (B.coordinateHalf 0 : ℝ≥0∞)) *
        (2 * (r : ℝ≥0∞)) * (2 * (r : ℝ≥0∞)) := by
  rw [volume_centeredCoordinateWindow_orthonormalBasis, Fin.prod_univ_three]
  simp [FrameBox.ballIntersectionHalf]

/-- Concrete local volume cap for the frame box itself. -/
theorem FrameBox.volume_carrier_inter_ball_le
    (B : FrameBox) (x : Space) (r : ℝ≥0) :
    volume (B.carrier ∩ Metric.ball x (r : ℝ)) ≤
      (2 * (B.coordinateHalf 0 : ℝ≥0∞)) *
        (2 * (r : ℝ≥0∞)) * (2 * (r : ℝ≥0∞)) := by
  rw [← B.volume_ballIntersectionCoordinateWindow x r]
  exact measure_mono (B.carrier_inter_ball_subset_coordinateWindow x r)

end
end Submission.Kakeya.ConvexGeometry
