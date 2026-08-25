import Submission.Kakeya.ConvexFactoring.TubeSpecificLocalGrowth

open Set MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

namespace FamilyStickyFrameBoxAxialThickeningV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.TransverseCoordinateOverlap

noncomputable section

/-!
# A two-short-axis window for a locally supported thickening

This is the geometric cap used by the faithful finite replacement of GWZ's
shared random motion.  If the packing centers lie both in a frame box and in
one motion ball `closedBall x rho`, their `mesh`-thickening lies in an oriented
coordinate window of full widths

`side 0 + 2*mesh`, `side 1 + 2*mesh`, `2*(rho + mesh)`.

Thus the long direction is cut at the motion scale.  In particular this does
not use the full widened frame-box volume, which would lose one factor of
`rho` in the Appendix Section 7 incidence budget.
-/

/-- Half-widths for the two widened box coordinates and the motion-truncated
axial coordinate. -/
def FrameBox.axialThickeningHalf
    (B : FrameBox) (rho mesh : NNReal) : Fin 3 -> NNReal :=
  ![B.coordinateHalf 0 + mesh, B.coordinateHalf 1 + mesh, rho + mesh]

/-- A set supported in both the frame box and a closed motion ball has a
thickening supported in the corresponding two-short-axis window. -/
theorem FrameBox.thickening_subset_axialCoordinateWindow
    (B : FrameBox) (A : Set Space) (x : Space) (rho mesh : NNReal)
    (hAbox : A ⊆ B.carrier)
    (hAball : A ⊆ Metric.closedBall x (rho : Real)) :
    Metric.thickening (mesh : Real) A ⊆
      centeredCoordinateWindow B.frame (B.axialBallIntersectionCenter x)
        (axialThickeningHalf B rho mesh) := by
  intro y hy
  rw [mem_centeredCoordinateWindow_iff]
  intro i
  fin_cases i
  · have hslab := B.thickening_subset_affineSlab A hAbox mesh 0 hy
    change |⟪B.frame 0, y⟫_ℝ - B.coordinateCenter 0| ≤
      ((B.coordinateHalf 0 + mesh : NNReal) : Real) at hslab
    change |⟪B.frame 0, y⟫_ℝ - B.coordinateCenter 0| ≤
      ((B.coordinateHalf 0 + mesh : NNReal) : Real)
    exact hslab
  · have hslab := B.thickening_subset_affineSlab A hAbox mesh 1 hy
    change |⟪B.frame 1, y⟫_ℝ - B.coordinateCenter 1| ≤
      ((B.coordinateHalf 1 + mesh : NNReal) : Real) at hslab
    change |⟪B.frame 1, y⟫_ℝ - B.coordinateCenter 1| ≤
      ((B.coordinateHalf 1 + mesh : NNReal) : Real)
    exact hslab
  · obtain ⟨z, hzA, hyz⟩ := Metric.mem_thickening_iff.mp hy
    have hzx : dist z x ≤ (rho : Real) :=
      Metric.mem_closedBall.mp (hAball hzA)
    have hyx : dist y x < (mesh : Real) + (rho : Real) :=
      (dist_triangle y z x).trans_lt (add_lt_add_of_lt_of_le hyz hzx)
    have hcoord :
        |⟪B.frame 2, y⟫_ℝ - ⟪B.frame 2, x⟫_ℝ| ≤ dist y x :=
      abs_inner_sub_inner_le_dist_of_norm_eq_one
        (B.frame 2) y x (B.frame.norm_eq_one 2)
    change
      |⟪B.frame 2, y⟫_ℝ - ⟪B.frame 2, x⟫_ℝ| ≤
        ((rho + mesh : NNReal) : Real)
    norm_num at hyx ⊢
    linarith

/-- Exact volume of the motion-truncated widened coordinate window. -/
theorem FrameBox.volume_axialThickeningCoordinateWindow
    (B : FrameBox) (x : Space) (rho mesh : NNReal) :
    volume (centeredCoordinateWindow B.frame
      (B.axialBallIntersectionCenter x)
      (axialThickeningHalf B rho mesh)) =
      ((B.side 0 : ENNReal) + 2 * (mesh : ENNReal)) *
        ((B.side 1 : ENNReal) + 2 * (mesh : ENNReal)) *
          (2 * ((rho : ENNReal) + (mesh : ENNReal))) := by
  rw [volume_centeredCoordinateWindow_orthonormalBasis,
    Fin.prod_univ_three]
  have hwidth0 :
      2 * (B.coordinateHalf 0 + mesh) = B.side 0 + 2 * mesh := by
    rw [FrameBox.coordinateHalf]
    ring
  have hwidth1 :
      2 * (B.coordinateHalf 1 + mesh) = B.side 1 + 2 * mesh := by
    rw [FrameBox.coordinateHalf]
    ring
  simp only [FrameBox.axialThickeningHalf]
  exact_mod_cast congrArg₂ (fun a b : NNReal => a * b * (2 * (rho + mesh)))
    hwidth0 hwidth1

/-- The local-support volume cap, retaining both short side lengths and
truncating the long direction at the motion radius. -/
theorem FrameBox.volume_thickening_le_axialCap
    (B : FrameBox) (A : Set Space) (x : Space) (rho mesh : NNReal)
    (hAbox : A ⊆ B.carrier)
    (hAball : A ⊆ Metric.closedBall x (rho : Real)) :
    volume (Metric.thickening (mesh : Real) A) ≤
      ((B.side 0 : ENNReal) + 2 * (mesh : ENNReal)) *
        ((B.side 1 : ENNReal) + 2 * (mesh : ENNReal)) *
          (2 * ((rho : ENNReal) + (mesh : ENNReal))) := by
  rw [← volume_axialThickeningCoordinateWindow B x rho mesh]
  exact measure_mono
    (thickening_subset_axialCoordinateWindow B A x rho mesh hAbox hAball)

#print axioms FrameBox.thickening_subset_axialCoordinateWindow
#print axioms FrameBox.volume_axialThickeningCoordinateWindow
#print axioms FrameBox.volume_thickening_le_axialCap

end


end FamilyStickyFrameBoxAxialThickeningV1
