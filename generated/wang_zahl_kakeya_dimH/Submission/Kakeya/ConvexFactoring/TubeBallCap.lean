import Submission.Kakeya.ConvexFactoring.FrameBoxBallIntersection
import Submission.Kakeya.ConvexFactoring.TubeFrameBoxDimensions

/-!
# Local ball caps for thin tubes

An aligned orthonormal frame supplies two transverse coordinates of half-width
`δ`. Intersecting with a radius-`R` ball supplies an axial coordinate of
half-width `R`. The resulting explicit coordinate window has volume
`8 * δ^2 * R`. No positivity or small-radius assumption is used, so the
statements include `δ = 0` and `R = 0`. This is a finite-scale local cap
estimate, not an endpoint Kakeya estimate.
-/

open scoped ENNReal NNReal Pointwise InnerProductSpace Matrix
open MeasureTheory Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya
open TransverseCoordinateOverlap

noncomputable section

/-- Coordinate center of the local cap: the tube center in both transverse
coordinates and the ball center in the axial coordinate. -/
def Tube.ballCapCenter {δ : ℝ≥0} (T : Tube δ)
    (frame : OrthonormalBasis (Fin 3) ℝ Space) (x : Space) : Coord :=
  ![(T.alignedFrameBox frame).coordinateCenter 0,
    (T.alignedFrameBox frame).coordinateCenter 1,
    ⟪frame 2, x⟫_ℝ]

/-- The two transverse half-widths are `δ`; the axial half-width is `R`. -/
def Tube.ballCapHalf (δ R : ℝ≥0) : Fin 3 → ℝ≥0 :=
  ![δ, δ, R]

/-- Orthogonal coordinate window enclosing the local tube cap. -/
def Tube.ballCapWindow {δ : ℝ≥0} (T : Tube δ)
    (frame : OrthonormalBasis (Fin 3) ℝ Space) (x : Space) (R : ℝ≥0) :
    Set Space :=
  centeredCoordinateWindow frame (T.ballCapCenter frame x)
    (Tube.ballCapHalf δ R)

/-- In an axis-aligned frame, a tube cut by a radius-`R` ball lies in the
window with half-widths `δ`, `δ`, and `R`. -/
theorem Tube.carrier_inter_ball_subset_ballCapWindow
    {δ : ℝ≥0} (T : Tube δ)
    (frame : OrthonormalBasis (Fin 3) ℝ Space)
    (hframe : frame 2 = T.axis.direction) (x : Space) (R : ℝ≥0) :
    T.carrier ∩ Metric.ball x (R : ℝ) ⊆
      T.ballCapWindow frame x R := by
  intro y hy
  have hybox : y ∈ (T.alignedFrameBox frame).carrier :=
    T.carrier_subset_alignedFrameBox frame hframe hy.1
  rw [FrameBox.carrier_eq_centeredCoordinateWindow,
    mem_centeredCoordinateWindow_iff] at hybox
  rw [Tube.ballCapWindow, mem_centeredCoordinateWindow_iff]
  intro i
  fin_cases i
  · simpa [Tube.ballCapCenter, Tube.ballCapHalf,
      FrameBox.coordinateHalf, Tube.alignedFrameBox, Tube.frameBoxSides]
      using hybox (0 : Fin 3)
  · simpa [Tube.ballCapCenter, Tube.ballCapHalf,
      FrameBox.coordinateHalf, Tube.alignedFrameBox, Tube.frameBoxSides]
      using hybox (1 : Fin 3)
  · change |⟪frame 2, y⟫_ℝ - ⟪frame 2, x⟫_ℝ| ≤ (R : ℝ)
    exact (abs_inner_sub_inner_le_dist_of_norm_eq_one
      (frame 2) y x (frame.norm_eq_one 2)).trans
        (Metric.mem_ball.mp hy.2).le

/-- Exact volume of the orthogonal cap window. -/
theorem Tube.volume_ballCapWindow {δ : ℝ≥0} (T : Tube δ)
    (frame : OrthonormalBasis (Fin 3) ℝ Space) (x : Space) (R : ℝ≥0) :
    volume (T.ballCapWindow frame x R) =
      (2 * (δ : ℝ≥0∞)) * (2 * (δ : ℝ≥0∞)) * (2 * (R : ℝ≥0∞)) := by
  rw [Tube.ballCapWindow, volume_centeredCoordinateWindow_orthonormalBasis,
    Fin.prod_univ_three]
  simp [Tube.ballCapHalf]

/-- A thin tube has the local ball-cap estimate `8 * δ^2 * R`. -/
theorem Tube.volume_carrier_inter_ball_le_eight_mul_sq
    {δ : ℝ≥0} (T : Tube δ) (x : Space) (R : ℝ≥0) :
    volume (T.carrier ∩ Metric.ball x (R : ℝ)) ≤
      8 * (δ : ℝ≥0∞) ^ 2 * (R : ℝ≥0∞) := by
  obtain ⟨frame, hframe⟩ := T.exists_alignedFrame
  calc
    volume (T.carrier ∩ Metric.ball x (R : ℝ)) ≤
        volume (T.ballCapWindow frame x R) :=
      measure_mono (T.carrier_inter_ball_subset_ballCapWindow
        frame hframe x R)
    _ = (2 * (δ : ℝ≥0∞)) * (2 * (δ : ℝ≥0∞)) *
        (2 * (R : ℝ≥0∞)) := T.volume_ballCapWindow frame x R
    _ = 8 * (δ : ℝ≥0∞) ^ 2 * (R : ℝ≥0∞) := by ring

end

end Submission.Kakeya.ConvexGeometry
