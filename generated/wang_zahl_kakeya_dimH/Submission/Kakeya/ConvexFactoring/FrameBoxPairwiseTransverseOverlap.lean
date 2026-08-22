import Submission.Kakeya.ConvexFactoring.FrameBoxCoordinateWindow
import Submission.Kakeya.ConvexFactoring.DeterminantAngleBridge

/-!
# Pairwise transverse overlap for frame boxes

This module projects a frame box onto an arbitrary direction and packages the
resulting half-width as an `NNReal`.  One chosen coordinate direction from
each of two boxes, together with a common longitudinal direction, then gives
a genuine three-slab container for their carrier intersection.  The exact
coordinate-window Jacobian formula yields a determinant overlap estimate, and
the determinant-angle bridge rewrites it as a reciprocal-sine estimate under
the corresponding unit and orthogonality hypotheses.
-/

open scoped ENNReal NNReal Pointwise InnerProductSpace
open MeasureTheory

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya
open TransverseCoordinateOverlap

noncomputable section

/-- The half-width of a frame box after projection onto an arbitrary
direction. -/
def FrameBox.directionalHalf (B : FrameBox) (e : Space) : ℝ≥0 :=
  ∑ k, ⟨|⟪e, B.frame k⟫_ℝ|, abs_nonneg _⟩ * (B.side k / 2)

/-- A frame box is contained in the affine slab obtained by projecting all
three of its half-edges onto an arbitrary direction. -/
theorem FrameBox.carrier_subset_directionalAffineSlab
    (B : FrameBox) (e : Space) :
    B.carrier ⊆ affineSlab e ⟪e, B.center⟫_ℝ (B.directionalHalf e) := by
  intro x hx
  change |⟪e, x⟫_ℝ - ⟪e, B.center⟫_ℝ| ≤ (B.directionalHalf e : ℝ)
  have hexpand :
      ⟪e, x⟫_ℝ - ⟪e, B.center⟫_ℝ =
        ∑ k, (⟪B.frame k, x⟫_ℝ - ⟪B.frame k, B.center⟫_ℝ) *
          ⟪e, B.frame k⟫_ℝ := by
    rw [← inner_sub_right]
    conv_lhs => rw [← B.frame.sum_repr' (x - B.center)]
    simp only [inner_sum, real_inner_smul_right, inner_sub_right]
  rw [hexpand]
  calc
    |∑ k, (⟪B.frame k, x⟫_ℝ - ⟪B.frame k, B.center⟫_ℝ) *
        ⟪e, B.frame k⟫_ℝ| ≤
        ∑ k, |(⟪B.frame k, x⟫_ℝ - ⟪B.frame k, B.center⟫_ℝ) *
          ⟪e, B.frame k⟫_ℝ| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |⟪B.frame k, x⟫_ℝ - ⟪B.frame k, B.center⟫_ℝ| *
        |⟪e, B.frame k⟫_ℝ| := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [abs_mul]
    _ ≤ ∑ k, ((B.side k : ℝ) / 2) * |⟪e, B.frame k⟫_ℝ| := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_right
        (B.centeredCoordinate_abs_le_halfSide hx k) (abs_nonneg _)
    _ = (B.directionalHalf e : ℝ) := by
      rw [FrameBox.directionalHalf, NNReal.coe_sum]
      apply Finset.sum_congr rfl
      intro k hk
      change (B.side k : ℝ) / 2 * |⟪e, B.frame k⟫_ℝ| =
        |⟪e, B.frame k⟫_ℝ| * ((B.side k : ℝ) / 2)
      ring

/-- The intersection of two frame boxes is contained in the three slabs
supplied by one arbitrary longitudinal direction and one chosen frame
coordinate from each box. -/
theorem FrameBox.inter_carrier_subset_threeTransverseSlabs
    (B₀ B₁ : FrameBox) (i j : Fin 3) (e : Space) :
    B₀.carrier ∩ B₁.carrier ⊆
      affineSlab e ⟪e, B₀.center⟫_ℝ (B₀.directionalHalf e) ∩
      affineSlab (B₀.frame i) (B₀.coordinateCenter i) (B₀.coordinateHalf i) ∩
      affineSlab (B₁.frame j) (B₁.coordinateCenter j) (B₁.coordinateHalf j) := by
  intro x hx
  exact ⟨⟨B₀.carrier_subset_directionalAffineSlab e hx.1,
    B₀.carrier_subset_affineSlab i hx.1⟩,
    B₁.carrier_subset_affineSlab j hx.2⟩

/-- A determinant-form transverse overlap bound for two frame boxes.  The
estimate follows from carrier containment and the exact Jacobian formula; no
overlap estimate is assumed. -/
theorem FrameBox.volume_inter_carrier_le_det
    (B₀ B₁ : FrameBox) (i j : Fin 3) (e : Space)
    (hdet : LinearMap.det
      (innerCoordinateMap ![e, B₀.frame i, B₁.frame j]) ≠ 0) :
    volume (B₀.carrier ∩ B₁.carrier) ≤
      ENNReal.ofReal |(LinearMap.det
        (innerCoordinateMap ![e, B₀.frame i, B₁.frame j]))⁻¹| *
      (2 * (B₀.directionalHalf e : ℝ≥0∞)) *
      (2 * (B₀.coordinateHalf i : ℝ≥0∞)) *
      (2 * (B₁.coordinateHalf j : ℝ≥0∞)) := by
  calc
    volume (B₀.carrier ∩ B₁.carrier) ≤
        volume
          (affineSlab e ⟪e, B₀.center⟫_ℝ (B₀.directionalHalf e) ∩
          affineSlab (B₀.frame i) (B₀.coordinateCenter i) (B₀.coordinateHalf i) ∩
          affineSlab (B₁.frame j) (B₁.coordinateCenter j)
            (B₁.coordinateHalf j)) :=
      measure_mono (B₀.inter_carrier_subset_threeTransverseSlabs B₁ i j e)
    _ = ENNReal.ofReal |(LinearMap.det
          (innerCoordinateMap ![e, B₀.frame i, B₁.frame j]))⁻¹| *
        (2 * (B₀.directionalHalf e : ℝ≥0∞)) *
        (2 * (B₀.coordinateHalf i : ℝ≥0∞)) *
        (2 * (B₁.coordinateHalf j : ℝ≥0∞)) :=
      volume_twoSlabs_with_longitudinalCut
        e (B₀.frame i) (B₁.frame j)
        ⟪e, B₀.center⟫_ℝ (B₀.coordinateCenter i) (B₁.coordinateCenter j)
        (B₀.directionalHalf e) (B₀.coordinateHalf i) (B₁.coordinateHalf j) hdet

/-- For a unit longitudinal vector perpendicular to both chosen frame
directions, the determinant factor in the overlap bound is exactly the
reciprocal sine of their angle. -/
theorem FrameBox.volume_inter_carrier_le_sin_angle
    (B₀ B₁ : FrameBox) (i j : Fin 3) (e : Space)
    (he : ‖e‖ = 1)
    (heu : ⟪e, B₀.frame i⟫_ℝ = 0)
    (hev : ⟪e, B₁.frame j⟫_ℝ = 0)
    (hangle : 0 < Real.sin
      (InnerProductGeometry.angle (B₀.frame i) (B₁.frame j))) :
    volume (B₀.carrier ∩ B₁.carrier) ≤
      ENNReal.ofReal
        ((Real.sin (InnerProductGeometry.angle
          (B₀.frame i) (B₁.frame j)))⁻¹) *
      (2 * (B₀.directionalHalf e : ℝ≥0∞)) *
      (2 * (B₀.coordinateHalf i : ℝ≥0∞)) *
      (2 * (B₁.coordinateHalf j : ℝ≥0∞)) := by
  have hu : ‖B₀.frame i‖ = 1 := B₀.frame.norm_eq_one i
  have hv : ‖B₁.frame j‖ = 1 := B₁.frame.norm_eq_one j
  have hdet : LinearMap.det
      (innerCoordinateMap ![e, B₀.frame i, B₁.frame j]) ≠ 0 :=
    det_innerCoordinateMap_ne_zero_of_sin_angle_pos
      e (B₀.frame i) (B₁.frame j) he hu hv heu hev hangle
  calc
    volume (B₀.carrier ∩ B₁.carrier) ≤
        ENNReal.ofReal |(LinearMap.det
          (innerCoordinateMap ![e, B₀.frame i, B₁.frame j]))⁻¹| *
        (2 * (B₀.directionalHalf e : ℝ≥0∞)) *
        (2 * (B₀.coordinateHalf i : ℝ≥0∞)) *
        (2 * (B₁.coordinateHalf j : ℝ≥0∞)) :=
      B₀.volume_inter_carrier_le_det B₁ i j e hdet
    _ = ENNReal.ofReal
          ((Real.sin (InnerProductGeometry.angle
            (B₀.frame i) (B₁.frame j)))⁻¹) *
        (2 * (B₀.directionalHalf e : ℝ≥0∞)) *
        (2 * (B₀.coordinateHalf i : ℝ≥0∞)) *
        (2 * (B₁.coordinateHalf j : ℝ≥0∞)) := by
      rw [abs_inv, abs_det_innerCoordinateMap_eq_sin_angle
        e (B₀.frame i) (B₁.frame j) he hu hv heu hev]

end

end Submission.Kakeya.ConvexGeometry
