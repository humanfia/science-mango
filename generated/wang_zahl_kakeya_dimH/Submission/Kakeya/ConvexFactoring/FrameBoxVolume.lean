import Submission.Kakeya.ConvexGeometry.BoxDimensions

open scoped ENNReal NNReal Pointwise

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya
open MeasureTheory

noncomputable section

/-- A frame box is Borel measurable. -/
theorem FrameBox.measurableSet_carrier (B : FrameBox) :
    MeasurableSet B.carrier :=
  B.isCompact_carrier.measurableSet

/-- The convex body underlying a frame box is Borel measurable. -/
theorem FrameBox.measurableSet_body (B : FrameBox) :
    MeasurableSet (B.body : Set Space) := by
  rw [B.coe_body]
  exact B.measurableSet_carrier

/-- The determinant of the edge vectors in their defining orthonormal frame. -/
private theorem FrameBox.det_edge (B : FrameBox) :
    B.frame.toBasis.det B.edge = ∏ i, (B.side i : ℝ) := by
  change B.frame.toBasis.det (fun i => (B.side i : ℝ) • B.frame i) = _
  rw [AlternatingMap.map_smul_univ]
  rw [← B.frame.coe_toBasis]
  rw [B.frame.toBasis.det_self]
  simp

/-- Exact volume of a frame box; `side` stores full side lengths. -/
theorem FrameBox.volume_carrier (B : FrameBox) :
    volume B.carrier = ∏ i, (B.side i : ℝ≥0∞) := by
  rw [FrameBox.carrier, Set.image_add_left, measure_preimage_add]
  rw [← B.frame.addHaar_eq_volume,
    Measure.addHaar_parallelepiped, B.det_edge]
  rw [abs_of_nonneg (Finset.prod_nonneg fun _ _ => NNReal.zero_le_coe)]
  rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => NNReal.zero_le_coe)]
  simp only [ENNReal.coe_nnreal_eq]

/-- Exact volume of the convex body underlying a frame box. -/
theorem FrameBox.volume_body (B : FrameBox) :
    volume (B.body : Set Space) = ∏ i, (B.side i : ℝ≥0∞) := by
  rw [B.coe_body]
  exact B.volume_carrier

/-- Rescaling all side lengths scales the volume by the cube of the factor. -/
theorem FrameBox.volume_rescale (r : ℝ≥0) (B : FrameBox) :
    volume (B.rescale r).carrier = (r : ℝ≥0∞) ^ 3 * volume B.carrier := by
  rw [(B.rescale r).volume_carrier, B.volume_carrier]
  simp only [FrameBox.rescale_side, ENNReal.coe_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- If every side length is positive, then the frame box has positive volume. -/
theorem FrameBox.volume_carrier_pos (B : FrameBox)
    (hside : ∀ i, 0 < B.side i) :
    0 < volume B.carrier := by
  rw [B.volume_carrier]
  rw [pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  exact fun i _ => ENNReal.coe_ne_zero.mpr (ne_of_gt (hside i))

/-- If every side length is positive, the underlying convex body has positive volume. -/
theorem FrameBox.volume_body_pos (B : FrameBox)
    (hside : ∀ i, 0 < B.side i) :
    0 < volume (B.body : Set Space) := by
  rw [B.volume_body]
  rw [pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  exact fun i _ => ENNReal.coe_ne_zero.mpr (ne_of_gt (hside i))

end

end Submission.Kakeya.ConvexGeometry
