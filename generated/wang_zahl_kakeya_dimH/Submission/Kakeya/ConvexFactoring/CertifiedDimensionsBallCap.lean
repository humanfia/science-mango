import Submission.Kakeya.ConvexFactoring.FrameBoxBallIntersection
import Submission.Kakeya.ConvexFactoring.CertifiedSlabOverlap
import Submission.Kakeya.ConvexGeometry.Shading

/-!
# Local ball caps for certified box dimensions

An outer frame-box certificate turns the coordinate-window cap for a frame
box into a local volume bound for the certified convex body and every subset
of that body.  For certified slabs, the short side is unfolded explicitly.
No local-volume or covering estimate is assumed.
-/

open scoped ENNReal NNReal Pointwise InnerProductSpace Matrix
open MeasureTheory Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-- The local ball intersection of a box-certified convex body is controlled
by its first side length and the two transverse ball diameters. -/
theorem BoxDimensionsCertificate.volume_inter_ball_le
    {C : ℝ≥0} {side : Fin 3 → ℝ≥0} {K : ConvexBody Space}
    (cert : BoxDimensionsCertificate C side K)
    (x : Space) (r : ℝ≥0) :
    volume ((K : Set Space) ∩ Metric.ball x (r : ℝ)) ≤
      (side 0 : ℝ≥0∞) * (2 * (r : ℝ≥0∞)) ^ 2 := by
  have hsubset :
      (K : Set Space) ∩ Metric.ball x (r : ℝ) ⊆
        cert.box.carrier ∩ Metric.ball x (r : ℝ) := by
    intro y hy
    constructor
    · change y ∈ cert.box.body
      exact cert.outer_le hy.1
    · exact hy.2
  have hbox := cert.box.volume_carrier_inter_ball_le x r
  have hfull :
      (2 : ℝ≥0∞) * (((side 0 / 2 : ℝ≥0)) : ℝ≥0∞) =
        (side 0 : ℝ≥0∞) := by
    rw [ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0)]
    exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  calc
    volume ((K : Set Space) ∩ Metric.ball x (r : ℝ)) ≤
        volume (cert.box.carrier ∩ Metric.ball x (r : ℝ)) :=
      measure_mono hsubset
    _ ≤ (2 * (cert.box.coordinateHalf 0 : ℝ≥0∞)) *
        (2 * (r : ℝ≥0∞)) * (2 * (r : ℝ≥0∞)) := hbox
    _ = (side 0 : ℝ≥0∞) * (2 * (r : ℝ≥0∞)) ^ 2 := by
      rw [FrameBox.coordinateHalf, cert.side_eq, hfull]
      simp [pow_two, mul_assoc]

/-- The same local cap holds for every set contained in the certified body. -/
theorem BoxDimensionsCertificate.volume_set_inter_ball_le
    {C : ℝ≥0} {side : Fin 3 → ℝ≥0} {K : ConvexBody Space}
    (cert : BoxDimensionsCertificate C side K)
    (A : Set Space) (hA : A ⊆ (K : Set Space))
    (x : Space) (r : ℝ≥0) :
    volume (A ∩ Metric.ball x (r : ℝ)) ≤
      (side 0 : ℝ≥0∞) * (2 * (r : ℝ≥0∞)) ^ 2 := by
  calc
    volume (A ∩ Metric.ball x (r : ℝ)) ≤
        volume ((K : Set Space) ∩ Metric.ball x (r : ℝ)) :=
      measure_mono (inter_subset_inter hA Subset.rfl)
    _ ≤ (side 0 : ℝ≥0∞) * (2 * (r : ℝ≥0∞)) ^ 2 :=
      cert.volume_inter_ball_le x r

/-- A shading carrier inherits the local cap from the certified body. -/
theorem BoxDimensionsCertificate.volume_shading_carrier_inter_ball_le
    {ι : Type*} {F : ConvexFamily ι} (Y : Shading F) (i : ι)
    {C : ℝ≥0} {side : Fin 3 → ℝ≥0}
    (cert : BoxDimensionsCertificate C side (F i))
    (x : Space) (r : ℝ≥0) :
    volume (Y.carrier i ∩ Metric.ball x (r : ℝ)) ≤
      (side 0 : ℝ≥0∞) * (2 * (r : ℝ≥0∞)) ^ 2 :=
  cert.volume_set_inter_ball_le (Y.carrier i) (Y.carrier_subset i) x r

/-- A certified slab has the explicit local cap `θ * (2r)^2`. -/
theorem SlabDimensionsCertificate.volume_inter_ball_le
    {C θ : ℝ≥0} {K : ConvexBody Space}
    (cert : SlabDimensionsCertificate C θ K)
    (x : Space) (r : ℝ≥0) :
    volume ((K : Set Space) ∩ Metric.ball x (r : ℝ)) ≤
      (θ : ℝ≥0∞) * (2 * (r : ℝ≥0∞)) ^ 2 := by
  simpa [slabSides] using
    cert.toBoxDimensionsCertificate.volume_inter_ball_le x r

/-- Every subset of a certified slab satisfies the same explicit cap. -/
theorem SlabDimensionsCertificate.volume_set_inter_ball_le
    {C θ : ℝ≥0} {K : ConvexBody Space}
    (cert : SlabDimensionsCertificate C θ K)
    (A : Set Space) (hA : A ⊆ (K : Set Space))
    (x : Space) (r : ℝ≥0) :
    volume (A ∩ Metric.ball x (r : ℝ)) ≤
      (θ : ℝ≥0∞) * (2 * (r : ℝ≥0∞)) ^ 2 := by
  simpa [slabSides] using
    cert.toBoxDimensionsCertificate.volume_set_inter_ball_le A hA x r

/-- In particular, every shading carrier inside a certified slab obeys the
same local cap, in the form needed by a covering-number growth argument. -/
theorem SlabDimensionsCertificate.volume_shading_carrier_inter_ball_le
    {ι : Type*} {F : ConvexFamily ι} (Y : Shading F) (i : ι)
    {C θ : ℝ≥0} (cert : SlabDimensionsCertificate C θ (F i))
    (x : Space) (r : ℝ≥0) :
    volume (Y.carrier i ∩ Metric.ball x (r : ℝ)) ≤
      (θ : ℝ≥0∞) * (2 * (r : ℝ≥0∞)) ^ 2 :=
  cert.volume_set_inter_ball_le (Y.carrier i) (Y.carrier_subset i) x r

end

end Submission.Kakeya.ConvexGeometry
