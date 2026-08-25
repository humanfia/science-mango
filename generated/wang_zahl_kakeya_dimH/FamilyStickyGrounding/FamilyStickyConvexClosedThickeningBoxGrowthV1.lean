import Submission.Kakeya.ConvexFactoring.BoxDimensionsMeasure
import Submission.Kakeya.ConvexFactoring.FrameBoxThickening

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace FamilyStickyConvexClosedThickeningBoxGrowthV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.TransverseCoordinateOverlap

noncomputable section

/-!
# Closed thickening growth from a certified frame box

The existing frame-box API bounds an *open* metric thickening.  Sticky
localization uses a closed thickening.  Compactness of a convex body makes
the infimum distance attained, so the same exact coordinate widths apply:
each full side grows by `2 * r`.
-/

/-- A closed thickening of a compact subset of a frame box lies in the
coordinate window obtained by adding `r` to every half-width. -/
theorem FrameBox.cthickening_subset_centeredCoordinateWindow
    (B : FrameBox) (A : Set Space) (hAcompact : IsCompact A)
    (hA : A ⊆ B.carrier) (r : NNReal) :
    Metric.cthickening (r : Real) A ⊆
      centeredCoordinateWindow B.frame B.coordinateCenter
        (B.widenedCoordinateHalf r) := by
  intro x hx
  rw [hAcompact.cthickening_eq_biUnion_closedBall
    (show (0 : Real) ≤ (r : Real) by positivity)] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨y, hyA, hxy⟩ := hx
  rw [mem_centeredCoordinateWindow_iff]
  intro i
  have hySlab := B.carrier_subset_affineSlab i (hA hyA)
  change |⟪B.frame i, y⟫_ℝ - B.coordinateCenter i| ≤
    (B.coordinateHalf i : Real) at hySlab
  have hxy' : dist x y ≤ (r : Real) := Metric.mem_closedBall.mp hxy
  change |⟪B.frame i, x⟫_ℝ - B.coordinateCenter i| ≤
    (B.widenedCoordinateHalf r i : Real)
  calc
    |⟪B.frame i, x⟫_ℝ - B.coordinateCenter i| =
        |(⟪B.frame i, x⟫_ℝ - ⟪B.frame i, y⟫_ℝ) +
          (⟪B.frame i, y⟫_ℝ - B.coordinateCenter i)| := by
      congr 1
      ring
    _ ≤ |⟪B.frame i, x⟫_ℝ - ⟪B.frame i, y⟫_ℝ| +
        |⟪B.frame i, y⟫_ℝ - B.coordinateCenter i| := abs_add_le _ _
    _ ≤ dist x y + (B.coordinateHalf i : Real) :=
      add_le_add
        (abs_inner_sub_inner_le_dist_of_norm_eq_one
          (B.frame i) x y (B.frame.norm_eq_one i)) hySlab
    _ ≤ (r : Real) + (B.coordinateHalf i : Real) :=
      add_le_add hxy' le_rfl
    _ = (B.widenedCoordinateHalf r i : Real) := by
      simp [FrameBox.widenedCoordinateHalf, add_comm]

/-- Exact widened-box upper bound for the closed thickening of a compact
subset. -/
theorem FrameBox.volume_cthickening_le_prod_side_add_two_mul
    (B : FrameBox) (A : Set Space) (hAcompact : IsCompact A)
    (hA : A ⊆ B.carrier) (r : NNReal) :
    volume (Metric.cthickening (r : Real) A) ≤
      ∏ i, ((B.side i : ENNReal) + 2 * (r : ENNReal)) := by
  rw [← B.volume_widenedCoordinateWindow r]
  exact measure_mono
    (FamilyStickyConvexClosedThickeningBoxGrowthV1.FrameBox.cthickening_subset_centeredCoordinateWindow B A hAcompact hA r)

/-- The computable ratio of the widened outer-box volume to the certified
inner-box volume. -/
def certifiedClosedThickeningLoss
    (C : NNReal) (side : Fin 3 → NNReal) (r : NNReal) : ENNReal :=
  (∏ i, ((side i : ENNReal) + 2 * (r : ENNReal))) /
    (((C⁻¹ : NNReal) : ENNReal) ^ 3 * ∏ i, (side i : ENNReal))

/-- A positive side certificate makes the certified inner-box volume
strictly positive. -/
theorem certifiedInnerBoxVolume_pos
    {C : NNReal} {side : Fin 3 → NNReal}
    (hC : 1 ≤ C) (hside : ∀ i, 0 < side i) :
    0 < (((C⁻¹ : NNReal) : ENNReal) ^ 3 *
      ∏ i, (side i : ENNReal)) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hCinv : 0 < C⁻¹ := inv_pos.mpr hCpos
  apply ENNReal.mul_pos
  · exact pow_ne_zero 3 (ENNReal.coe_ne_zero.mpr hCinv.ne')
  · exact Finset.prod_ne_zero_iff.mpr fun i hi =>
      ENNReal.coe_ne_zero.mpr (hside i).ne'

/-- A positive-side `HasBoxDimensions` certificate proves closed-thickening
volume growth with the literal outer/inner box ratio.  No volume-ratio
inequality is supplied as an assumption. -/
theorem HasBoxDimensions.volume_closedThickening_le_certifiedLoss
    {C : NNReal} {side : Fin 3 → NNReal} {K : ConvexBody Space}
    (h : HasBoxDimensions C side K) (hside : ∀ i, 0 < side i)
    (r : NNReal) :
    volume (Metric.cthickening (r : Real) (K : Set Space)) ≤
      certifiedClosedThickeningLoss C side r * volume (K : Set Space) := by
  rcases h with ⟨hC, B, hBside, hinner, houter⟩
  have hlower :
      (((C⁻¹ : NNReal) : ENNReal) ^ 3 * ∏ i, (side i : ENNReal)) ≤
        volume (K : Set Space) := by
    exact (show HasBoxDimensions C side K from
      ⟨hC, B, hBside, hinner, houter⟩).volume_lower_bound
  have hdenPos :
      0 < (((C⁻¹ : NNReal) : ENNReal) ^ 3 *
        ∏ i, (side i : ENNReal)) :=
    certifiedInnerBoxVolume_pos hC hside
  have hdenTop :
      (((C⁻¹ : NNReal) : ENNReal) ^ 3 *
        ∏ i, (side i : ENNReal)) < ∞ := by
    apply ENNReal.mul_lt_top
    · exact ENNReal.pow_lt_top ENNReal.coe_lt_top
    · exact ENNReal.prod_lt_top fun i hi => ENNReal.coe_lt_top
  calc
    volume (Metric.cthickening (r : Real) (K : Set Space)) ≤
        ∏ i, ((side i : ENNReal) + 2 * (r : ENNReal)) := by
      simpa [hBside] using
        FamilyStickyConvexClosedThickeningBoxGrowthV1.FrameBox.volume_cthickening_le_prod_side_add_two_mul
          B (K : Set Space) K.isCompact houter r
    _ = certifiedClosedThickeningLoss C side r *
        (((C⁻¹ : NNReal) : ENNReal) ^ 3 *
          ∏ i, (side i : ENNReal)) := by
      symm
      exact ENNReal.div_mul_cancel hdenPos.ne' hdenTop.ne
    _ ≤ certifiedClosedThickeningLoss C side r *
        volume (K : Set Space) := by
      gcongr

#print axioms FrameBox.cthickening_subset_centeredCoordinateWindow
#print axioms FrameBox.volume_cthickening_le_prod_side_add_two_mul
#print axioms certifiedInnerBoxVolume_pos
#print axioms HasBoxDimensions.volume_closedThickening_le_certifiedLoss

end
end FamilyStickyConvexClosedThickeningBoxGrowthV1
