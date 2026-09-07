import Family8Grounding.Family8SelectedParentJohnFrameNormalizationV9

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentJohnBoxAffineTransportV16

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.TransverseCoordinateOverlap
open Family8SelectedParentJohnFrameNormalizationV9

noncomputable section

def normalizedJohnBox {H : ConvexBody Space}
    (J : PositiveJohnFrame H) (r : NNReal) : FrameBox where
  center := 0
  frame := J.certificate.box.frame
  side := fun _ ↦ r

@[simp] theorem normalizedJohnBox_center
    {H : ConvexBody Space} (J : PositiveJohnFrame H) (r : NNReal) :
    (normalizedJohnBox J r).center = 0 := rfl

@[simp] theorem normalizedJohnBox_frame
    {H : ConvexBody Space} (J : PositiveJohnFrame H) (r : NNReal) :
    (normalizedJohnBox J r).frame = J.certificate.box.frame := rfl

@[simp] theorem normalizedJohnBox_side
    {H : ConvexBody Space} (J : PositiveJohnFrame H)
    (r : NNReal) (i : Fin 3) : (normalizedJohnBox J r).side i = r := rfl

theorem image_rescaledBox_subset_normalizedJohnBox
    {H : ConvexBody Space} (J : PositiveJohnFrame H) (r : NNReal) :
    J.affineEquiv '' (J.certificate.box.rescale r).carrier ⊆
      (normalizedJohnBox J r).carrier := by
  rintro y ⟨x, hx, rfl⟩
  rw [FrameBox.carrier_eq_centeredCoordinateWindow,
    mem_centeredCoordinateWindow_iff]
  intro i
  change |⟪J.certificate.box.frame i, J.affineEquiv x⟫_ℝ -
      ⟪J.certificate.box.frame i, (0 : Space)⟫_ℝ| ≤
        ((r / 2 : NNReal) : Real)
  rw [J.inner_affineEquiv_apply, inner_zero_right, sub_zero,
    abs_div, abs_of_pos (show (0 : Real) < (J.side i : Real) by
      exact_mod_cast (J.side_pos i))]
  apply (div_le_iff₀ (show (0 : Real) < (J.side i : Real) by
    exact_mod_cast (J.side_pos i))).2
  have hsource :=
    (J.certificate.box.rescale r).centeredCoordinate_abs_le_halfSide hx i
  simp only [FrameBox.rescale_frame, FrameBox.rescale_center,
    FrameBox.rescale_side] at hsource
  rw [J.certificate.side_eq] at hsource
  have hscale :
      ((r * J.side i : NNReal) : Real) / 2 =
        ((r / 2 : NNReal) : Real) * (J.side i : Real) := by
    norm_num [NNReal.coe_div, NNReal.coe_mul]
    ring
  exact hsource.trans_eq hscale

theorem normalizedJohnBox_subset_image_rescaledBox
    {H : ConvexBody Space} (J : PositiveJohnFrame H) (r : NNReal) :
    (normalizedJohnBox J r).carrier ⊆
      J.affineEquiv '' (J.certificate.box.rescale r).carrier := by
  intro y hy
  let x := J.affineEquiv.symm y
  refine ⟨x, ?_, J.affineEquiv.apply_symm_apply y⟩
  rw [FrameBox.carrier_eq_centeredCoordinateWindow,
    mem_centeredCoordinateWindow_iff]
  intro i
  simp only [FrameBox.rescale_frame, FrameBox.coordinateCenter,
    FrameBox.rescale_center, FrameBox.coordinateHalf,
    FrameBox.rescale_side]
  rw [J.certificate.side_eq]
  change |⟪J.certificate.box.frame i, x⟫_ℝ -
      ⟪J.certificate.box.frame i, J.certificate.box.center⟫_ℝ| ≤
        (((r * J.side i) / 2 : NNReal) : Real)
  have hcoord := J.inner_affineEquiv_apply x i
  rw [show J.affineEquiv x = y by
    exact J.affineEquiv.apply_symm_apply y] at hcoord
  have hsideNe : (J.side i : Real) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast (J.side_pos i))
  have hnum :
      ⟪J.certificate.box.frame i, x⟫_ℝ -
          ⟪J.certificate.box.frame i, J.certificate.box.center⟫_ℝ =
        ⟪J.certificate.box.frame i, y⟫_ℝ * (J.side i : Real) := by
    exact ((eq_div_iff hsideNe).mp hcoord).symm
  rw [hnum, abs_mul, abs_of_pos (show (0 : Real) < (J.side i : Real) by
    exact_mod_cast (J.side_pos i))]
  have htarget :=
    (normalizedJohnBox J r).centeredCoordinate_abs_le_halfSide hy i
  simp only [normalizedJohnBox_frame, normalizedJohnBox_center,
    normalizedJohnBox_side, inner_zero_right, sub_zero] at htarget
  have hmul := mul_le_mul_of_nonneg_right htarget
    (show (0 : Real) ≤ (J.side i : Real) by positivity)
  have hscale :
      (r : Real) / 2 * (J.side i : Real) =
        (((r * J.side i) / 2 : NNReal) : Real) := by
    norm_num [NNReal.coe_div, NNReal.coe_mul]
    ring
  exact hmul.trans_eq hscale

theorem image_rescaledBox_eq_normalizedJohnBox
    {H : ConvexBody Space} (J : PositiveJohnFrame H) (r : NNReal) :
    J.affineEquiv '' (J.certificate.box.rescale r).carrier =
      (normalizedJohnBox J r).carrier :=
  Set.Subset.antisymm (image_rescaledBox_subset_normalizedJohnBox J r)
    (normalizedJohnBox_subset_image_rescaledBox J r)

#print axioms normalizedJohnBox
#print axioms image_rescaledBox_subset_normalizedJohnBox
#print axioms normalizedJohnBox_subset_image_rescaledBox
#print axioms image_rescaledBox_eq_normalizedJohnBox

end
end Family8SelectedParentJohnBoxAffineTransportV16
