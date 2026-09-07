import Family8Grounding.Family8SelectedOccurrenceMaxWitnessCommonScaleV1
import Family8Grounding.Family8StickyParentHullVolumeBoundV1
import Family8Grounding.Family8ThinPlankFiveParameterFrameBoxPackingV4
import Submission.Kakeya.ConvexFactoring.FrameBoxCoordinateWindowEquiv
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

namespace Family8ClosedBallFourBufferedCommonScaleUnitPlankV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.TransverseCoordinateOverlap
open Submission.Kakeya.ConvexFactoring
open Family6AffineConvexVolumeCoreV1
open Family8SelectedOccurrenceMaxWitnessCommonScaleV1
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8StickyParentHullVolumeBoundV1
open Family8ThinPlankFiveParameterFrameBoxPackingV4

noncomputable section

def bufferedCommonScaleEquiv (delta : NNReal) : Space ≃ᵃ[Real] Space :=
  (maxWitnessCommonScaleEquiv delta).trans
    (scalarDilationAffineEquiv (8 : NNReal)⁻¹ (by norm_num))

@[simp] theorem bufferedCommonScaleEquiv_apply
    (delta : NNReal) (x : Space) :
    bufferedCommonScaleEquiv delta x =
      (1 / 8 : Real) • ((maxWitnessCommonScale delta : Real) • x) := by
  change (((8 : NNReal)⁻¹ : NNReal) : Real) •
      ((maxWitnessCommonScale delta : Real) • x) = _
  norm_num

@[simp] theorem bufferedCommonScaleEquiv_symm_apply
    (delta : NNReal) (x : Space) :
    (bufferedCommonScaleEquiv delta).symm x =
      ((maxWitnessCommonScale delta : Real)⁻¹) • ((8 : Real) • x) := by
  change (maxWitnessCommonScaleEquiv delta).symm
      ((scalarDilationAffineEquiv (8 : NNReal)⁻¹ _).symm x) = _
  rw [scalarDilationAffineEquiv_symm_apply]
  norm_num
  rfl

def standardFrame : OrthonormalBasis (Fin 3) Real Space :=
  (stdOrthonormalBasis Real Space).reindex (finCongr (by simp [Space]))

def standardUnitFrameBox : FrameBox where
  center := 0
  frame := standardFrame
  side := plankSides 1 1

@[simp] theorem standardUnitFrameBox_side (i : Fin 3) :
    standardUnitFrameBox.side i = 1 := by
  fin_cases i <;> rfl

theorem maxWitnessCommonScale_le_one (delta : NNReal) :
    maxWitnessCommonScale delta ≤ 1 := by
  rw [maxWitnessCommonScale]
  exact (inv_le_one₀ (by positivity)).2 (by simp)

theorem maxWitnessCommonScale_inv_le_two
    {delta : NNReal} (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹) :
    (maxWitnessCommonScale delta)⁻¹ ≤ 2 := by
  rw [maxWitnessCommonScale, inv_inv]
  nlinarith

theorem bufferedCommonScale_closedBallFour_outer
    (delta : NNReal) :
    (affineImageConvexBody (bufferedCommonScaleEquiv delta)
      closedBallFourBody : Set Space) ⊆ standardUnitFrameBox.carrier := by
  rintro y ⟨x, hx, rfl⟩
  rw [FrameBox.carrier_eq_centeredCoordinateWindow,
    mem_centeredCoordinateWindow_iff]
  intro i
  have hxnorm : ‖x‖ ≤ 4 := by
    rw [coe_closedBallFourBody, Metric.mem_closedBall, dist_zero_right] at hx
    exact hx
  have hinner := abs_real_inner_le_norm
    (standardUnitFrameBox.frame i)
    (bufferedCommonScaleEquiv delta x)
  rw [standardUnitFrameBox.frame.norm_eq_one, one_mul] at hinner
  change
    |⟪standardUnitFrameBox.frame i, bufferedCommonScaleEquiv delta x⟫_Real -
      ⟪standardUnitFrameBox.frame i, standardUnitFrameBox.center⟫_Real| ≤
        ((standardUnitFrameBox.side i / 2 : NNReal) : Real)
  have hcenter : standardUnitFrameBox.center = 0 := rfl
  rw [hcenter, inner_zero_right, sub_zero, standardUnitFrameBox_side]
  norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
  calc
    |⟪standardUnitFrameBox.frame i, bufferedCommonScaleEquiv delta x⟫_Real| ≤
        ‖bufferedCommonScaleEquiv delta x‖ := hinner
    _ = (1 / 8 : Real) * (maxWitnessCommonScale delta : Real) * ‖x‖ := by
      rw [bufferedCommonScaleEquiv_apply, norm_smul, norm_smul,
        Real.norm_eq_abs, Real.norm_eq_abs]
      norm_num
      ring
    _ ≤ (1 / 8 : Real) * 1 * 4 := by
      gcongr
      exact_mod_cast maxWitnessCommonScale_le_one delta
    _ = (1 : Real) / 2 := by norm_num

theorem bufferedCommonScale_closedBallFour_inner
    {delta : NNReal} (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹) :
    ((standardUnitFrameBox.rescale (8 : NNReal)⁻¹).body : Set Space) ⊆
      (affineImageConvexBody (bufferedCommonScaleEquiv delta)
        closedBallFourBody : Set Space) := by
  intro y hy
  let x := (bufferedCommonScaleEquiv delta).symm y
  refine ⟨x, ?_, (bufferedCommonScaleEquiv delta).apply_symm_apply y⟩
  rw [coe_closedBallFourBody, Metric.mem_closedBall, dist_zero_right]
  have hynorm : ‖y‖ ≤ (3 : Real) / 16 := by
    have h := frameBox_dist_center_le_half_sum_side
      (standardUnitFrameBox.rescale (8 : NNReal)⁻¹) hy
    change dist y 0 ≤ _ at h
    rw [dist_zero_right] at h
    calc
      ‖y‖ ≤ ((∑ i, (standardUnitFrameBox.rescale (8 : NNReal)⁻¹).side i : NNReal) : Real) / 2 := h
      _ = (3 : Real) / 16 := by
        norm_num [standardUnitFrameBox_side, Fin.sum_univ_three, NNReal.coe_inv]
  have hsinv : ((maxWitnessCommonScale delta)⁻¹ : Real) ≤ 2 := by
    exact_mod_cast maxWitnessCommonScale_inv_le_two hdeltaHalf
  have hsinv0 : (0 : Real) ≤ ((maxWitnessCommonScale delta)⁻¹ : Real) := by
    positivity
  change ‖x‖ ≤ 4
  calc
    ‖x‖ = ((maxWitnessCommonScale delta)⁻¹ : Real) * 8 * ‖y‖ := by
      dsimp only [x]
      rw [bufferedCommonScaleEquiv_symm_apply, norm_smul, norm_smul,
        Real.norm_eq_abs, Real.norm_eq_abs]
      rw [abs_of_nonneg hsinv0]
      norm_num
      ring
    _ ≤ 2 * 8 * ((3 : Real) / 16) := by gcongr
    _ ≤ 4 := by norm_num

theorem bufferedCommonScale_closedBallFour_isPlank
    {delta : NNReal} (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹) :
    IsPlank 8 1 1
      (affineImageConvexBody (bufferedCommonScaleEquiv delta)
        closedBallFourBody) := by
  refine ⟨by norm_num, le_rfl, le_rfl, by
    refine ⟨by norm_num, standardUnitFrameBox, ?_, ?_, ?_⟩
    · funext i
      fin_cases i <;> rfl
    · exact bufferedCommonScale_closedBallFour_inner hdeltaHalf
    · exact bufferedCommonScale_closedBallFour_outer delta⟩

#print axioms bufferedCommonScale_closedBallFour_isPlank

end
end Family8ClosedBallFourBufferedCommonScaleUnitPlankV1
