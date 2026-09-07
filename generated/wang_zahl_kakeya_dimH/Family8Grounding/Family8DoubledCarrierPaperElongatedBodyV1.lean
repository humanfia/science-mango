import Family8Grounding.Family8Def212ConvexWolffAtEveryScaleV2
import Family8Grounding.Family8FiniteRandomRigidMotionPaperElongatedFrameTestV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set
open scoped NNReal InnerProductSpace

namespace Family8DoubledCarrierPaperElongatedBodyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionPaperElongatedFrameTestV1

noncomputable section

/-- The literal full two-fold carrier of a radius-`rho` tube lies in its
length-six elongated frame body. -/
theorem twoFoldTubeCarrier_subset_paperElongatedBody
    {rho : NNReal} (T : Tube rho)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (hframe : frame 2 = T.axis.direction) (hrho : rho ≤ 1) :
    twoFoldTubeCarrier T ⊆
      (paperElongatedBody T frame : Set Space) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyBox := T.carrier_subset_alignedFrameBox frame hframe hy
  rw [FrameBox.carrier_eq_centeredCoordinateWindow,
    Submission.Kakeya.ConvexGeometry.TransverseCoordinateOverlap.mem_centeredCoordinateWindow_iff]
      at hyBox
  rw [coe_paperElongatedBody,
    FrameBox.carrier_eq_centeredCoordinateWindow,
    Submission.Kakeya.ConvexGeometry.TransverseCoordinateOverlap.mem_centeredCoordinateWindow_iff]
  intro i
  have hi := hyBox i
  change
    |⟪frame i,
        tubeCenter T + (2 : Real) • (y - tubeCenter T)⟫_Real -
      ⟪frame i, tubeAxisMidpoint T⟫_Real| ≤
        ((paperElongatedSides rho i : NNReal) : Real) / 2
  have hcenter : tubeCenter T = tubeAxisMidpoint T := by
    simp only [tubeCenter, tubeAxisMidpoint]
    norm_num
  have hcoordinate :
      ⟪frame i, tubeCenter T + (2 : Real) • (y - tubeCenter T)⟫_Real -
          ⟪frame i, tubeAxisMidpoint T⟫_Real =
        2 * (⟪frame i, y⟫_Real -
          ⟪frame i, tubeAxisMidpoint T⟫_Real) := by
    rw [hcenter, inner_add_right, real_inner_smul_right, inner_sub_right]
    ring
  rw [hcoordinate, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
  fin_cases i
  · norm_num [Tube.alignedFrameBox, Tube.frameBoxSides,
      FrameBox.coordinateCenter, FrameBox.coordinateHalf,
      paperElongatedSides, tubeAxisMidpoint] at hi ⊢
    nlinarith [NNReal.zero_le_coe (q := rho)]
  · norm_num [Tube.alignedFrameBox, Tube.frameBoxSides,
      FrameBox.coordinateCenter, FrameBox.coordinateHalf,
      paperElongatedSides, tubeAxisMidpoint] at hi ⊢
    nlinarith [NNReal.zero_le_coe (q := rho)]
  · norm_num [Tube.alignedFrameBox, Tube.frameBoxSides,
      FrameBox.coordinateCenter, FrameBox.coordinateHalf,
      paperElongatedSides, tubeAxisMidpoint] at hi ⊢
    have hrhoReal : (rho : Real) ≤ 1 := by exact_mod_cast hrho
    nlinarith

#print axioms twoFoldTubeCarrier_subset_paperElongatedBody

end
end Family8DoubledCarrierPaperElongatedBodyV1
