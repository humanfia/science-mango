import Family8Grounding.Family8ClosedBallFourBufferedCommonScaleUnitPlankV1
import Family8Grounding.Family8SelectedParentJohnPlankSideWidthBridgeV8
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

namespace Family8BufferedCommonScaleTubePlankV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffineConvexVolumeCoreV1
open Family8ClosedBallFourBufferedCommonScaleUnitPlankV1
open Family8SelectedOccurrenceMaxWitnessCommonScaleV1
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV8

noncomputable section

def bufferedCommonWidth (delta : NNReal) : NNReal :=
  (8 : NNReal)⁻¹ * maxWitnessCommonWidth delta

def bufferedCommonScaleTubeBody {delta : NNReal} (T : Tube delta) :
    ConvexBody Space :=
  affineImageConvexBody (bufferedCommonScaleEquiv delta) T.body

noncomputable def bufferedCommonScaleTubeCertificate
    {delta : NNReal} (T : Tube delta)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹) :
    BoxDimensionsCertificate 2
      (fun i => (8 : NNReal)⁻¹ *
        plankSides (maxWitnessCommonWidth delta)
          (maxWitnessCommonWidth delta) i)
      (bufferedCommonScaleTubeBody T) := by
  let cert0 := commonScaleTubeCertificate T hdeltaHalf
  let cert1 := scalarDilationBoxDimensionsCertificate cert0
    (8 : NNReal)⁻¹ (by norm_num)
  have hbody :
      affineImageConvexBody
          (scalarDilationAffineEquiv (8 : NNReal)⁻¹ (by norm_num))
          (commonScaleTubeBody T) =
        bufferedCommonScaleTubeBody T := by
    rw [commonScaleTubeBody, affineImageConvexBody_trans]
    rfl
  exact hbody ▸ cert1

theorem bufferedCommonScaleTube_sideWidthEnvelope (delta : NNReal) :
    SideWidthEnvelope
      (fun i => (8 : NNReal)⁻¹ *
        plankSides (maxWitnessCommonWidth delta)
          (maxWitnessCommonWidth delta) i)
      (plankSides (bufferedCommonWidth delta)
        (bufferedCommonWidth delta)) 8 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      simp [bufferedCommonWidth, plankSides]
  · intro i
    have hinv : (8 : NNReal)⁻¹ ≤ 1 :=
      (inv_le_one₀ (by norm_num)).2 (by norm_num)
    fin_cases i <;>
      simp [bufferedCommonWidth, plankSides] <;>
      exact mul_le_of_le_one_left (by positivity) hinv

theorem bufferedCommonWidth_pos
    {delta : NNReal} (hdelta : 0 < delta) :
    0 < bufferedCommonWidth delta := by
  exact mul_pos (by norm_num) (maxWitnessCommonWidth_pos hdelta)

theorem bufferedCommonWidth_le_one (delta : NNReal) :
    bufferedCommonWidth delta ≤ 1 := by
  calc
    bufferedCommonWidth delta ≤ maxWitnessCommonWidth delta := by
      rw [bufferedCommonWidth]
      exact mul_le_of_le_one_left (by positivity)
        ((inv_le_one₀ (by norm_num)).2 (by norm_num))
    _ ≤ 1 := maxWitnessCommonWidth_le_one delta

theorem bufferedCommonScaleTube_isPlank
    {delta : NNReal} (T : Tube delta) (hdelta : 0 < delta)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹) :
    IsPlank 16 (bufferedCommonWidth delta)
      (bufferedCommonWidth delta) (bufferedCommonScaleTubeBody T) := by
  have h := isPlank_of_boxCertificate_sideWidthEnvelope
    (bufferedCommonScaleTubeCertificate T hdeltaHalf)
    (bufferedCommonWidth_pos hdelta) le_rfl
    (bufferedCommonWidth_le_one delta)
    (bufferedCommonScaleTube_sideWidthEnvelope delta)
  norm_num at h ⊢
  exact h

#print axioms bufferedCommonScaleTubeCertificate
#print axioms bufferedCommonScaleTube_isPlank

end
end Family8BufferedCommonScaleTubePlankV1
