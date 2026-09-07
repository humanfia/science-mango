import Family8Grounding.Family8SelectedOccurrenceMaxWitnessCommonScaleV1
import Family8Grounding.Family8SelectedParentPlankHalfPostKatzTaoV3
import Family8Grounding.Family8StickyParentHullVolumeBoundV1
import Submission.Kakeya.ConvexFactoring.BoxDimensionsMeasure
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ClosedBallFourCommonScaleUnitPlankNoGoV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family6AffineConvexVolumeCoreV1
open Family8SelectedOccurrenceMaxWitnessCommonScaleV1
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentPlankHalfPostKatzTaoV3
open Family8StickyParentHullVolumeBoundV1

noncomputable section

/-!
# The radius-four ambient is not a unit plank after common scaling

The common-witness scaling is designed to normalize an individual fine
tube.  At `delta = 1/2` its factor is exactly `1/2`, so applying it to the
radius-four global containment ball leaves a radius-two ball.  Its volume is
strictly larger than one, whereas every certified `1 x 1 x 1` plank has
volume at most one.  Thus the global containment ambient cannot itself
supply the unit-plank certificate required by the common-witness endpoint.
-/

/-- At the largest allowed fine radius, the common scale is one half. -/
theorem maxWitnessCommonScale_half :
    maxWitnessCommonScale (2 : NNReal)⁻¹ = (2 : NNReal)⁻¹ := by
  norm_num [maxWitnessCommonScale]

/-- The corresponding common affine equivalence is literal half dilation. -/
theorem maxWitnessCommonScaleEquiv_half :
    maxWitnessCommonScaleEquiv (2 : NNReal)⁻¹ =
      scalarDilationAffineEquiv (2 : NNReal)⁻¹ (by norm_num) := by
  unfold maxWitnessCommonScaleEquiv
  congr 1
  exact maxWitnessCommonScale_half

/-- Half dilation reduces the radius-four ambient volume by exactly eight. -/
theorem volume_commonScale_closedBallFour_half :
    volume
        (affineImageConvexBody
          (maxWitnessCommonScaleEquiv (2 : NNReal)⁻¹)
          closedBallFourBody : Set Space) =
      (1 / 8 : ENNReal) * volume (closedBallFourBody : Set Space) := by
  rw [maxWitnessCommonScaleEquiv_half, volume_affineImageConvexBody,
    halfScalarDilationAffineJacobian]

/-- The half-scaled radius-four ambient still has volume strictly above one. -/
theorem one_lt_volume_commonScale_closedBallFour_half :
    1 < volume
      (affineImageConvexBody
        (maxWitnessCommonScaleEquiv (2 : NNReal)⁻¹)
        closedBallFourBody : Set Space) := by
  rw [volume_commonScale_closedBallFour_half, coe_closedBallFourBody,
    EuclideanSpace.volume_closedBall_fin_three]
  rw [← mul_assoc]
  norm_num
  have hcoeff : (8 : ENNReal)⁻¹ * 64 = 8 := by
    calc
      (8 : ENNReal)⁻¹ * 64 = 8⁻¹ * (8 * 8) := by norm_num
      _ = (8⁻¹ * 8) * 8 := by rw [mul_assoc]
      _ = 1 * 8 := by rw [ENNReal.inv_mul_cancel] <;> norm_num
      _ = 8 := by norm_num
  rw [hcoeff]
  have hpi : 1 < ENNReal.ofReal (Real.pi * 4 / 3) := by
    rw [ENNReal.one_lt_ofReal]
    nlinarith [Real.pi_gt_three]
  calc
    1 < ENNReal.ofReal (Real.pi * 4 / 3) := hpi
    _ = 1 * ENNReal.ofReal (Real.pi * 4 / 3) := by rw [one_mul]
    _ ≤ 8 * ENNReal.ofReal (Real.pi * 4 / 3) := by gcongr; norm_num

/-- Concrete obstruction: the globally containing radius-four ball cannot
become a certified unit plank under common scaling, regardless of the
comparability constant. -/
theorem no_unitPlank_commonScale_closedBallFour_at_half (C : NNReal) :
    ¬ IsPlank C 1 1
      (affineImageConvexBody
        (maxWitnessCommonScaleEquiv (2 : NNReal)⁻¹)
        closedBallFourBody) := by
  intro hplank
  have hupper :
      volume
          (affineImageConvexBody
            (maxWitnessCommonScaleEquiv (2 : NNReal)⁻¹)
            closedBallFourBody : Set Space) ≤ 1 := by
    simpa using hplank.volume_upper_bound
  exact (not_lt_of_ge hupper) one_lt_volume_commonScale_closedBallFour_half

#print axioms maxWitnessCommonScale_half
#print axioms maxWitnessCommonScaleEquiv_half
#print axioms volume_commonScale_closedBallFour_half
#print axioms one_lt_volume_commonScale_closedBallFour_half
#print axioms no_unitPlank_commonScale_closedBallFour_at_half

end
end Family8ClosedBallFourCommonScaleUnitPlankNoGoV1
