import ChallengeDeps
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

open MeasureTheory
open scoped ENNReal NNReal

namespace FamilyStickyBallVolumeScalingThreeV1

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-!
# Exact radius scaling for balls in the ambient three-space

The shared-packing cover uses balls of radius `3 * mesh`, whereas disjointness
uses radius `mesh`.  Since the ambient `Space` is literally Euclidean
three-space, Mathlib's proved volume formula gives the exact factor `27`.
No generic-dimension or asymptotic-volume hypothesis is introduced.
-/

/-- Tripling the radius of an open ball in `Space` multiplies volume by
exactly `27`. -/
theorem volume_ball_three_mul (mesh : NNReal) :
    volume (Metric.ball (0 : Space) ((3 * mesh : NNReal) : Real)) =
      27 * volume (Metric.ball (0 : Space) (mesh : Real)) := by
  rw [EuclideanSpace.volume_ball_fin_three,
    EuclideanSpace.volume_ball_fin_three]
  simp only [ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul,
    ENNReal.coe_ofNat]
  ring

/-- The corresponding monotone form used by balance estimates. -/
theorem volume_ball_three_mul_le (mesh : NNReal) :
    volume (Metric.ball (0 : Space) ((3 * mesh : NNReal) : Real)) ≤
      27 * volume (Metric.ball (0 : Space) (mesh : Real)) := by
  rw [volume_ball_three_mul]

#print axioms volume_ball_three_mul
#print axioms volume_ball_three_mul_le

end


end FamilyStickyBallVolumeScalingThreeV1
