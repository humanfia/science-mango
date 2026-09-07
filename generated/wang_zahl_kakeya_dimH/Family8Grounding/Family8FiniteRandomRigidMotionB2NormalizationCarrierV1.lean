import Family8Grounding.Family8FiniteRandomRigidMotionB2NormalizationCoreV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionB2NormalizationCarrierV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1

noncomputable section

/-!
# Carrier transport for the radius-two normalization

The eighth-dilated short axis sits in the centered unit-axis extension.  The
same dilation sends the entire source `delta`-tube into the resulting
`delta/8` project tube.
-/

/-- The eighth-dilated source axis is contained in the centered unit-axis
extension. -/
theorem image_eighthDilation_axis_subset_normalizedAxis
    {delta : NNReal} (T : Tube delta) :
    eighthDilationPoint '' T.axis.carrier ⊆
      (eighthNormalizedAxis T).carrier := by
  rintro x ⟨y, hy, rfl⟩
  rw [UnitSegment.carrier_eq_image] at hy
  obtain ⟨t, ht, rfl⟩ := hy
  let u : Real := 7 / 16 + t / 8
  have hu : u ∈ Set.Icc (0 : Real) 1 := by
    constructor <;> dsimp only [u] <;> linarith [ht.1, ht.2]
  have heq :
      eighthDilationPoint ((fun t : Real => T.axis.base + t • T.axis.direction) t) =
        (eighthNormalizedAxis T).base +
          u • (eighthNormalizedAxis T).direction := by
    simp only [eighthNormalizedAxis_base,
      eighthNormalizedAxis_direction, eighthDilationPoint,
      tubeAxisMidpoint]
    dsimp only [u]
    module
  rw [heq]
  exact (eighthNormalizedAxis T).mem_carrier_of_mem_Icc hu

/-- Eighth-dilation sends the whole source tube into the genuine normalized
project tube. -/
theorem image_eighthDilation_tube_carrier_subset_normalizedTube
    {delta : NNReal} (T : Tube delta) :
    eighthDilationPoint '' T.carrier ⊆
      (eighthNormalizedTube T).carrier := by
  rintro x ⟨y, hy, rfl⟩
  have hdelta0 : 0 <= (delta : Real) := by positivity
  rw [Tube.carrier,
    T.axis.isCompact_carrier.cthickening_eq_biUnion_closedBall hdelta0] at hy
  simp only [Set.mem_iUnion, Metric.mem_closedBall] at hy
  obtain ⟨a, haAxis, hya⟩ := hy
  have haNormalized :
      eighthDilationPoint a ∈ (eighthNormalizedAxis T).carrier :=
    image_eighthDilation_axis_subset_normalizedAxis T ⟨a, haAxis, rfl⟩
  have hdist :
      dist (eighthDilationPoint y) (eighthDilationPoint a) <=
        ((delta / 8 : NNReal) : Real) := by
    rw [dist_eq_norm]
    have hsub :
        eighthDilationPoint y - eighthDilationPoint a =
          (1 / 8 : Real) • (y - a) := by
      simp only [eighthDilationPoint]
      module
    rw [hsub, norm_smul, Real.norm_eq_abs]
    norm_num only [abs_of_nonneg (by norm_num : (0 : Real) <= 1 / 8)]
    have hya' : ‖y - a‖ <= (delta : Real) := by
      simpa only [dist_eq_norm] using hya
    push_cast
    nlinarith
  change eighthDilationPoint y ∈
    Metric.cthickening ((delta / 8 : NNReal) : Real)
      (eighthNormalizedAxis T).carrier
  exact Metric.closedBall_subset_cthickening haNormalized _ hdist

#print axioms image_eighthDilation_axis_subset_normalizedAxis
#print axioms image_eighthDilation_tube_carrier_subset_normalizedTube

end
end Family8FiniteRandomRigidMotionB2NormalizationCarrierV1
