import Family8Grounding.Family8GeneralizedFrostmanMultiplicityV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionB2NormalizationCoreV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

noncomputable section

/-!
# Constant-scale normalization of tubes contained in `B(0,2)`

The random rotation-plus-translation construction naturally places moved
tubes in the radius-two ball, not the unit ball.  We dilate by `1/8`, keep
the dilated axis segment centered, and extend it to a genuine unit segment.
The resulting `delta/8` tube is honestly contained in the unit ball.
-/

/-- Midpoint of the parametrized unit axis. -/
def tubeAxisMidpoint {delta : NNReal} (T : Tube delta) : Space :=
  T.axis.base + (1 / 2 : Real) • T.axis.direction

/-- The ambient eighth-dilation used in the normalization. -/
def eighthDilationPoint (x : Space) : Space :=
  (1 / 8 : Real) • x

/-- Unit-axis extension centered at the eighth-dilated source midpoint. -/
def eighthNormalizedAxis {delta : NNReal} (T : Tube delta) : UnitSegment where
  base := eighthDilationPoint (tubeAxisMidpoint T) -
    (1 / 2 : Real) • T.axis.direction
  direction := T.axis.direction
  norm_direction := T.axis.norm_direction

/-- A genuine project tube at the rescaled radius. -/
def eighthNormalizedTube {delta : NNReal} (T : Tube delta) : Tube (delta / 8) where
  axis := eighthNormalizedAxis T

@[simp] theorem eighthNormalizedAxis_direction
    {delta : NNReal} (T : Tube delta) :
    (eighthNormalizedAxis T).direction = T.axis.direction := rfl

@[simp] theorem eighthNormalizedAxis_base
    {delta : NNReal} (T : Tube delta) :
    (eighthNormalizedAxis T).base =
      eighthDilationPoint (tubeAxisMidpoint T) -
        (1 / 2 : Real) • T.axis.direction := rfl

@[simp] theorem eighthNormalizedTube_axis
    {delta : NNReal} (T : Tube delta) :
    (eighthNormalizedTube T).axis = eighthNormalizedAxis T := rfl

/-- The source axis midpoint belongs to the source tube. -/
theorem tubeAxisMidpoint_mem_carrier
    {delta : NNReal} (T : Tube delta) :
    tubeAxisMidpoint T ∈ T.carrier := by
  apply T.axis_subset_carrier
  exact T.axis.mem_carrier_of_mem_Icc (by norm_num)

/-- Radius-two containment controls the source midpoint. -/
theorem norm_tubeAxisMidpoint_le_two_of_carrier_subset
    {delta : NNReal} (T : Tube delta)
    (hB2 : T.carrier ⊆ Metric.closedBall (0 : Space) 2) :
    ‖tubeAxisMidpoint T‖ <= 2 := by
  have hm := hB2 (tubeAxisMidpoint_mem_carrier T)
  simpa only [Metric.mem_closedBall, dist_zero_right] using hm

/-- The centered extended unit axis lies in the radius-`3/4` ball. -/
theorem eighthNormalizedAxis_carrier_subset_threeQuartersBall
    {delta : NNReal} (T : Tube delta)
    (hB2 : T.carrier ⊆ Metric.closedBall (0 : Space) 2) :
    (eighthNormalizedAxis T).carrier ⊆
      Metric.closedBall (0 : Space) (3 / 4 : Real) := by
  intro x hx
  rw [UnitSegment.carrier_eq_image] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  rw [Metric.mem_closedBall, dist_zero_right]
  have hmid := norm_tubeAxisMidpoint_le_two_of_carrier_subset T hB2
  have hcenter :
      ‖eighthDilationPoint (tubeAxisMidpoint T)‖ <= (1 / 4 : Real) := by
    calc
      ‖eighthDilationPoint (tubeAxisMidpoint T)‖ =
          (1 / 8 : Real) * ‖tubeAxisMidpoint T‖ := by
        simp [eighthDilationPoint, norm_smul]
      _ <= (1 / 8 : Real) * 2 := by gcongr
      _ = (1 / 4 : Real) := by norm_num
  have hoffset :
      ‖(t - 1 / 2 : Real) • T.axis.direction‖ <= (1 / 2 : Real) := by
    rw [norm_smul, T.axis.norm_direction, mul_one, Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have hpoint :
      (eighthNormalizedAxis T).base +
          t • (eighthNormalizedAxis T).direction =
        eighthDilationPoint (tubeAxisMidpoint T) +
          (t - 1 / 2 : Real) • T.axis.direction := by
    simp only [eighthNormalizedAxis_base, eighthNormalizedAxis_direction]
    module
  change ‖(eighthNormalizedAxis T).base +
    t • (eighthNormalizedAxis T).direction‖ ≤ (3 / 4 : Real)
  rw [hpoint]
  calc
    ‖eighthDilationPoint (tubeAxisMidpoint T) +
        (t - 1 / 2 : Real) • T.axis.direction‖ <=
        ‖eighthDilationPoint (tubeAxisMidpoint T)‖ +
          ‖(t - 1 / 2 : Real) • T.axis.direction‖ := norm_add_le _ _
    _ <= (1 / 4 : Real) + (1 / 2 : Real) := add_le_add hcenter hoffset
    _ = (3 / 4 : Real) := by norm_num

/-- After eighth-dilation and unit-axis extension, every normalized tube is
contained in the unit ball. -/
theorem eighthNormalizedTube_carrier_subset_unitBall
    {delta : NNReal} (T : Tube delta)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hB2 : T.carrier ⊆ Metric.closedBall (0 : Space) 2) :
    (eighthNormalizedTube T).carrier ⊆
      Metric.closedBall (0 : Space) 1 := by
  have haxis :=
    eighthNormalizedAxis_carrier_subset_threeQuartersBall T hB2
  have hradius : ((delta / 8 : NNReal) : Real) <= (1 / 16 : Real) := by
    have hreal' : (delta : Real) ≤ (((2 : NNReal)⁻¹ : NNReal) : Real) :=
      NNReal.coe_le_coe.mpr hdeltaHalf
    have hreal : (delta : Real) ≤ (1 / 2 : Real) := by
      simpa using hreal'
    push_cast
    linarith
  change Metric.cthickening ((delta / 8 : NNReal) : Real)
      (eighthNormalizedAxis T).carrier ⊆ Metric.closedBall (0 : Space) 1
  refine (Metric.cthickening_subset_of_subset _ haxis).trans ?_
  rw [cthickening_closedBall (by positivity) (by norm_num)]
  exact Metric.closedBall_subset_closedBall (by linarith)

#print axioms tubeAxisMidpoint_mem_carrier
#print axioms norm_tubeAxisMidpoint_le_two_of_carrier_subset
#print axioms eighthNormalizedAxis_carrier_subset_threeQuartersBall
#print axioms eighthNormalizedTube_carrier_subset_unitBall

end
end Family8FiniteRandomRigidMotionB2NormalizationCoreV1
