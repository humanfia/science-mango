import Family8Grounding.Family8Def212ConvexWolffAtEveryScaleV2
import Submission.Kakeya.ConvexFactoring.TubeHierarchyInfrastructure
import Mathlib.Tactic

/-!
# A one-radius tube thickening lies in the full two-fold dilation

The full paper dilation doubles both length and transverse radius.  Hence
thickening a radius-`rho` tube carrier by at most `rho` stays inside that
full dilation.  This is the geometric bridge needed by parent-specific
occurrence hulls; it is not a stored unique-owner conclusion.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8TubeClosedThickeningInsideTwoFoldV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8Def212ConvexWolffAtEveryScaleV2

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

/-- Thickening a radius-`rho` tube by another `rho` is contained in its full
central two-fold dilation. -/
theorem cthickening_carrier_subset_twoFoldTubeCarrier
    {rho : NNReal} (hrho : 0 < rho) (T : Tube rho) :
    Metric.cthickening (rho : Real) T.carrier ⊆
      twoFoldTubeCarrier T := by
  intro x hx
  rw [Tube.carrier,
    cthickening_cthickening (by positivity) (by positivity)] at hx
  rw [T.axis.isCompact_carrier.cthickening_eq_biUnion_closedBall
    (by positivity)] at hx
  obtain ⟨z, hzAxis, hxzBall⟩ := Set.mem_iUnion₂.mp hx
  have hxz : dist x z ≤ (rho : Real) + (rho : Real) :=
    Metric.mem_closedBall.mp hxzBall
  let c : Space := tubeCenter T
  let xhalf : Space := c + (2 : Real)⁻¹ • (x - c)
  let zhalf : Space := c + (2 : Real)⁻¹ • (z - c)
  have hcAxis : c ∈ T.axis.carrier := by
    simpa only [c, tubeCenter] using
      T.axis.mem_carrier_of_mem_Icc
        (t := (2 : Real)⁻¹) (by constructor <;> norm_num)
  have hzhalfAxis : zhalf ∈ T.axis.carrier := by
    exact T.axis.convex_carrier.add_smul_sub_mem hcAxis hzAxis
      ⟨by norm_num, by norm_num⟩
  have hhalfSub : xhalf - zhalf = (2 : Real)⁻¹ • (x - z) := by
    dsimp only [xhalf, zhalf]
    module
  have hhalfDist : dist xhalf zhalf ≤ (rho : Real) := by
    rw [dist_eq_norm, hhalfSub, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num), ← dist_eq_norm]
    calc
      (2 : Real)⁻¹ * dist x z ≤
          (2 : Real)⁻¹ * ((rho : Real) + (rho : Real)) :=
        mul_le_mul_of_nonneg_left hxz (by norm_num)
      _ = (rho : Real) := by ring
  have hxhalfCarrier : xhalf ∈ T.carrier := by
    exact Metric.mem_cthickening_of_dist_le xhalf zhalf (rho : Real)
      T.axis.carrier hzhalfAxis hhalfDist
  refine ⟨xhalf, hxhalfCarrier, ?_⟩
  dsimp only [twoFoldTubeCarrier, centeredDilationCarrier, xhalf, c]
  module

/-- A smaller thickening of any subset of the parent tube is likewise
contained in the full two-fold parent. -/
theorem cthickening_subset_twoFoldTubeCarrier_of_subset_of_le
    {rho r : NNReal} (hrho : 0 < rho) (T : Tube rho)
    {A : Set Space} (hA : A ⊆ T.carrier) (hr : r ≤ rho) :
    Metric.cthickening (r : Real) A ⊆ twoFoldTubeCarrier T := by
  exact (Metric.cthickening_subset_of_subset (r : Real) hA).trans
    ((Metric.cthickening_mono (by exact_mod_cast hr) T.carrier).trans
      (cthickening_carrier_subset_twoFoldTubeCarrier hrho T))

#print axioms cthickening_carrier_subset_twoFoldTubeCarrier
#print axioms cthickening_subset_twoFoldTubeCarrier_of_subset_of_le

end


end Family8TubeClosedThickeningInsideTwoFoldV2
