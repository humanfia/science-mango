import Family8Grounding.Family8ActualRestrictedMassWeightedCriticalBallShadingV4
import Family8Grounding.Family8Family7GenericNativeHighMaxWeightCeilingCardRetentionV3
import Family8Grounding.Family8ProjectedActiveShadingMassMeasureV1
import Family8Grounding.Family8WeightedCanonicalBallMassRatioV1
import Family8Grounding.Family8WeightedCanonicalCriticalScaleProxyAverageV2
import FamilyStickyGrounding.FamilyStickyWZ2ProjectionSliceRetentionV1
import Mathlib.Tactic

/-!
# A ten-radius full-coefficient actual-mass critical scale, V5

The cinematic reduced metric omits the graph-c coefficient and therefore
needs a prior common-c bucket.  For the geometric normalization itself one
may instead use the maximum of all four graph-coefficient gaps.  On a
unit-ball-supported `L₃` family this metric is at most six, hence at most the
canonical ceiling sixteen.

With exponent zero and actual restricted tube masses as weights, the ceiling
ball is the whole active family.  The weighted critical ball consequently
retains the entire projected shading mass, while controlling all four affine
normalization gaps.  No fibre floor, active-pattern equal share, or common-c
bucket is used.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8FullCoefficientActualMassCriticalScaleV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8ActualRestrictedMassWeightedCriticalBallShadingV4
open Family8Family7GenericNativeHighMaxWeightCeilingCardRetentionV3
open Family8Family7NativeHighCriticalScaleAbsAxisChartV1
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8ProjectedActiveShadingMassMeasureV1
open Family8WeightedCanonicalBallMassRatioV1
open Family8WeightedCanonicalCriticalScaleProxyAverageV2
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyWZ2AmbientRestrictedIntegralAdapterV1
open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2ShadingPopularityV2

noncomputable section

universe u

/-- Maximum of all four reduced graph-coefficient gaps. -/
def fullProjectedTubeCoefficientDistance {radius : NNReal}
    (T U : Tube radius) : Real :=
  max
    (max |projectedTubeGraphA T - projectedTubeGraphA U|
      |projectedTubeGraphB T - projectedTubeGraphB U|)
    (max |projectedTubeGraphC T - projectedTubeGraphC U|
      |projectedTubeGraphD T - projectedTubeGraphD U|)

theorem graphA_gap_le_fullCoefficientDistance
    {radius : NNReal} (T U : Tube radius) :
    |projectedTubeGraphA T - projectedTubeGraphA U| ≤
      fullProjectedTubeCoefficientDistance T U := by
  exact (le_max_left _ _).trans (le_max_left _ _)

theorem graphB_gap_le_fullCoefficientDistance
    {radius : NNReal} (T U : Tube radius) :
    |projectedTubeGraphB T - projectedTubeGraphB U| ≤
      fullProjectedTubeCoefficientDistance T U := by
  exact (le_max_right _ _).trans (le_max_left _ _)

theorem graphC_gap_le_fullCoefficientDistance
    {radius : NNReal} (T U : Tube radius) :
    |projectedTubeGraphC T - projectedTubeGraphC U| ≤
      fullProjectedTubeCoefficientDistance T U := by
  exact (le_max_left _ _).trans (le_max_right _ _)

theorem graphD_gap_le_fullCoefficientDistance
    {radius : NNReal} (T U : Tube radius) :
    |projectedTubeGraphD T - projectedTubeGraphD U| ≤
      fullProjectedTubeCoefficientDistance T U := by
  exact (le_max_right _ _).trans (le_max_right _ _)

theorem fullProjectedTubeCoefficientDistance_self
    {radius : NNReal} (T : Tube radius) :
    fullProjectedTubeCoefficientDistance T T = 0 := by
  simp [fullProjectedTubeCoefficientDistance]

/-- Unit support and the `L₃` direction chart bound the full metric by six. -/
theorem fullProjectedTubeCoefficientDistance_le_six_of_supported_vertical
    {radius : NNReal} (T U : Tube radius)
    (hverticalT : (1 / 2 : Real) ≤ |T.axis.direction 2|)
    (hverticalU : (1 / 2 : Real) ≤ |U.axis.direction 2|)
    (hbaseT : T.axis.base ∈ Metric.closedBall (0 : Space) 1)
    (hbaseU : U.axis.base ∈ Metric.closedBall (0 : Space) 1) :
    fullProjectedTubeCoefficientDistance T U ≤ 6 := by
  have hAT := abs_projectedTubeGraphA_le_three_of_supported_vertical
    T hverticalT hbaseT
  have hAU := abs_projectedTubeGraphA_le_three_of_supported_vertical
    U hverticalU hbaseU
  have hBT := abs_projectedTubeGraphB_le_three_of_supported_vertical
    T hverticalT hbaseT
  have hBU := abs_projectedTubeGraphB_le_three_of_supported_vertical
    U hverticalU hbaseU
  have hCT := abs_projectedTubeGraphC_le_two_of_abs_final_half T hverticalT
  have hCU := abs_projectedTubeGraphC_le_two_of_abs_final_half U hverticalU
  have hDT := abs_projectedTubeGraphD_le_two_of_abs_final_half T hverticalT
  have hDU := abs_projectedTubeGraphD_le_two_of_abs_final_half U hverticalU
  have hA : |projectedTubeGraphA T - projectedTubeGraphA U| ≤ 6 := by
    calc
      |projectedTubeGraphA T - projectedTubeGraphA U| ≤
          |projectedTubeGraphA T| + |projectedTubeGraphA U| := abs_sub _ _
      _ ≤ 6 := by linarith
  have hB : |projectedTubeGraphB T - projectedTubeGraphB U| ≤ 6 := by
    calc
      |projectedTubeGraphB T - projectedTubeGraphB U| ≤
          |projectedTubeGraphB T| + |projectedTubeGraphB U| := abs_sub _ _
      _ ≤ 6 := by linarith
  have hC : |projectedTubeGraphC T - projectedTubeGraphC U| ≤ 6 := by
    calc
      |projectedTubeGraphC T - projectedTubeGraphC U| ≤
          |projectedTubeGraphC T| + |projectedTubeGraphC U| := abs_sub _ _
      _ ≤ 6 := by linarith
  have hD : |projectedTubeGraphD T - projectedTubeGraphD U| ≤ 6 := by
    calc
      |projectedTubeGraphD T - projectedTubeGraphD U| ≤
          |projectedTubeGraphD T| + |projectedTubeGraphD U| := abs_sub _ _
      _ ≤ 6 := by linarith
  exact max_le (max_le hA hB) (max_le hC hD)

/-- Geometry-only template on the whole active family. -/
def fullCoefficientNormTemplate
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (active : Finset iota) (hactive : active.Nonempty)
    (hradius : 0 < radius) (htenRadiusSixteen : 10 * (radius : Real) ≤ 16) :
    WeightedCanonicalNormBallData iota where
  family := active
  distance := fun i j => fullProjectedTubeCoefficientDistance
    (S.family.tubes i) (S.family.tubes j)
  weight := fun _ => 0
  delta := 10 * (radius : Real)
  ceiling := 16
  exponent := 0
  family_nonempty := hactive
  self_le_delta := by
    intro center _hcenter
    rw [fullProjectedTubeCoefficientDistance_self]
    positivity
  delta_pos := by
    exact mul_pos (by norm_num) (NNReal.coe_pos.mpr hradius)
  delta_le_ceiling := htenRadiusSixteen
  exponent_nonneg := le_rfl

/-- Same geometric datum, now weighted by literal restricted 3D tube mass. -/
def fullCoefficientActualMassNormData
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (active : Finset iota) (hactive : active.Nonempty)
    (hradius : 0 < radius) (htenRadiusSixteen : 10 * (radius : Real) ≤ 16)
    (Y : Shading S.family.bodyFamily) (X : Set Space) :
    WeightedCanonicalNormBallData iota :=
  actualRestrictedMassWeightedNormData
    (fullCoefficientNormTemplate S active hactive hradius htenRadiusSixteen)
    Y X

theorem fullCoefficient_family_distance_le_sixteen
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (active : Finset iota) (hactive : active.Nonempty)
    (hradius : 0 < radius) (htenRadiusSixteen : 10 * (radius : Real) ≤ 16)
    (Y : Shading S.family.bodyFamily) (X : Set Space)
    (hactiveSource : active ⊆ S.source)
    (hcontained : ∀ i, i ∈ active →
      (S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    {i j : iota}
    (hi : i ∈ (fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X).family)
    (hj : j ∈ (fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X).family) :
    (fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X).distance i j ≤ 16 := by
  have hiVertical := S.source_direction_final_half i (hactiveSource hi)
  have hjVertical := S.source_direction_final_half j (hactiveSource hj)
  have hiBase : (S.family.tubes i).axis.base ∈
      Metric.closedBall (0 : Space) 1 :=
    hcontained i hi ((S.family.tubes i).axis_subset_carrier
      (S.family.tubes i).axis.base_mem_carrier)
  have hjBase : (S.family.tubes j).axis.base ∈
      Metric.closedBall (0 : Space) 1 :=
    hcontained j hj ((S.family.tubes j).axis_subset_carrier
      (S.family.tubes j).axis.base_mem_carrier)
  change fullProjectedTubeCoefficientDistance
    (S.family.tubes i) (S.family.tubes j) ≤ 16
  exact (fullProjectedTubeCoefficientDistance_le_six_of_supported_vertical
    (S.family.tubes i) (S.family.tubes j) hiVertical hjVertical hiBase
      hjBase).trans (by norm_num)

theorem fullCoefficient_ceilingBall_eq_family
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (active : Finset iota) (hactive : active.Nonempty)
    (hradius : 0 < radius) (htenRadiusSixteen : 10 * (radius : Real) ≤ 16)
    (Y : Shading S.family.bodyFamily) (X : Set Space)
    (hactiveSource : active ⊆ S.source)
    (hcontained : ∀ i, i ∈ active →
      (S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (center : iota)
    (hcenter : center ∈ (fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X).family) :
    let W := fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X
    W.family.filter (fun i => W.distance i center ≤ W.ceiling) = W.family := by
  let W := fullCoefficientActualMassNormData S active hactive
    hradius htenRadiusSixteen Y X
  apply Finset.filter_eq_self.mpr
  intro i hi
  exact fullCoefficient_family_distance_le_sixteen S active hactive
    hradius htenRadiusSixteen Y X hactiveSource hcontained hi hcenter

/-- Exponent zero makes the weighted critical ball retain all actual mass. -/
theorem fullCoefficient_totalWeight_le_criticalBallWeight
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (active : Finset iota) (hactive : active.Nonempty)
    (hradius : 0 < radius) (htenRadiusSixteen : 10 * (radius : Real) ≤ 16)
    (Y : Shading S.family.bodyFamily) (X : Set Space)
    (hactiveSource : active ⊆ S.source)
    (hcontained : ∀ i, i ∈ active →
      (S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1) :
    let W := fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X
    (∑ i ∈ W.family, W.weight i) ≤
      ∑ i ∈ W.criticalBall, W.weight i := by
  let W := fullCoefficientActualMassNormData S active hactive
    hradius htenRadiusSixteen Y X
  let center := W.criticalCenter
  have hball := fullCoefficient_ceilingBall_eq_family S active hactive
    hradius htenRadiusSixteen Y X hactiveSource hcontained center
      W.criticalCenter_mem_family
  have hmass := weightedBallMass_le_ratio_rpow_mul_criticalBallMass W
    W.delta_le_ceiling le_rfl center W.criticalCenter_mem_family
  change finiteWeightedBallMass W.family W.distance W.weight W.ceiling center ≤
    ((ENNReal.ofReal W.ceiling / ENNReal.ofReal W.criticalScale) ^
      W.exponent) * ∑ i ∈ W.criticalBall, W.weight i at hmass
  unfold finiteWeightedBallMass at hmass
  rw [hball] at hmass
  simpa only [W, fullCoefficientActualMassNormData,
    actualRestrictedMassWeightedNormData, fullCoefficientNormTemplate,
    ENNReal.rpow_zero, one_mul] using hmass

/-- The canonical lower candidate is ten times the physical radius, so the
large-proxy separation is automatic. -/
theorem ten_mul_radius_le_fullCoefficientCriticalScale
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (active : Finset iota) (hactive : active.Nonempty)
    (hradius : 0 < radius)
    (htenRadiusSixteen : 10 * (radius : Real) ≤ 16)
    (Y : Shading S.family.bodyFamily) (X : Set Space) :
    10 * (radius : Real) ≤
      (fullCoefficientActualMassNormData S active hactive
        hradius htenRadiusSixteen Y X).criticalScale := by
  exact (fullCoefficientActualMassNormData S active hactive
    hradius htenRadiusSixteen Y X).criticalScale_bounds.1

/-- The projected shading-mass measure of a measurable set is retained by
the literal full-coefficient critical-ball shading with constant one. -/
theorem projectedActiveShadingMass_le_fullCoefficientCriticalBallShadingMass
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (Y : Shading S.family.bodyFamily) (active : Finset iota)
    (hactive : active.Nonempty)
    (f : Real → Real) (hf : Measurable f)
    (E : Set (Real × Real)) (hE : MeasurableSet E)
    (hradius : 0 < radius) (htenRadiusSixteen : 10 * (radius : Real) ≤ 16)
    (hactiveSource : active ⊆ S.source)
    (hcontained : ∀ i, i ∈ active →
      (S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1) :
    let X := twistedProjection f ⁻¹' E
    let hX : MeasurableSet X := (twistedProjection_measurable f hf) hE
    let W := fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X
    projectedActiveShadingMassMeasure Y active f E ≤
      (weightedCanonicalCriticalBallShading S W
        (restrictedShading Y X hX)).shadingMass := by
  let X := twistedProjection f ⁻¹' E
  let hX : MeasurableSet X := (twistedProjection_measurable f hf) hE
  let W := fullCoefficientActualMassNormData S active hactive
    hradius htenRadiusSixteen Y X
  have hprojected := projectedActiveShadingMassMeasure_apply
    Y active f hf hE
  have hcritical := fullCoefficient_totalWeight_le_criticalBallWeight
    S active hactive hradius htenRadiusSixteen Y X hactiveSource hcontained
  calc
    projectedActiveShadingMassMeasure Y active f E =
        ∑ i ∈ active, restrictedMass Y X i := by
      simpa only [X] using hprojected
    _ ≤ ∑ i ∈ W.criticalBall, W.weight i := by
      simpa only [W, fullCoefficientActualMassNormData,
        actualRestrictedMassWeightedNormData,
        fullCoefficientNormTemplate] using hcritical
    _ = (weightedCanonicalCriticalBallShading S W
          (restrictedShading Y X hX)).shadingMass := by
      unfold Shading.shadingMass
      simp only [weightedCanonicalCriticalBallShading, restrictedShading,
        W, fullCoefficientActualMassNormData,
        actualRestrictedMassWeightedNormData, restrictedMass]
      exact Finset.sum_subtype _ (fun _i => Iff.rfl) _

#print axioms fullProjectedTubeCoefficientDistance
#print axioms fullProjectedTubeCoefficientDistance_le_six_of_supported_vertical
#print axioms fullCoefficientNormTemplate
#print axioms fullCoefficientActualMassNormData
#print axioms ten_mul_radius_le_fullCoefficientCriticalScale
#print axioms fullCoefficient_totalWeight_le_criticalBallWeight
#print axioms projectedActiveShadingMass_le_fullCoefficientCriticalBallShadingMass

end
end Family8FullCoefficientActualMassCriticalScaleV5
