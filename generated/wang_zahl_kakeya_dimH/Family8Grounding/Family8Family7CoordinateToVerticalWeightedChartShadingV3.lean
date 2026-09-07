import Family8Grounding.Family8Family7CoordinateToVerticalWeightedChartSourceV2
import Family8Grounding.Family8Family7CoordinateToVerticalMassTransportV1
import Submission.Kakeya.ConvexFactoring.QuantitativeRefinement
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7CoordinateToVerticalWeightedChartShadingV3

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8Family7CoordinateToVerticalTubeTransportV1
open Family8Family7CoordinateToVerticalShadingV1
open Family8Family7CoordinateToVerticalMassTransportV1
open Family8Family7CoordinateToVerticalWeightedChartSourceV2

noncomputable section

universe u

/-! # Weight-heavy chart shading on the same transported index family -/

/-- Restrict the original shading to the selected direction chart and move
it by the same coordinate permutation as the corresponding tubes. -/
def coordinateToVerticalChartShadingV3
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (k : Fin 3) (F : UniformTubeFamily radius iota)
    (Y : Shading F.bodyFamily) (source : Finset iota) :
    Shading (coordinateToVerticalChartSourceV2 k F source).family.bodyFamily :=
  coordinateToVerticalShading k F
    (IndexedShadingRefinement.restrictTo Y
      (verticalSourceDirectionChartFiber F source k)).shading

@[simp] theorem coordinateToVerticalChartShadingV3_carrier
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (k : Fin 3) (F : UniformTubeFamily radius iota)
    (Y : Shading F.bodyFamily) (source : Finset iota) (i : iota) :
    (coordinateToVerticalChartShadingV3 k F Y source).carrier i =
      if i ∈ verticalSourceDirectionChartFiber F source k then
        coordinateToVerticalRigidMotion k '' Y.carrier i
      else ∅ := by
  rw [coordinateToVerticalChartShadingV3,
    coordinateToVerticalShading_carrier,
    IndexedShadingRefinement.restrictTo_carrier]
  split_ifs <;> simp_all

theorem coordinateToVerticalChartShadingV3_shadingMass
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (k : Fin 3) (F : UniformTubeFamily radius iota)
    (Y : Shading F.bodyFamily) (source : Finset iota) :
    (coordinateToVerticalChartShadingV3 k F Y source).shadingMass =
      (IndexedShadingRefinement.restrictTo Y
        (verticalSourceDirectionChartFiber F source k)).shading.shadingMass := by
  exact coordinateToVerticalShading_shadingMass k F
    (IndexedShadingRefinement.restrictTo Y
      (verticalSourceDirectionChartFiber F source k)).shading

/-- Exact ENNReal realization of the NNReal weighted chart pigeonhole. -/
theorem exists_coordinateToVerticalChartShadingV3_mass_retention
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    (F : UniformTubeFamily radius iota)
    (Y : Shading F.bodyFamily) (source : Finset iota) :
    ∃ k : Fin 3,
      WithinFactor 3
        (IndexedShadingRefinement.restrictTo Y source).shading.shadingMass
        (coordinateToVerticalChartShadingV3 k F Y source).shadingMass := by
  obtain ⟨k, hweight⟩ :=
    exists_coordinateToVerticalChartSourceV2_weight_retention
      F source (shadingWeight Y)
  refine ⟨k, ?_⟩
  unfold WithinFactor
  rw [shadingMass_restrictTo_eq_coe_sum_shadingWeight,
    coordinateToVerticalChartShadingV3_shadingMass,
    shadingMass_restrictTo_eq_coe_sum_shadingWeight]
  exact_mod_cast hweight

#print axioms coordinateToVerticalChartShadingV3
#print axioms coordinateToVerticalChartShadingV3_carrier
#print axioms coordinateToVerticalChartShadingV3_shadingMass
#print axioms exists_coordinateToVerticalChartShadingV3_mass_retention

end

end Family8Family7CoordinateToVerticalWeightedChartShadingV3
