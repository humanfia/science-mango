import Family8Grounding.Family8Family7CoordinateToVerticalWeightedChartShadingV3
import Family8Grounding.Family8Family7FirstCrossingFinalFiberDataV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7FirstCrossingFinalFiberVerticalChartAdapterV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open Family8Family7FirstCrossingFinalFiberDataV1
open Family8Family7CoordinateToVerticalWeightedChartSourceV2
open Family8Family7CoordinateToVerticalWeightedChartShadingV3

noncomputable section

universe u v

/-! # Same-object first-crossing final-fibre vertical-chart adapter -/

def firstCrossingFinalFiberVerticalSource
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (axis : Fin 3) (S : WZL3UniformTubeSource radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization S.family.bodyFamily coarse)
    (k : kappa) : WZL3UniformTubeSource radius iota :=
  coordinateToVerticalChartSourceV2 axis S.family
    (selectedFrozenFiberActive S P k)

def firstCrossingFinalFiberVerticalShading
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (axis : Fin 3) (S : WZL3UniformTubeSource radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization S.family.bodyFamily coarse)
    {Y : Shading S.family.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa) :
    Shading (firstCrossingFinalFiberVerticalSource axis S P k).family.bodyFamily :=
  coordinateToVerticalChartShadingV3 axis S.family
    (selectedFrozenFiberShading S P A k)
    (selectedFrozenFiberActive S P k)

/-- The final-fibre shading is already supported on its literal
factorization fibre, so restricting it there changes no mass. -/
theorem selectedFrozenFiberShading_restrict_active_shadingMass
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (S : WZL3UniformTubeSource radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization S.family.bodyFamily coarse)
    {Y : Shading S.family.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa) :
    (IndexedShadingRefinement.restrictTo
      (selectedFrozenFiberShading S P A k)
      (selectedFrozenFiberActive S P k)).shading.shadingMass =
        (selectedFrozenFiberShading S P A k).shadingMass := by
  rw [shadingMass_restrictTo_eq_sum]
  unfold Shading.shadingMass
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _hi hi
  rw [selectedFrozenFiberActive_eq S P k] at hi
  rw [selectedFrozenFiberShading_carrier S P A k i,
    selectedFrozenFiberActive_eq S P k, if_neg hi, measure_empty]

/-- The actual selected final-fibre mass survives the chart choice and
coordinate transport with the exact factor three, on the same index type. -/
theorem exists_firstCrossingFinalFiberVertical_mass_retention
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (S : WZL3UniformTubeSource radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization S.family.bodyFamily coarse)
    {Y : Shading S.family.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa) :
    ∃ axis : Fin 3,
      WithinFactor 3
        (selectedFrozenFiberShading S P A k).shadingMass
        (firstCrossingFinalFiberVerticalShading axis S P A k).shadingMass := by
  obtain ⟨axis, hmass⟩ :=
    exists_coordinateToVerticalChartShadingV3_mass_retention
      S.family (selectedFrozenFiberShading S P A k)
        (selectedFrozenFiberActive S P k)
  refine ⟨axis, ?_⟩
  rw [selectedFrozenFiberShading_restrict_active_shadingMass S P A k]
    at hmass
  exact hmass

#print axioms firstCrossingFinalFiberVerticalSource
#print axioms firstCrossingFinalFiberVerticalShading
#print axioms selectedFrozenFiberShading_restrict_active_shadingMass
#print axioms exists_firstCrossingFinalFiberVertical_mass_retention

end

end Family8Family7FirstCrossingFinalFiberVerticalChartAdapterV1
