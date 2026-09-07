import Family8Grounding.Family8Family7CoordinateToVerticalUnionTransportV1
import Family8Grounding.Family8Family7FirstCrossingFamilyGraphBucketV12
import Mathlib.Tactic

/-!
# Average retention on the literal FirstCrossing graph bucket, V11

V10 is frozen after direct validation exposed one mechanical local-let rewrite
failure.  This ADD-only successor unfolds that let with `dsimp` first and keeps
the same raw-coordinate, elementwise union and average proof.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7FirstCrossingFamilyGraphBucketAverageRetentionV11

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8Family7CoordinateToVerticalMassTransportV1
open Family8Family7CoordinateToVerticalShadingV1
open Family8Family7CoordinateToVerticalUnionTransportV1
open Family8Family7CoordinateToVerticalWeightedChartShadingV3
open Family8Family7CoordinateToVerticalWeightedChartSourceV2
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1

noncomputable section

universe u v

/-- The selected graph-bucket union is contained in the full coordinate
image of the same final-fibre shading. -/
theorem firstCrossingFamilyGraphBucketShading_shadedUnion_subset_coordinate
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (axis : Fin 3) (label : Int)
    (F : UniformTubeFamily radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization F.bodyFamily coarse)
    {Y : Shading F.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa) :
    (firstCrossingFamilyGraphBucketShading
      axis label F P A k).shadedUnion ⊆
        (firstCrossingFamilyCoordinateShading axis F P A k).shadedUnion := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  rw [firstCrossingFamilyGraphBucketShading,
    IndexedShadingRefinement.restrictTo_carrier] at hxi
  by_cases hi : i ∈ verticalSourceGraphCBucketFiber
      ((radius : Real) / 2)
      (firstCrossingFamilyVerticalSource axis F P k) label
  · rw [if_pos hi] at hxi
    have hiChart :=
      (mem_verticalSourceGraphCBucketFiber_iff
        ((radius : Real) / 2)
        (firstCrossingFamilyVerticalSource axis F P k) label i).1 hi |>.1
    change i ∈ verticalSourceDirectionChartFiber
      F (P.index.fiber k) axis at hiChart
    rw [firstCrossingFamilyVerticalShading,
      coordinateToVerticalChartShadingV3_carrier,
      if_pos hiChart] at hxi
    change x ∈
      (coordinateToVerticalShading axis F
        (finalFiberShading A k)).carrier i at hxi ⊢
    exact hxi
  · rw [if_neg hi] at hxi
    exact hxi.elim

/-- The exact chart/graph mass loss also bounds the original final-fibre
average by the graph-bucket average. -/
theorem finalFiber_averageMultiplicity_le_graphLoss_mul_graphAverage
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (axis : Fin 3) (label : Int)
    (F : UniformTubeFamily radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization F.bodyFamily coarse)
    {Y : Shading F.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa)
    (hretained : WithinFactor
      (3 * verticalGraphCBucketLoss ((radius : Real) / 2))
      (finalFiberShading A k).shadingMass
      (firstCrossingFamilyGraphBucketShading
        axis label F P A k).shadingMass) :
    (finalFiberShading A k).averageMultiplicity ≤
      ((3 * verticalGraphCBucketLoss
        ((radius : Real) / 2) : Nat) : ENNReal) *
        (firstCrossingFamilyGraphBucketShading
          axis label F P A k).averageMultiplicity := by
  let graphLoss : ENNReal :=
    ((3 * verticalGraphCBucketLoss
      ((radius : Real) / 2) : Nat) : ENNReal)
  let Zgraph := firstCrossingFamilyGraphBucketShading axis label F P A k
  have hmass :
      (coordinateToVerticalShading axis F
        (finalFiberShading A k)).shadingMass ≤
        graphLoss * Zgraph.shadingMass := by
    have hmass0 : (finalFiberShading A k).shadingMass ≤
        graphLoss * Zgraph.shadingMass := by
      simpa only [graphLoss, Zgraph, WithinFactor, nsmul_eq_mul] using
        hretained
    rw [coordinateToVerticalShading_shadingMass]
    exact hmass0
  have hunion : Zgraph.shadedUnion ⊆
      (coordinateToVerticalShading axis F
        (finalFiberShading A k)).shadedUnion := by
    intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    dsimp only [Zgraph] at hxi
    rw [firstCrossingFamilyGraphBucketShading,
      IndexedShadingRefinement.restrictTo_carrier] at hxi
    by_cases hi : i ∈ verticalSourceGraphCBucketFiber
        ((radius : Real) / 2)
        (firstCrossingFamilyVerticalSource axis F P k) label
    · rw [if_pos hi] at hxi
      have hiChart :=
        (mem_verticalSourceGraphCBucketFiber_iff
          ((radius : Real) / 2)
          (firstCrossingFamilyVerticalSource axis F P k) label i).1 hi |>.1
      change i ∈ verticalSourceDirectionChartFiber
        F (P.index.fiber k) axis at hiChart
      rw [firstCrossingFamilyVerticalShading,
        coordinateToVerticalChartShadingV3_carrier,
        if_pos hiChart] at hxi
      change x ∈
        (coordinateToVerticalShading axis F
          (finalFiberShading A k)).carrier i at hxi ⊢
      exact hxi
    · rw [if_neg hi] at hxi
      exact hxi.elim
  have haverage :
      (coordinateToVerticalShading axis F
        (finalFiberShading A k)).averageMultiplicity ≤
        graphLoss * Zgraph.averageMultiplicity := by
    unfold Shading.averageMultiplicity
    calc
      (coordinateToVerticalShading axis F
          (finalFiberShading A k)).shadingMass /
          volume (coordinateToVerticalShading axis F
            (finalFiberShading A k)).shadedUnion ≤
          (graphLoss * Zgraph.shadingMass) /
            volume (coordinateToVerticalShading axis F
              (finalFiberShading A k)).shadedUnion :=
        ENNReal.div_le_div_right hmass _
      _ ≤ (graphLoss * Zgraph.shadingMass) /
          volume Zgraph.shadedUnion :=
        ENNReal.div_le_div_left (measure_mono hunion) _
      _ = graphLoss *
          (Zgraph.shadingMass / volume Zgraph.shadedUnion) := by
        simp only [div_eq_mul_inv]
        ac_rfl
  rw [← coordinateToVerticalShading_averageMultiplicity
    axis F (finalFiberShading A k)]
  simpa only [Zgraph, graphLoss] using haverage

#print axioms
  firstCrossingFamilyGraphBucketShading_shadedUnion_subset_coordinate
#print axioms
  finalFiber_averageMultiplicity_le_graphLoss_mul_graphAverage

end
end Family8Family7FirstCrossingFamilyGraphBucketAverageRetentionV11
