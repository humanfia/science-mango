import Family8Grounding.Family8Family7CoordinateToVerticalUnionTransportV1
import Family8Grounding.Family8Family7FirstCrossingFamilyGraphBucketV12

/-!
# Exact source/coordinate average identity on a first-crossing graph, V4

V1--V3 are frozen extensionality drafts: this version of `Shading` has no
generated `ext` theorem.  This ADD-only successor derives structure equality
from equality of the carrier function using the authoritative
`Shading.mk.injEq`, then rewrites the shading before applying the raw
coordinate-average identity.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7FirstCrossingGraphAverageIdentityV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
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

/-- Proof fields of a shading are irrelevant, so equality of its literal
carrier function determines the whole structure. -/
theorem shading_eq_of_carrier_eq
    {iota : Type u} {F : ConvexFamily iota}
    (Y Z : Shading F) (hcarrier : Y.carrier = Z.carrier) : Y = Z := by
  cases Y
  cases Z
  simpa only [Shading.mk.injEq] using hcarrier

/-- On the literal graph bucket, chart restriction equals coordinate
transport of the original graph restriction as a shading. -/
theorem firstCrossingFamilyGraphBucketShading_eq_coordinate_restrictTo
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (axis : Fin 3) (label : Int)
    (F : UniformTubeFamily radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization F.bodyFamily coarse)
    {Y : Shading F.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa) :
    let graph := verticalSourceGraphCBucketFiber ((radius : Real) / 2)
      (firstCrossingFamilyVerticalSource axis F P k) label
    firstCrossingFamilyGraphBucketShading axis label F P A k =
      coordinateToVerticalShading axis F
        (IndexedShadingRefinement.restrictTo
          (finalFiberShading A k) graph).shading := by
  dsimp only
  apply shading_eq_of_carrier_eq
  funext i
  rw [firstCrossingFamilyGraphBucketShading,
    IndexedShadingRefinement.restrictTo_carrier,
    coordinateToVerticalShading_carrier,
    IndexedShadingRefinement.restrictTo_carrier]
  by_cases hi : i ∈ verticalSourceGraphCBucketFiber
      ((radius : Real) / 2)
      (firstCrossingFamilyVerticalSource axis F P k) label
  · rw [if_pos hi, if_pos hi]
    have hiChart :=
      (mem_verticalSourceGraphCBucketFiber_iff
        ((radius : Real) / 2)
        (firstCrossingFamilyVerticalSource axis F P k) label i).1 hi |>.1
    change i ∈ verticalSourceDirectionChartFiber
      F (P.index.fiber k) axis at hiChart
    rw [firstCrossingFamilyVerticalShading,
      coordinateToVerticalChartShadingV3_carrier, if_pos hiChart]
  · rw [if_neg hi, if_neg hi, Set.image_empty]

/-- The graph-bucket average is exactly the average of the same source graph
restriction; no loss and no reselection occur in the coordinate chart. -/
theorem firstCrossingFamilyGraphBucketShading_averageMultiplicity_eq_restrictTo
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (axis : Fin 3) (label : Int)
    (F : UniformTubeFamily radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization F.bodyFamily coarse)
    {Y : Shading F.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa) :
    let graph := verticalSourceGraphCBucketFiber ((radius : Real) / 2)
      (firstCrossingFamilyVerticalSource axis F P k) label
    (firstCrossingFamilyGraphBucketShading
      axis label F P A k).averageMultiplicity =
      (IndexedShadingRefinement.restrictTo
        (finalFiberShading A k) graph).shading.averageMultiplicity := by
  dsimp only
  let graph := verticalSourceGraphCBucketFiber ((radius : Real) / 2)
    (firstCrossingFamilyVerticalSource axis F P k) label
  let Z : Shading F.bodyFamily :=
    (IndexedShadingRefinement.restrictTo
      (finalFiberShading A k) graph).shading
  have hshading :
      firstCrossingFamilyGraphBucketShading axis label F P A k =
        coordinateToVerticalShading axis F Z := by
    simpa only [graph, Z] using
      firstCrossingFamilyGraphBucketShading_eq_coordinate_restrictTo
        axis label F P A k
  rw [hshading]
  change (coordinateToVerticalShading axis F Z).averageMultiplicity =
    Z.averageMultiplicity
  exact coordinateToVerticalShading_averageMultiplicity axis F Z

#print axioms shading_eq_of_carrier_eq
#print axioms
  firstCrossingFamilyGraphBucketShading_eq_coordinate_restrictTo
#print axioms
  firstCrossingFamilyGraphBucketShading_averageMultiplicity_eq_restrictTo

end
end Family8Family7FirstCrossingGraphAverageIdentityV4
