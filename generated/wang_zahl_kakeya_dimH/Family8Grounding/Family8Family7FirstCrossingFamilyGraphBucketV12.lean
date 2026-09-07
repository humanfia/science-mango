import Family8Grounding.Family8Family7CoordinateToVerticalSelectedSubtypeDensityV3
import Family8Grounding.Family8GeneralizedFrostmanMultiplicityV1
import Family8Grounding.Family8Family7CoordinateToVerticalShadingV1
import Family8Grounding.Family8Family7CoordinateToVerticalWeightedChartSourceV2
import Family8Grounding.Family8Family7CoordinateToVerticalWeightedChartShadingV3
import Family8Grounding.Family8Family7WeightedVerticalGraphCBucketV1
import Family8Grounding.Family8FrozenAssemblyMassPopularFiberDensityV2
import Family8Grounding.Family8FrozenComparableActualAverageMassDensityV1
import Family8Grounding.Family8FrozenNeighborhoodAssemblyV1
import Family8Grounding.Family8StickyShadingAwareLogBucketSelectionV1
import FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
import FamilyStickyCinematicL32WZL3UniformTubeSourceV1
import Submission.Kakeya.ConvexFactoring.HeavyParentSelection
import Submission.Kakeya.ConvexFactoring.QuantitativeRefinement
import Submission.Kakeya.Uniformity.TubeFamily
import Mathlib.Tactic

/-!
# Family-only first-crossing chart and graph bucket, V12

V10 unfolded the shading wrapper but not its dependent source wrapper, while
V11's raw local object broke two later wrapper rewrites; neither is imported.
This clean successor retains the wrapper object and unfolds both layers only
at the unique cast seam, preserving the literal family, assembly fibre, direction chart, graph bucket, and every
mass identity unchanged.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7FirstCrossingFamilyGraphBucketV12

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Family8Family7CoordinateToVerticalSelectedSubtypeDensityV3
open Family8Family7CoordinateToVerticalShadingV1
open Family8Family7CoordinateToVerticalWeightedChartShadingV3
open Family8Family7CoordinateToVerticalWeightedChartSourceV2
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FrozenAssemblyMassPopularFiberDensityV2
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8StickyShadingAwareLogBucketSelectionV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u v

/-- The genuine vertical source selected inside one actual factorization
fibre.  Its source is the literal direction-chart subset of that fibre. -/
def firstCrossingFamilyVerticalSource
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (axis : Fin 3) (F : UniformTubeFamily radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization F.bodyFamily coarse) (k : kappa) :
    WZL3UniformTubeSource radius iota :=
  coordinateToVerticalChartSourceV2 axis F (P.index.fiber k)

/-- The corresponding transported chart restriction of the literal final
fibre shading. -/
def firstCrossingFamilyVerticalShading
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (axis : Fin 3) (F : UniformTubeFamily radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization F.bodyFamily coarse)
    {Y : Shading F.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa) :
    Shading (firstCrossingFamilyVerticalSource axis F P k).family.bodyFamily :=
  coordinateToVerticalChartShadingV3 axis F
    (finalFiberShading A k) (P.index.fiber k)

/-- The full coordinate image of the final-fibre shading, before selecting
the chart or graph bucket. -/
def firstCrossingFamilyCoordinateShading
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (axis : Fin 3) (F : UniformTubeFamily radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization F.bodyFamily coarse)
    {Y : Shading F.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa) :
    Shading (firstCrossingFamilyVerticalSource axis F P k).family.bodyFamily :=
  coordinateToVerticalShading axis F (finalFiberShading A k)

/-- The actual chart shading restricted to one occupied graph-`c` bucket. -/
def firstCrossingFamilyGraphBucketShading
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (axis : Fin 3) (label : Int)
    (F : UniformTubeFamily radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization F.bodyFamily coarse)
    {Y : Shading F.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa) :
    Shading (firstCrossingFamilyVerticalSource axis F P k).family.bodyFamily :=
  (IndexedShadingRefinement.restrictTo
    (firstCrossingFamilyVerticalShading axis F P A k)
    (verticalSourceGraphCBucketFiber ((radius : Real) / 2)
      (firstCrossingFamilyVerticalSource axis F P k) label)).shading

/-- A final-fibre shading is already supported on its literal
factorization fibre. -/
theorem finalFiberShading_restrict_fiber_shadingMass
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (F : UniformTubeFamily radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization F.bodyFamily coarse)
    {Y : Shading F.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa) :
    (IndexedShadingRefinement.restrictTo
      (finalFiberShading A k) (P.index.fiber k)).shading.shadingMass =
        (finalFiberShading A k).shadingMass := by
  rw [shadingMass_restrictTo_eq_sum]
  unfold Shading.shadingMass
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _hi hi
  rw [finalFiberShading, fiberShading_carrier, if_neg hi, measure_empty]

/-- The chart shading is already supported on the genuine chart source. -/
theorem firstCrossingFamilyVerticalShading_restrict_source_shadingMass
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (axis : Fin 3) (F : UniformTubeFamily radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization F.bodyFamily coarse)
    {Y : Shading F.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa) :
    (IndexedShadingRefinement.restrictTo
      (firstCrossingFamilyVerticalShading axis F P A k)
      (firstCrossingFamilyVerticalSource axis F P k).source).shading.shadingMass =
      (firstCrossingFamilyVerticalShading axis F P A k).shadingMass := by
  rw [shadingMass_restrictTo_eq_sum]
  unfold Shading.shadingMass
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _hi hi
  change i ∉ verticalSourceDirectionChartFiber F (P.index.fiber k) axis at hi
  rw [firstCrossingFamilyVerticalShading,
    coordinateToVerticalChartShadingV3_carrier, if_neg hi, measure_empty]

/-- A family-only mass-popular fibre admits one genuine vertical chart and
one occupied graph bucket, with exact combined loss
`3 * verticalGraphCBucketLoss`. -/
theorem exists_firstCrossingFamilyGraphBucket_mass_retention
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (F : UniformTubeFamily radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization F.bodyFamily coarse)
    {Y : Shading F.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa)
    (hradius : 0 < radius)
    (hmass : (finalFiberShading A k).shadingMass ≠ 0) :
    ∃ axis : Fin 3, ∃ label : Int,
      (verticalSourceGraphCBucketFiber ((radius : Real) / 2)
        (firstCrossingFamilyVerticalSource axis F P k) label).Nonempty ∧
      WithinFactor
        (3 * verticalGraphCBucketLoss ((radius : Real) / 2))
        (finalFiberShading A k).shadingMass
        (firstCrossingFamilyGraphBucketShading
          axis label F P A k).shadingMass ∧
      (∀ i, i ∈ verticalSourceGraphCBucketFiber ((radius : Real) / 2)
          (firstCrossingFamilyVerticalSource axis F P k) label →
        verticalGraphCBucket ((radius : Real) / 2)
          ((firstCrossingFamilyVerticalSource axis F P k).family.tubes i) =
            label) ∧
      ∀ i, i ∈ verticalSourceGraphCBucketFiber ((radius : Real) / 2)
          (firstCrossingFamilyVerticalSource axis F P k) label →
        ∀ j, j ∈ verticalSourceGraphCBucketFiber ((radius : Real) / 2)
          (firstCrossingFamilyVerticalSource axis F P k) label →
        |projectedTubeGraphC
              ((firstCrossingFamilyVerticalSource axis F P k).family.tubes i) -
            projectedTubeGraphC
              ((firstCrossingFamilyVerticalSource axis F P k).family.tubes j)| ≤
          (radius : Real) / 2 := by
  obtain ⟨axis, hchart⟩ :=
    exists_coordinateToVerticalChartShadingV3_mass_retention
      F (finalFiberShading A k) (P.index.fiber k)
  rw [finalFiberShading_restrict_fiber_shadingMass F P A k] at hchart
  let V := firstCrossingFamilyVerticalShading axis F P A k
  let VS := firstCrossingFamilyVerticalSource axis F P k
  have hVmass : V.shadingMass ≠ 0 := by
    intro hzero
    apply hmass
    have hchart' : (finalFiberShading A k).shadingMass ≤
        3 • V.shadingMass := by
      simpa only [V, firstCrossingFamilyVerticalShading,
        firstCrossingFamilyVerticalSource, WithinFactor] using hchart
    have hle : (finalFiberShading A k).shadingMass ≤ 0 := by
      simpa only [hzero, nsmul_zero] using hchart'
    exact le_antisymm hle bot_le
  have hVSsource : VS.source.Nonempty := by
    by_contra hnonempty
    have hempty : VS.source = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnonempty
    apply hVmass
    rw [← firstCrossingFamilyVerticalShading_restrict_source_shadingMass
      axis F P A k, shadingMass_restrictTo_eq_sum, hempty]
    simp
  have heta : 0 < (radius : Real) / 2 := by
    exact div_pos (by exact_mod_cast hradius) (by norm_num)
  obtain ⟨label, hfiber, _hoccupied, hloss, hbucket⟩ :=
    exists_verticalSourceGraphCBucket_weight_retention heta VS hVSsource
      (shadingWeight V)
  have hgraph : WithinFactor (verticalGraphCBucketLoss ((radius : Real) / 2))
      V.shadingMass
      (firstCrossingFamilyGraphBucketShading
        axis label F P A k).shadingMass := by
    unfold WithinFactor
    rw [← firstCrossingFamilyVerticalShading_restrict_source_shadingMass
      axis F P A k,
      shadingMass_restrictTo_eq_coe_sum_shadingWeight,
      firstCrossingFamilyGraphBucketShading,
      shadingMass_restrictTo_eq_coe_sum_shadingWeight]
    exact_mod_cast hloss
  have hcombined := hchart.trans hgraph
  refine ⟨axis, label, ?_, ?_, ?_, ?_⟩
  · simpa only [VS] using hfiber
  · simpa only [V] using hcombined
  · intro i hi
    apply hbucket i
    simpa only [VS] using hi
  · intro i hi j hj
    apply abs_projectedTubeGraphC_sub_le_of_verticalGraphCBucket_eq heta
    exact (hbucket i (by simpa only [VS] using hi)).trans
      (hbucket j (by simpa only [VS] using hj)).symm

/-- Every selected graph index lies in the original actual fibre. -/
theorem firstCrossingFamilyGraphBucket_subset_fiber
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (axis : Fin 3) (label : Int)
    (F : UniformTubeFamily radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization F.bodyFamily coarse) (k : kappa) :
    verticalSourceGraphCBucketFiber ((radius : Real) / 2)
        (firstCrossingFamilyVerticalSource axis F P k) label ⊆
      P.index.fiber k := by
  intro i hi
  have hiChart :=
    (mem_verticalSourceGraphCBucketFiber_iff
      ((radius : Real) / 2)
      (firstCrossingFamilyVerticalSource axis F P k) label i).1 hi |>.1
  change i ∈ verticalSourceDirectionChartFiber F (P.index.fiber k) axis
    at hiChart
  exact (mem_verticalSourceDirectionChartFiber_iff
    F (P.index.fiber k) axis i).1 hiChart |>.1

/-- On the full selected actual fibre, coordinate-image mass-on is exactly
the final-fibre mass. -/
theorem firstCrossingFamilyCoordinateShading_shadingMassOn_fiber
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (axis : Fin 3) (F : UniformTubeFamily radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization F.bodyFamily coarse)
    {Y : Shading F.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa) :
    shadingMassOn (firstCrossingFamilyCoordinateShading axis F P A k)
        (P.index.fiber k) = (finalFiberShading A k).shadingMass := by
  have hrestrict := finalFiberShading_restrict_fiber_shadingMass F P A k
  rw [shadingMass_restrictTo_eq_sum] at hrestrict
  unfold shadingMassOn firstCrossingFamilyCoordinateShading
  simp_rw [coordinateToVerticalShading_carrier,
    volume_rigidMotion_image]
  exact hrestrict

/-- On the graph bucket, the same coordinate-image mass-on is exactly the
literal graph-restricted shading mass. -/
theorem firstCrossingFamilyCoordinateShading_shadingMassOn_graph
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
    shadingMassOn (firstCrossingFamilyCoordinateShading axis F P A k) graph =
      (firstCrossingFamilyGraphBucketShading axis label F P A k).shadingMass := by
  dsimp only
  rw [firstCrossingFamilyGraphBucketShading,
    shadingMass_restrictTo_eq_sum]
  unfold shadingMassOn
  apply Finset.sum_congr rfl
  intro i hi
  have hiChart :=
    (mem_verticalSourceGraphCBucketFiber_iff
      ((radius : Real) / 2)
      (firstCrossingFamilyVerticalSource axis F P k) label i).1 hi |>.1
  change i ∈ verticalSourceDirectionChartFiber F (P.index.fiber k) axis
    at hiChart
  rw [firstCrossingFamilyCoordinateShading,
    coordinateToVerticalShading_carrier,
    firstCrossingFamilyVerticalShading,
    coordinateToVerticalChartShadingV3_carrier, if_pos hiChart]

/-- The selected graph-subtype density is the same whether it is read from
the full coordinate shading or from the already graph-restricted shading. -/
theorem firstCrossingFamilyCoordinateShading_selectedGraph_density
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
    (selectedCoarseShading
      (firstCrossingFamilyCoordinateShading axis F P A k) graph).shadingDensity =
      (selectedCoarseShading
        (firstCrossingFamilyGraphBucketShading axis label F P A k) graph).shadingDensity := by
  dsimp only
  unfold Shading.shadingDensity
  rw [selectedCoarseShading_mass, selectedCoarseShading_mass]
  apply congrArg (fun mass ↦ mass / _)
  apply Finset.sum_congr rfl
  intro i hi
  have hiChart :=
    (mem_verticalSourceGraphCBucketFiber_iff
      ((radius : Real) / 2)
      (firstCrossingFamilyVerticalSource axis F P k) label i).1 hi |>.1
  change i ∈ verticalSourceDirectionChartFiber F (P.index.fiber k) axis
    at hiChart
  rw [firstCrossingFamilyCoordinateShading,
    coordinateToVerticalShading_carrier,
    firstCrossingFamilyGraphBucketShading,
    IndexedShadingRefinement.restrictTo_carrier, if_pos hi,
    firstCrossingFamilyVerticalShading,
    coordinateToVerticalChartShadingV3_carrier, if_pos hiChart]

#print axioms firstCrossingFamilyVerticalSource
#print axioms firstCrossingFamilyVerticalShading
#print axioms firstCrossingFamilyCoordinateShading
#print axioms firstCrossingFamilyGraphBucketShading
#print axioms finalFiberShading_restrict_fiber_shadingMass
#print axioms firstCrossingFamilyVerticalShading_restrict_source_shadingMass
#print axioms exists_firstCrossingFamilyGraphBucket_mass_retention
#print axioms firstCrossingFamilyGraphBucket_subset_fiber
#print axioms firstCrossingFamilyCoordinateShading_shadingMassOn_fiber
#print axioms firstCrossingFamilyCoordinateShading_shadingMassOn_graph
#print axioms firstCrossingFamilyCoordinateShading_selectedGraph_density

end
end Family8Family7FirstCrossingFamilyGraphBucketV12
