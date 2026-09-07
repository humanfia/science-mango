import Family8Grounding.Family8Family7FirstCrossingFinalFiberVerticalChartAdapterV1
import Family8Grounding.Family8Family7WeightedVerticalGraphCBucketV1
import Submission.Kakeya.ConvexFactoring.QuantitativeRefinement
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7FirstCrossingFinalFiberVerticalGraphCBucketV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open Family8Family7FirstCrossingFinalFiberDataV1
open Family8Family7CoordinateToVerticalWeightedChartSourceV2
open Family8Family7CoordinateToVerticalWeightedChartShadingV3
open Family8Family7FirstCrossingFinalFiberVerticalChartAdapterV1
open Family8Family7WeightedVerticalGraphCBucketV1

noncomputable section

universe u v

/-! # Literal first-crossing chart plus weighted graph-c bucket -/

def firstCrossingFinalFiberVerticalGraphCBucketShading
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (axis : Fin 3) (label : Int)
    (S : WZL3UniformTubeSource radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization S.family.bodyFamily coarse)
    {Y : Shading S.family.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa) :
    Shading (firstCrossingFinalFiberVerticalSource axis S P k).family.bodyFamily :=
  (IndexedShadingRefinement.restrictTo
    (firstCrossingFinalFiberVerticalShading axis S P A k)
    (verticalSourceGraphCBucketFiber ((radius : Real) / 2)
      (firstCrossingFinalFiberVerticalSource axis S P k) label)).shading

/-- The transported chart shading is already supported on the source field
of its literal WZL3 record. -/
theorem firstCrossingFinalFiberVerticalShading_restrict_source_shadingMass
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (axis : Fin 3) (S : WZL3UniformTubeSource radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization S.family.bodyFamily coarse)
    {Y : Shading S.family.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa) :
    (IndexedShadingRefinement.restrictTo
      (firstCrossingFinalFiberVerticalShading axis S P A k)
      (firstCrossingFinalFiberVerticalSource axis S P k).source).shading.shadingMass =
      (firstCrossingFinalFiberVerticalShading axis S P A k).shadingMass := by
  rw [shadingMass_restrictTo_eq_sum]
  unfold Shading.shadingMass
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _hi hi
  change i ∉ verticalSourceDirectionChartFiber S.family
    (selectedFrozenFiberActive S P k) axis at hi
  rw [firstCrossingFinalFiberVerticalShading,
    coordinateToVerticalChartShadingV3_carrier, if_neg hi, measure_empty]

/-- Chart selection and the honest graph-c floor bucket compose with the
exact loss `3 * graphBucketLoss`; the selected label is nonempty and has the
same-bucket slope bound used by the native-high core. -/
theorem exists_firstCrossingFinalFiberVerticalGraphCBucket_mass_retention
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (S : WZL3UniformTubeSource radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization S.family.bodyFamily coarse)
    {Y : Shading S.family.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa)
    (hradius : 0 < radius)
    (hmass : (selectedFrozenFiberShading S P A k).shadingMass ≠ 0) :
    ∃ axis : Fin 3, ∃ label : Int,
      (verticalSourceGraphCBucketFiber ((radius : Real) / 2)
        (firstCrossingFinalFiberVerticalSource axis S P k) label).Nonempty ∧
      WithinFactor
        (3 * verticalGraphCBucketLoss ((radius : Real) / 2))
        (selectedFrozenFiberShading S P A k).shadingMass
        (firstCrossingFinalFiberVerticalGraphCBucketShading
          axis label S P A k).shadingMass ∧
      (∀ i, i ∈ verticalSourceGraphCBucketFiber ((radius : Real) / 2)
          (firstCrossingFinalFiberVerticalSource axis S P k) label →
        verticalGraphCBucket ((radius : Real) / 2)
          ((firstCrossingFinalFiberVerticalSource axis S P k).family.tubes i) =
            label) ∧
      ∀ i, i ∈ verticalSourceGraphCBucketFiber ((radius : Real) / 2)
          (firstCrossingFinalFiberVerticalSource axis S P k) label →
        ∀ j, j ∈ verticalSourceGraphCBucketFiber ((radius : Real) / 2)
          (firstCrossingFinalFiberVerticalSource axis S P k) label →
        |projectedTubeGraphC
              ((firstCrossingFinalFiberVerticalSource axis S P k).family.tubes i) -
            projectedTubeGraphC
              ((firstCrossingFinalFiberVerticalSource axis S P k).family.tubes j)| ≤
          (radius : Real) / 2 := by
  obtain ⟨axis, hchart⟩ :=
    exists_firstCrossingFinalFiberVertical_mass_retention S P A k
  let V := firstCrossingFinalFiberVerticalShading axis S P A k
  let VS := firstCrossingFinalFiberVerticalSource axis S P k
  have hVmass : V.shadingMass ≠ 0 := by
    intro hzero
    apply hmass
    have hle : (selectedFrozenFiberShading S P A k).shadingMass ≤ 0 := by
      simpa [WithinFactor, V, hzero] using hchart
    exact le_antisymm hle bot_le
  have hVSsource : VS.source.Nonempty := by
    by_contra hnonempty
    have hempty : VS.source = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnonempty
    apply hVmass
    rw [← firstCrossingFinalFiberVerticalShading_restrict_source_shadingMass
      axis S P A k, shadingMass_restrictTo_eq_sum, hempty]
    simp
  have heta : 0 < (radius : Real) / 2 := by
    exact div_pos (by exact_mod_cast hradius) (by norm_num)
  obtain ⟨label, hfiber, _hoccupied, hloss, hbucket⟩ :=
    exists_verticalSourceGraphCBucket_weight_retention heta VS hVSsource
      (shadingWeight V)
  have hgraph : WithinFactor (verticalGraphCBucketLoss ((radius : Real) / 2))
      V.shadingMass
      (firstCrossingFinalFiberVerticalGraphCBucketShading
        axis label S P A k).shadingMass := by
    unfold WithinFactor
    rw [← firstCrossingFinalFiberVerticalShading_restrict_source_shadingMass
      axis S P A k,
      shadingMass_restrictTo_eq_coe_sum_shadingWeight,
      firstCrossingFinalFiberVerticalGraphCBucketShading,
      shadingMass_restrictTo_eq_coe_sum_shadingWeight]
    exact_mod_cast hloss
  have hcombined := hchart.trans hgraph
  refine ⟨axis, label, ?_, ?_, ?_, ?_⟩
  · simpa [VS] using hfiber
  · simpa [V] using hcombined
  · intro i hi
    apply hbucket i
    simpa [VS] using hi
  · intro i hi j hj
    apply abs_projectedTubeGraphC_sub_le_of_verticalGraphCBucket_eq heta
    exact (hbucket i (by simpa [VS] using hi)).trans
      (hbucket j (by simpa [VS] using hj)).symm

#print axioms firstCrossingFinalFiberVerticalGraphCBucketShading
#print axioms firstCrossingFinalFiberVerticalShading_restrict_source_shadingMass
#print axioms exists_firstCrossingFinalFiberVerticalGraphCBucket_mass_retention

end

end Family8Family7FirstCrossingFinalFiberVerticalGraphCBucketV1
