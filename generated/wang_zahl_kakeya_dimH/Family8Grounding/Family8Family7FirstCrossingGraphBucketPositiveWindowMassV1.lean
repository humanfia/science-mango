import Family8Grounding.Family8Family7FirstCrossingFinalFiberVerticalGraphCBucketV1
import Family8Grounding.Family8Family7WeightedVerticalGraphCBucketActualBridgeV1
import Family8Grounding.Family8ShadingAwareProjectedPhysicalV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7FirstCrossingGraphBucketPositiveWindowMassV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8Family7FirstCrossingFinalFiberDataV1
open Family8Family7FirstCrossingFinalFiberVerticalChartAdapterV1
open Family8Family7FirstCrossingFinalFiberVerticalGraphCBucketV1
open Family8Family7WeightedVerticalGraphCBucketActualBridgeV1
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8ShadingAwareProjectedPhysicalV3
open FamilyStickyCinematicL32PyzActualNormFirstExtremalConcreteCBucketCapV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u v

/-! # Positive zero/universal window mass on the literal graph-c bucket -/

def zeroUnivWindowShading
    {iota : Type u} {F : ConvexFamily iota} (Y : Shading F) : Shading F :=
  shadingWindowRestriction Y (fun _ : Real => 0) measurable_const
    Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ

@[simp] theorem zeroUnivWindowShading_carrier
    {iota : Type u} {F : ConvexFamily iota}
    (Y : Shading F) (i : iota) :
    (zeroUnivWindowShading Y).carrier i = Y.carrier i := by
  simp [zeroUnivWindowShading, shadingWindowRestriction,
    shadingProjectionWindow]

theorem positive_activeWindowMass_of_graphBucketShadingMass
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (axis : Fin 3) (label : Int)
    (S : WZL3UniformTubeSource radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization S.family.bodyFamily coarse)
    {Y : Shading S.family.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa)
    (hmass : 0 < (firstCrossingFinalFiberVerticalGraphCBucketShading
      axis label S P A k).shadingMass) :
    0 < ∑ i ∈ verticalSourceGraphCBucketFiber ((radius : Real) / 2)
        (firstCrossingFinalFiberVerticalSource axis S P k) label,
      volume ((zeroUnivWindowShading
        (firstCrossingFinalFiberVerticalGraphCBucketShading
          axis label S P A k)).carrier i) := by
  simp_rw [zeroUnivWindowShading_carrier]
  have hsum :
      (∑ i ∈ verticalSourceGraphCBucketFiber ((radius : Real) / 2)
          (firstCrossingFinalFiberVerticalSource axis S P k) label,
        volume ((firstCrossingFinalFiberVerticalGraphCBucketShading
          axis label S P A k).carrier i)) =
        (firstCrossingFinalFiberVerticalGraphCBucketShading
          axis label S P A k).shadingMass := by
    change (∑ i ∈ verticalSourceGraphCBucketFiber ((radius : Real) / 2)
          (firstCrossingFinalFiberVerticalSource axis S P k) label,
        volume (((IndexedShadingRefinement.restrictTo
          (firstCrossingFinalFiberVerticalShading axis S P A k)
          (verticalSourceGraphCBucketFiber ((radius : Real) / 2)
            (firstCrossingFinalFiberVerticalSource axis S P k)
              label)).shading).carrier i)) =
      ((IndexedShadingRefinement.restrictTo
        (firstCrossingFinalFiberVerticalShading axis S P A k)
        (verticalSourceGraphCBucketFiber ((radius : Real) / 2)
          (firstCrossingFinalFiberVerticalSource axis S P k)
            label)).shading).shadingMass
    rw [shadingMass_restrictTo_eq_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [IndexedShadingRefinement.restrictTo_carrier, if_pos hi]
  rwa [hsum]

/-- The fixed selected assembly fibre automatically supplies a literal
vertical chart, an actual graph-c bucket, and positive active window mass.
The only source premise is the positive shaded-union conclusion already
returned by the same first-crossing assembly. -/
theorem exists_firstCrossingGraphBucket_positiveActiveWindowMass
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (S : WZL3UniformTubeSource radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization S.family.bodyFamily coarse)
    {Y : Shading S.family.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa)
    (hradius : 0 < radius)
    (hfiber : 0 < volume
      (selectedFrozenFiberShading S P A k).shadedUnion) :
    ∃ axis : Fin 3, ∃ label : Int,
      (verticalSourceGraphCBucketFiber ((radius : Real) / 2)
        (firstCrossingFinalFiberVerticalSource axis S P k) label).Nonempty ∧
      (∀ i, i ∈ verticalSourceGraphCBucketFiber ((radius : Real) / 2)
          (firstCrossingFinalFiberVerticalSource axis S P k) label →
        actualProjectedTubeCBucket ((radius : Real) / 2)
          ((firstCrossingFinalFiberVerticalSource axis S P k).family.tubes i) =
            label) ∧
      0 < ∑ i ∈ verticalSourceGraphCBucketFiber ((radius : Real) / 2)
          (firstCrossingFinalFiberVerticalSource axis S P k) label,
        volume ((zeroUnivWindowShading
          (firstCrossingFinalFiberVerticalGraphCBucketShading
            axis label S P A k)).carrier i) := by
  have hselectedMass :
      (selectedFrozenFiberShading S P A k).shadingMass ≠ 0 := by
    apply ne_of_gt
    have hle := natCast_mul_volume_le_shadingMass_of_pointMultiplicity_lower
      (selectedFrozenFiberShading S P A k) 1 (fun x hx => Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (((selectedFrozenFiberShading S P A k).pointMultiplicity_pos_iff_mem_shadedUnion x).mpr hx)))
    have hle' : volume (selectedFrozenFiberShading S P A k).shadedUnion ≤
        (selectedFrozenFiberShading S P A k).shadingMass := by
      simpa using hle
    exact hfiber.trans_le hle'
  obtain ⟨axis, label, hnonempty, hretention, _hverticalBucket,
      _hgraphGap⟩ :=
    exists_firstCrossingFinalFiberVerticalGraphCBucket_mass_retention
      S P A k hradius hselectedMass
  have hgraphMass : 0 <
      (firstCrossingFinalFiberVerticalGraphCBucketShading
        axis label S P A k).shadingMass := by
    apply pos_iff_ne_zero.mpr
    intro hzero
    apply hselectedMass
    have hle : (selectedFrozenFiberShading S P A k).shadingMass ≤ 0 := by
      simpa [WithinFactor, hzero] using hretention
    exact le_antisymm hle bot_le
  refine ⟨axis, label, hnonempty, ?_,
    positive_activeWindowMass_of_graphBucketShadingMass
      axis label S P A k hgraphMass⟩
  intro i hi
  exact actualProjectedTubeCBucket_eq_of_mem_verticalSourceGraphCBucketFiber
    ((radius : Real) / 2)
      (firstCrossingFinalFiberVerticalSource axis S P k) label hi

#print axioms zeroUnivWindowShading
#print axioms zeroUnivWindowShading_carrier
#print axioms positive_activeWindowMass_of_graphBucketShadingMass
#print axioms exists_firstCrossingGraphBucket_positiveActiveWindowMass

end

end Family8Family7FirstCrossingGraphBucketPositiveWindowMassV1
