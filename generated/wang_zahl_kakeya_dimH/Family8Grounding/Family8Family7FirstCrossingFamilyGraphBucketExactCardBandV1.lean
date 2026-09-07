import Family8Grounding.Family8Family7FirstCrossingFamilyGraphBucketV12
import Family8Grounding.Family8Family7ShadingMassPositiveProjectedActiveRegionV1
import Family8Grounding.Family8Family7FiniteProjectedPositiveExactCardBandV1
import FamilyStickyGrounding.FamilyStickyWZ2ProjectionSliceRetentionV1
import Mathlib.Tactic

/-!
# Exact-card positive band on the family-generic first-crossing graph bucket

This ADD-only wrapper stays on the literal graph and graph-restricted shading
chosen by `Family8Family7FirstCrossingFamilyGraphBucketV12`.  Unlike the older
WZL3-specialized wrapper, the input fine family is an arbitrary uniform tube
family, as required by the normalized LongCore bounded assembly.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7FirstCrossingFamilyGraphBucketExactCardBandV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8Family7FiniteProjectedPositiveExactCardBandV1
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7ShadingMassPositiveProjectedActiveRegionV1
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8ShadingAwareProjectedPhysicalV3
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyWZ2ProjectionSliceRetentionV1

noncomputable section

universe u v

/-- The literal zero/universal-window projected datum on the family-generic
graph bucket. -/
def firstCrossingFamilyGraphBucketZeroPhysical
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (axis : Fin 3) (label : Int)
    (F : UniformTubeFamily radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization F.bodyFamily coarse)
    {Y : Shading F.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa) :
    FiniteProjectedShading ProjectionSpace iota :=
  shadingAwareProjectedPhysical
    (firstCrossingFamilyGraphBucketShading axis label F P A k)
    (verticalSourceGraphCBucketFiber ((radius : Real) / 2)
      (firstCrossingFamilyVerticalSource axis F P k) label)
    (fun _ : Real => 0) measurable_const Set.univ MeasurableSet.univ
      Set.univ MeasurableSet.univ

@[simp] theorem firstCrossingFamilyGraphBucketZeroPhysical_ambient
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (axis : Fin 3) (label : Int)
    (F : UniformTubeFamily radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization F.bodyFamily coarse)
    {Y : Shading F.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa) :
    (firstCrossingFamilyGraphBucketZeroPhysical
      axis label F P A k).ambient =
      verticalSourceGraphCBucketFiber ((radius : Real) / 2)
        (firstCrossingFamilyVerticalSource axis F P k) label :=
  rfl

/-- Nonzero literal graph shading mass gives a positive projected region on
the same graph, with no family, axis, label, or shading reselection. -/
theorem positive_firstCrossingFamilyGraphBucket_activeRegion
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (axis : Fin 3) (label : Int)
    (F : UniformTubeFamily radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization F.bodyFamily coarse)
    {Y : Shading F.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa)
    (hgraphMass :
      (firstCrossingFamilyGraphBucketShading
        axis label F P A k).shadingMass ≠ 0) :
    0 < volume
      {u | u ∈ (firstCrossingFamilyGraphBucketZeroPhysical
          axis label F P A k).base ∧
        ((firstCrossingFamilyGraphBucketZeroPhysical
          axis label F P A k).activeAtPoint u).Nonempty} := by
  let VS := firstCrossingFamilyVerticalSource axis F P k
  let graph := verticalSourceGraphCBucketFiber
    ((radius : Real) / 2) VS label
  let V := firstCrossingFamilyVerticalShading axis F P A k
  let Zgraph := firstCrossingFamilyGraphBucketShading axis label F P A k
  have hsum : 0 < ∑ i ∈ graph,
      volume ((shadingWindowRestriction Zgraph (fun _ : Real => 0)
        measurable_const Set.univ MeasurableSet.univ
          Set.univ MeasurableSet.univ).carrier i) := by
    have hwindow : ∀ i,
        (shadingWindowRestriction Zgraph (fun _ : Real => 0)
          measurable_const Set.univ MeasurableSet.univ
            Set.univ MeasurableSet.univ).carrier i =
          Zgraph.carrier i := by
      intro i
      simp [shadingWindowRestriction, shadingProjectionWindow]
    simp_rw [hwindow]
    have heq : (∑ i ∈ graph, volume (Zgraph.carrier i)) =
        Zgraph.shadingMass := by
      change (∑ i ∈ graph,
          volume (((IndexedShadingRefinement.restrictTo V graph).shading
            ).carrier i)) =
        (IndexedShadingRefinement.restrictTo V graph).shading.shadingMass
      rw [shadingMass_restrictTo_eq_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [IndexedShadingRefinement.restrictTo_carrier, if_pos hi]
    rw [heq]
    exact pos_iff_ne_zero.mpr (by simpa only [Zgraph] using hgraphMass)
  have hpositive := positive_projectedActiveRegion_of_activeShadingMass
    Zgraph graph (fun _ : Real => 0) measurable_const
      Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ hsum
  simpa only [firstCrossingFamilyGraphBucketZeroPhysical, Zgraph, graph, VS]
    using hpositive

/-- The positive family-generic graph region contains one literal positive
exact-cardinality band. -/
theorem exists_firstCrossingFamilyGraphBucket_positiveExactCardBand
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (axis : Fin 3) (label : Int)
    (F : UniformTubeFamily radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization F.bodyFamily coarse)
    {Y : Shading F.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa)
    (hgraphMass :
      (firstCrossingFamilyGraphBucketShading
        axis label F P A k).shadingMass ≠ 0) :
    let graph := verticalSourceGraphCBucketFiber ((radius : Real) / 2)
      (firstCrossingFamilyVerticalSource axis F P k) label
    let Z := firstCrossingFamilyGraphBucketZeroPhysical axis label F P A k
    ∃ n : Nat, 1 ≤ n ∧ n ≤ graph.card ∧
      0 < volume (Z.multiplicityBand n n) := by
  dsimp only
  let Z := firstCrossingFamilyGraphBucketZeroPhysical axis label F P A k
  have hpositive := positive_firstCrossingFamilyGraphBucket_activeRegion
    axis label F P A k hgraphMass
  obtain ⟨n, hn1, hnambient, hband⟩ :=
    exists_positive_exactCard_multiplicityBand volume Z (by
      simpa only [Z] using hpositive)
  refine ⟨n, hn1, ?_, hband⟩
  simpa only [Z, firstCrossingFamilyGraphBucketZeroPhysical_ambient]
    using hnambient

#print axioms firstCrossingFamilyGraphBucketZeroPhysical
#print axioms firstCrossingFamilyGraphBucketZeroPhysical_ambient
#print axioms positive_firstCrossingFamilyGraphBucket_activeRegion
#print axioms exists_firstCrossingFamilyGraphBucket_positiveExactCardBand

end
end Family8Family7FirstCrossingFamilyGraphBucketExactCardBandV1
