import Family8Grounding.Family8Family7FirstCrossingGraphBucketPositiveWindowMassV1
import Family8Grounding.Family8ShadingAwareProjectedPhysicalV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7FirstCrossingGraphBucketZeroPhysicalV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8Family7FirstCrossingFinalFiberVerticalChartAdapterV1
open Family8Family7FirstCrossingFinalFiberVerticalGraphCBucketV1
open Family8Family7FirstCrossingGraphBucketPositiveWindowMassV1
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FrozenNeighborhoodAssemblyV1
open Family8ShadingAwareProjectedPhysicalV3
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyWZ2ProjectionSliceRetentionV1

noncomputable section

universe u v

/-! # Zero/universal-window projected physical datum on a graph bucket -/

def firstCrossingGraphBucketZeroPhysical
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (axis : Fin 3) (label : Int)
    (S : WZL3UniformTubeSource radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization S.family.bodyFamily coarse)
    {Y : Shading S.family.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa) :
    FiniteProjectedShading ProjectionSpace iota :=
  shadingAwareProjectedPhysical
    (firstCrossingFinalFiberVerticalGraphCBucketShading
      axis label S P A k)
    (verticalSourceGraphCBucketFiber ((radius : Real) / 2)
      (firstCrossingFinalFiberVerticalSource axis S P k) label)
    (fun _ : Real => 0) measurable_const Set.univ MeasurableSet.univ
      Set.univ MeasurableSet.univ

#print axioms firstCrossingGraphBucketZeroPhysical

end

end Family8Family7FirstCrossingGraphBucketZeroPhysicalV2
