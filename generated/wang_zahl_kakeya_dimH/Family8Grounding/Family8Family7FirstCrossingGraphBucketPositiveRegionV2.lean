import Family8Grounding.Family8Family7FirstCrossingGraphBucketZeroPhysicalV2
import Family8Grounding.Family8Family7ShadingMassPositiveProjectedActiveRegionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7FirstCrossingGraphBucketPositiveRegionV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8Family7FirstCrossingFinalFiberVerticalChartAdapterV1
open Family8Family7FirstCrossingFinalFiberVerticalGraphCBucketV1
open Family8Family7FirstCrossingGraphBucketPositiveWindowMassV1
open Family8Family7FirstCrossingGraphBucketZeroPhysicalV2
open Family8Family7ShadingMassPositiveProjectedActiveRegionV1
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FrozenNeighborhoodAssemblyV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u v

/-! # Positive projected active region on the literal graph bucket -/

theorem positive_firstCrossingGraphBucket_activeRegion
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (axis : Fin 3) (label : Int)
    (S : WZL3UniformTubeSource radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization S.family.bodyFamily coarse)
    {Y : Shading S.family.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa)
    (hmass : 0 < ∑ i ∈
      verticalSourceGraphCBucketFiber ((radius : Real) / 2)
        (firstCrossingFinalFiberVerticalSource axis S P k) label,
      volume ((zeroUnivWindowShading
        (firstCrossingFinalFiberVerticalGraphCBucketShading
          axis label S P A k)).carrier i)) :
    0 < volume
      {u | u ∈ (firstCrossingGraphBucketZeroPhysical
          axis label S P A k).base ∧
        ((firstCrossingGraphBucketZeroPhysical
          axis label S P A k).activeAtPoint u).Nonempty} := by
  apply positive_projectedActiveRegion_of_activeShadingMass
    (firstCrossingFinalFiberVerticalGraphCBucketShading axis label S P A k)
    (verticalSourceGraphCBucketFiber ((radius : Real) / 2)
      (firstCrossingFinalFiberVerticalSource axis S P k) label)
    (fun _ : Real => 0) measurable_const Set.univ MeasurableSet.univ
      Set.univ MeasurableSet.univ
  simpa only [zeroUnivWindowShading] using hmass

#print axioms positive_firstCrossingGraphBucket_activeRegion

end

end Family8Family7FirstCrossingGraphBucketPositiveRegionV2
