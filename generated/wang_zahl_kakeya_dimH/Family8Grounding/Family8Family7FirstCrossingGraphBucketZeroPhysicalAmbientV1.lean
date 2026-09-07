import Family8Grounding.Family8Family7FirstCrossingGraphBucketZeroPhysicalV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7FirstCrossingGraphBucketZeroPhysicalAmbientV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8Family7FirstCrossingFinalFiberVerticalChartAdapterV1
open Family8Family7FirstCrossingGraphBucketZeroPhysicalV2
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FrozenNeighborhoodAssemblyV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u v

/-! # Ambient projection of the literal graph-bucket datum -/

@[simp] theorem firstCrossingGraphBucketZeroPhysical_ambient
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (axis : Fin 3) (label : Int)
    (S : WZL3UniformTubeSource radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization S.family.bodyFamily coarse)
    {Y : Shading S.family.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa) :
    (firstCrossingGraphBucketZeroPhysical
      axis label S P A k).ambient =
      verticalSourceGraphCBucketFiber ((radius : Real) / 2)
        (firstCrossingFinalFiberVerticalSource axis S P k) label := rfl

#print axioms firstCrossingGraphBucketZeroPhysical_ambient

end

end Family8Family7FirstCrossingGraphBucketZeroPhysicalAmbientV1
