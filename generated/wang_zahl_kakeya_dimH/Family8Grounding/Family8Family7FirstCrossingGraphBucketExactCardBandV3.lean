import Family8Grounding.Family8Family7FirstCrossingGraphBucketZeroPhysicalV2
import Family8Grounding.Family8Family7FiniteProjectedPositiveExactCardBandV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7FirstCrossingGraphBucketExactCardBandV3

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8Family7FiniteProjectedPositiveExactCardBandV1
open Family8Family7FirstCrossingGraphBucketZeroPhysicalV2
open Family8FrozenNeighborhoodAssemblyV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u v

/-! # Exact-card selection, kept in the literal projected datum -/

theorem exists_firstCrossingGraphBucket_positiveExactCardBand
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (axis : Fin 3) (label : Int)
    (S : WZL3UniformTubeSource radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization S.family.bodyFamily coarse)
    {Y : Shading S.family.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa)
    (hpositive : 0 < volume
      {u | u ∈ (firstCrossingGraphBucketZeroPhysical
          axis label S P A k).base ∧
        ((firstCrossingGraphBucketZeroPhysical
          axis label S P A k).activeAtPoint u).Nonempty}) :
    ∃ n : Nat,
      1 ≤ n ∧
      n ≤ (firstCrossingGraphBucketZeroPhysical
        axis label S P A k).ambient.card ∧
      0 < volume ((firstCrossingGraphBucketZeroPhysical
        axis label S P A k).multiplicityBand n n) :=
  exists_positive_exactCard_multiplicityBand volume
    (firstCrossingGraphBucketZeroPhysical axis label S P A k) hpositive

#print axioms exists_firstCrossingGraphBucket_positiveExactCardBand

end

end Family8Family7FirstCrossingGraphBucketExactCardBandV3
