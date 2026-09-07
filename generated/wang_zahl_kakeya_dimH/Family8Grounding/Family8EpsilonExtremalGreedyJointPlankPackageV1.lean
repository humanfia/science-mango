import Family8Grounding.Family8EpsilonExtremalActiveStickyXUpperV1
import Family8Grounding.Family8GreedySuppliedCoverJointParallelBoundV1
import Family8Grounding.Family8GreedyWinnerNormalizationScalarBoundsV1
import Mathlib.Tactic

/-!
# A joint epsilon-extremal greedy/plank package

At a scale `tau ∈ [delta, 1/2]`, an epsilon-extremal family supplies a
genuine geometric `TubeScaleCover`.  Independently, the full-convex greedy
partition supplies a mass-retaining normalized winner bucket.  This file
returns both objects in one existential witness and equips the honest
greedy/supplied joint sticky cover with all currently automatic bounds.

The joint parent tube is literally the supplied parent tube.  In particular,
the construction does not use an identity cover or a normalized geometric
proxy.  The joint refinement can, however, split one whole greedy block
among several supplied parents.  No maximal-density or Frostman property of
the whole block is therefore asserted for an individual joint fibre.

The returned `W` retains its uniform normalized-plank conclusion through
`GreedyWinnerNormalizedPlankBucket.family_isPlank`; the final conjunct below
adds the quantitative common-scalar interval `[1/1024, 1]`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8EpsilonExtremalGreedyJointPlankPackageV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8ActiveCoarseDeltaMaxXUpperV1
open Family8EpsilonExtremalActiveStickyXUpperV1
open Family8GreedySuppliedCoverJointParallelBoundV1
open Family8GreedySuppliedCoverJointStickyScaleCoverV1
open Family8GreedyWinnerNormalizedPlankBucketV1
open Family8GreedyWinnerNormalizationScalarBoundsV1
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover

noncomputable section

variable {delta tau : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {Y : Shading fine.bodyFamily}
  {active : Finset iota} {parallelLoss : Nat}
  {epsilon sigma : Real}

/-- One supplied geometric cover, one normalized greedy-winner plank bucket,
and the automatic estimates for their honest occupied joint refinement.

The parent equality records exact provenance in the original coordinates.
Returning `W` itself also preserves `W.family_isPlank`; the scalar bounds are
stated explicitly because they are the quantitative bridge available for a
future normalization pullback. -/
theorem exists_epsilonExtremalGreedyJointPlankPackage
    (G : EpsilonExtremalTubeFamily
      fine Y active parallelLoss epsilon sigma)
    (P : GreedyDensityPartition fine.bodyFamily
      (hullCandidates active) (hullContainer fine.bodyFamily) active)
    (hdeltaTau : delta <= tau)
    (htauHalf : tau <= (2 : NNReal)⁻¹) :
    exists C : @TubeScaleCover delta tau iota _ fine active,
      exists W : GreedyWinnerNormalizedPlankBucket P G.delta_pos,
        (forall U : Tube tau,
          (jointParallelCluster P C U).card <=
            P.length * parallelLoss) ∧
        (greedySuppliedJointStickyScaleCover P C).coarseCard <=
          active.card ∧
        (greedySuppliedJointStickyScaleCover P C).coarseCard <=
          P.length * C.count ∧
        (forall i : {i // i ∈ active},
          (greedySuppliedJointStickyScaleCover P C).coarse.tubes
              ((greedySuppliedJointStickyScaleCover P C).parent i) =
            C.tubes (C.parent i.1)) ∧
        ((activeCoarseCardScaleMass
            (greedySuppliedJointStickyScaleCover P C) : NNReal) : ENNReal) <=
          1024 * coarseDeltaMax
            (greedySuppliedJointStickyScaleCover P C) ∧
        (forall k : Fin (blocks fine.bodyFamily P).length,
          k ∈ W.selected ->
            (1024 : NNReal)⁻¹ <= (sideShapeUpper W.label 2)⁻¹ ∧
              (sideShapeUpper W.label 2)⁻¹ <= 1) := by
  obtain ⟨C, hparallel⟩ := G.scale_covers tau hdeltaTau
    (htauHalf.trans (by norm_num))
  obtain ⟨W⟩ := exists_greedyWinnerNormalizedPlankBucket
    P G.delta_pos G.active_nonempty G.contained_in_unit_ball
  refine ⟨C, W, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro U
    exact jointParallelCluster_card_le_length_mul P C hparallel U
  · exact greedySuppliedJointStickyScaleCover_coarseCard_le_active P C
  · exact
      greedySuppliedJointStickyScaleCover_coarseCard_le_length_mul_count P C
  · intro i
    exact parent_tube_eq_suppliedParentTube P C i
  · exact
      activeCoarseCardScaleMass_le_1024_mul_coarseDeltaMax
        (activeSubtypeDatum fine Y active)
        (activeSubtypeDatum_isAdmissible G)
        (greedySuppliedJointStickyScaleCover P C) htauHalf
  · intro k hk
    exact
      GreedyWinnerNormalizedPlankBucket.normalizationScalar_bounds
        P G.delta_pos W G.contained_in_unit_ball k hk

#print axioms exists_epsilonExtremalGreedyJointPlankPackage

end
end Family8EpsilonExtremalGreedyJointPlankPackageV1
