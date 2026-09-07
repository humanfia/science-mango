import Family8Grounding.Family8EpsilonExtremalSameScaleFineParallelClusterV1
import Mathlib.Tactic

/-!
# Automatic same-scale fine parallel-cluster package

An `EpsilonExtremalTubeFamily` supplies a genuine `delta`-scale
`TubeScaleCover` by specializing its all-scale cover field at `tau = delta`.
The lossless same-scale transfer then injects every active fine directional
cluster into the corresponding supplied parent cluster.

The theorem below returns the supplied cover itself, its original uniform
parent-cluster bound, the transferred fine-cluster bound, and the literal
carrier containment witnessing parent provenance.  It does not manufacture
a numerical upper bound for `parallelLoss` and does not assert an
`IsKatzTao` conclusion.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set
open scoped ENNReal NNReal InnerProductSpace

namespace Family8EpsilonExtremalSameScaleFineParallelClusterPackageV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8EpsilonExtremalSameScaleFineParallelClusterV1

noncomputable section

universe u

variable {delta : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {Y : Shading fine.bodyFamily}
  {active : Finset iota} {parallelLoss : Nat}
  {epsilon sigma : Real}

/-- The primitive epsilon-extremal cover at the literal fine scale, together
with both its supplied parent-cluster loss and the resulting active fine
directional-cluster loss.  The final conjunct records that the returned
parent is the genuine geometric parent supplied by `G.scale_covers`.-/
theorem exists_sameScaleCover_with_activeFineParallelCluster_bound
    (G : EpsilonExtremalTubeFamily
      fine Y active parallelLoss epsilon sigma) :
    exists C : @TubeScaleCover delta delta iota _ fine active,
      (forall U : Tube delta,
        (C.parallelCluster U).card <= parallelLoss) ∧
      (forall U : Tube delta,
        (activeFineParallelCluster fine active U).card <= parallelLoss) ∧
      (forall i : iota, i ∈ active ->
        (fine.tubes i).carrier ⊆
          (C.tubes (C.parent i)).carrier) := by
  obtain ⟨C, hparentCluster⟩ := G.scale_covers delta le_rfl
    (G.delta_le_half.trans (by norm_num))
  refine ⟨C, hparentCluster, ?_, ?_⟩
  · intro U
    exact
      activeFineParallelCluster_card_le_of_epsilonExtremal_parentBound
        G C hparentCluster U
  · intro i hi
    exact C.carrier_subset i hi

#print axioms exists_sameScaleCover_with_activeFineParallelCluster_bound

end
end Family8EpsilonExtremalSameScaleFineParallelClusterPackageV1
