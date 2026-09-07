import Family8Grounding.Family8GreedySuppliedCoverJointStickyScaleCoverV1
import Mathlib.Tactic

/-!
# Parallel-cluster loss for the greedy/supplied joint cover

The joint cover remembers a greedy occurrence in addition to the genuine
supplied parent.  Hence one supplied coarse tube can occur once for each
greedy block.  This file proves the corresponding sharp finite bookkeeping
bound: the joint parallel cluster is at most the number of greedy
occurrences times the supplied parallel cluster.

No geometric approximation is introduced.  The proof uses the exact
decoding equivalence of occupied joint parent codes and the literal equality
between each joint coarse tube and its supplied tube.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set
open scoped ENNReal NNReal

namespace Family8GreedySuppliedCoverJointParallelBoundV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8GreedySuppliedCoverJointStickyScaleCoverV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

universe u v

variable {delta tau : NNReal}
  {iota : Type u} {kappa : Type v}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {active : Finset iota}
  {candidates : Finset kappa}
  {container : kappa → ConvexBody Space}

/-- The literal parallel cluster in the coarse family of the joint sticky
cover. -/
def jointParallelCluster
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (C : @TubeScaleCover delta tau iota _ fine active)
    (U : Tube tau) :
    Finset (Fin (occupiedJointParents P C).card) := by
  classical
  exact Finset.univ.filter fun q ↦
    EssentiallyParallelAtScale
      ((greedySuppliedJointStickyScaleCover P C).coarse.tubes q) U

@[simp]
theorem mem_jointParallelCluster
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (C : @TubeScaleCover delta tau iota _ fine active)
    (U : Tube tau) (q : Fin (occupiedJointParents P C).card) :
    q ∈ jointParallelCluster P C U ↔
      EssentiallyParallelAtScale
        ((greedySuppliedJointStickyScaleCover P C).coarse.tubes q) U := by
  simp [jointParallelCluster]

/-- Every joint parallel occurrence injects into a pair consisting of its
greedy occurrence and an occurrence of the genuine supplied parallel
cluster. -/
theorem jointParallelCluster_card_le_blocks_mul_supplied
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (C : @TubeScaleCover delta tau iota _ fine active)
    (U : Tube tau) :
    (jointParallelCluster P C U).card ≤
      (blocks fine.bodyFamily P).length * (C.parallelCluster U).card := by
  classical
  let e := occupiedJointParentEquiv P C
  let f : {q // q ∈ jointParallelCluster P C U} →
      Fin (blocks fine.bodyFamily P).length ×
        {r // r ∈ C.parallelCluster U} := fun q ↦
    ((e.symm q.1).1.1, ⟨(e.symm q.1).1.2, by
      have hparallel := (mem_jointParallelCluster P C U q.1).1 q.2
      rw [coarse_tube_eq_decoded_suppliedTube P C q.1] at hparallel
      simpa [TubeScaleCover.parallelCluster] using hparallel⟩)
  have hf : Function.Injective f := by
    intro q r hqr
    dsimp only [f] at hqr
    apply Subtype.ext
    apply e.symm.injective
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z ↦ z.1) hqr
    · exact congrArg (fun z ↦ z.2.1) hqr
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_prod, Fintype.card_fin,
    Fintype.card_coe] using hcard

/-- Replacing the supplied cluster cardinality by a uniform loss gives the
joint cover's explicit loss. -/
theorem jointParallelCluster_card_le_length_mul
    (P : GreedyDensityPartition fine.bodyFamily candidates container active)
    (C : @TubeScaleCover delta tau iota _ fine active)
    {parallelLoss : Nat}
    (hparallel : ∀ U : Tube tau,
      (C.parallelCluster U).card ≤ parallelLoss)
    (U : Tube tau) :
    (jointParallelCluster P C U).card ≤ P.length * parallelLoss := by
  calc
    (jointParallelCluster P C U).card ≤
        (blocks fine.bodyFamily P).length * (C.parallelCluster U).card :=
      jointParallelCluster_card_le_blocks_mul_supplied P C U
    _ ≤ (blocks fine.bodyFamily P).length * parallelLoss :=
      Nat.mul_le_mul_left _ (hparallel U)
    _ = P.length * parallelLoss := by
      rw [blocks_length fine.bodyFamily P]

#print axioms jointParallelCluster
#print axioms jointParallelCluster_card_le_blocks_mul_supplied
#print axioms jointParallelCluster_card_le_length_mul

end
end Family8GreedySuppliedCoverJointParallelBoundV1
