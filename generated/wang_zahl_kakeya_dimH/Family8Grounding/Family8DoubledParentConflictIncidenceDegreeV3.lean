import Family8Grounding.Family8DoubledParentConflictWeightedRetentionV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal BigOperators

namespace Family8DoubledParentConflictIncidenceDegreeV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8DoubledParentConflictClusteringV2.ScaleCover
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

namespace ScaleCover

variable {delta rho : NNReal} {index : Type} [Fintype index]
  [DecidableEq index] {fine : UniformTubeFamily delta index}

/-- Active parents whose full doubled carrier contains one fixed active fine
tube.  This is the genuine cross-parent multiplicity in Definition 2.10. -/
noncomputable def doubledParentsContainingFine
    (S : StickyScaleCover fine rho) (i : index) :
    Finset (Fin S.coarseCard) := by
  classical
  exact S.activeCoarse.filter fun k ↦
    (fine.tubes i).carrier ⊆ twoFoldTubeCarrier (S.coarse.tubes k)

@[simp]
theorem mem_doubledParentsContainingFine
    (S : StickyScaleCover fine rho) (i : index)
    (k : Fin S.coarseCard) :
    k ∈ doubledParentsContainingFine S i ↔
      k ∈ S.activeCoarse ∧
        (fine.tubes i).carrier ⊆
          twoFoldTubeCarrier (S.coarse.tubes k) := by
  classical
  simp [doubledParentsContainingFine]

/-- The closed doubled-parent conflict neighbourhood as a noncomputable
finite set, keeping decidability implementation details out of theorem
statements. -/
noncomputable def closedDoubledParentConflictNeighbours
    (S : StickyScaleCover fine rho) (k : Fin S.coarseCard) :
    Finset (Fin S.coarseCard) := by
  classical
  exact S.activeCoarse.filter fun l ↦
    l = k ∨ DoubledParentConflict S k l

@[simp]
theorem mem_closedDoubledParentConflictNeighbours
    (S : StickyScaleCover fine rho) (k l : Fin S.coarseCard) :
    l ∈ closedDoubledParentConflictNeighbours S k ↔
      l ∈ S.activeCoarse ∧
        (l = k ∨ DoubledParentConflict S k l) := by
  classical
  simp [closedDoubledParentConflictNeighbours]

/-- Every closed `2A` conflict neighbour of `k` lies either at `k` itself or
in the union of the parent-incidence sets of fine tubes contained in `2k`. -/
theorem closedDoubledParentConflict_subset_incidenceUnion
    (S : StickyScaleCover fine rho) (k : Fin S.coarseCard) :
    closedDoubledParentConflictNeighbours S k ⊆
      insert k ((doubledFiber S k).biUnion
        (doubledParentsContainingFine S)) := by
  classical
  intro l hl
  have hlData := (mem_closedDoubledParentConflictNeighbours S k l).mp hl
  rcases hlData.2 with hEq | hconflict
  · exact Finset.mem_insert.mpr (Or.inl hEq)
  · obtain ⟨i, hiActive, hik, hil⟩ := hconflict
    apply Finset.mem_insert.mpr
    right
    apply Finset.mem_biUnion.mpr
    refine ⟨i, ?_, ?_⟩
    · exact (mem_doubledFiber S i k).mpr ⟨hiActive, hik⟩
    · exact (mem_doubledParentsContainingFine S i l).mpr
        ⟨hlData.1, hil⟩

/-- Finite double-counting form of the `2A` conflict degree bound. -/
theorem closedDoubledParentConflict_card_le_one_add_mul
    (S : StickyScaleCover fine rho) (N M : Nat)
    (hfine : ∀ k, k ∈ S.activeCoarse →
      (doubledFiber S k).card ≤ N)
    (hparent : ∀ i, i ∈ S.activeFine →
      (doubledParentsContainingFine S i).card ≤ M)
    (k : Fin S.coarseCard) (hk : k ∈ S.activeCoarse) :
    (closedDoubledParentConflictNeighbours S k).card ≤
      1 + N * M := by
  classical
  have hunion :
      ((doubledFiber S k).biUnion
        (doubledParentsContainingFine S)).card ≤
        ∑ i ∈ doubledFiber S k,
          (doubledParentsContainingFine S i).card :=
    Finset.card_biUnion_le
  have hsum :
      (∑ i ∈ doubledFiber S k,
        (doubledParentsContainingFine S i).card) ≤
        (doubledFiber S k).card * M := by
    calc
      (∑ i ∈ doubledFiber S k,
          (doubledParentsContainingFine S i).card) ≤
          ∑ _i ∈ doubledFiber S k, M := by
        apply Finset.sum_le_sum
        intro i hi
        exact hparent i ((mem_doubledFiber S i k).mp hi).1
      _ = (doubledFiber S k).card * M := by simp
  calc
    (closedDoubledParentConflictNeighbours S k).card ≤
        (insert k ((doubledFiber S k).biUnion
          (doubledParentsContainingFine S))).card :=
      Finset.card_le_card
        (closedDoubledParentConflict_subset_incidenceUnion S k)
    _ ≤ 1 + ((doubledFiber S k).biUnion
        (doubledParentsContainingFine S)).card := by
      simpa only [Nat.add_comm] using
        Finset.card_insert_le k
          ((doubledFiber S k).biUnion
            (doubledParentsContainingFine S))
    _ ≤ 1 + ∑ i ∈ doubledFiber S k,
        (doubledParentsContainingFine S i).card := by gcongr
    _ ≤ 1 + (doubledFiber S k).card * M := by gcongr
    _ ≤ 1 + N * M := by
      gcongr
      exact hfine k hk

/-- The two honest incidence caps imply the public extensional degree
predicate consumed by weighted greedy selection. -/
theorem closedDoubledParentConflictDegreeBound_of_incidence
    (S : StickyScaleCover fine rho) (N M : Nat)
    (hfine : ∀ k, k ∈ S.activeCoarse →
      (doubledFiber S k).card ≤ N)
    (hparent : ∀ i, i ∈ S.activeFine →
      (doubledParentsContainingFine S i).card ≤ M) :
    ClosedDoubledParentConflictDegreeBound S
      ((1 + N * M : Nat) : ENNReal) := by
  intro k hk neighbours hneighbours
  have heq : neighbours = closedDoubledParentConflictNeighbours S k := by
    ext l
    rw [hneighbours, mem_closedDoubledParentConflictNeighbours]
  rw [heq]
  exact_mod_cast closedDoubledParentConflict_card_le_one_add_mul
    S N M hfine hparent k hk

#print axioms closedDoubledParentConflict_subset_incidenceUnion
#print axioms closedDoubledParentConflict_card_le_one_add_mul
#print axioms closedDoubledParentConflictDegreeBound_of_incidence

end ScaleCover
end
end Family8DoubledParentConflictIncidenceDegreeV3
