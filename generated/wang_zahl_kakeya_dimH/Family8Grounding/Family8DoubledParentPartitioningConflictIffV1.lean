import Family8Grounding.Family8Def212ConvexWolffAtEveryScaleV2
import Mathlib.Tactic

/-!
# Doubled-parent partitioning is exactly absence of parent conflicts

This file records the missing converse to the conflict-free construction.
For a literal sticky scale cover, doubled-parent partitioning is equivalent to
pairwise absence of a fine tube contained in two distinct doubled parents.
Thus arbitrary covers do not acquire partitioning merely from a chosen parent
map: one must either prove this no-conflict property or restrict/select the
cover, with a separate retention argument for the selected hierarchy.
-/

set_option autoImplicit false
set_option warningAsError true

open Set

namespace Family8DoubledParentPartitioningConflictIffV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

namespace ScaleCover

variable {delta rho : NNReal} {index : Type} [Fintype index]
  [DecidableEq index] {fine : UniformTubeFamily delta index}

/-- A doubled-parent conflict is an active fine tube lying in two full
doubled parents. -/
def DoubledParentConflict (S : StickyScaleCover fine rho)
    (k l : Fin S.coarseCard) : Prop :=
  ∃ i, i ∈ S.activeFine ∧
    (fine.tubes i).carrier ⊆ twoFoldTubeCarrier (S.coarse.tubes k) ∧
    (fine.tubes i).carrier ⊆ twoFoldTubeCarrier (S.coarse.tubes l)

/-- Pairwise absence of doubled-parent conflicts gives literal disjointness
of the doubled fibres. -/
theorem isDoubledParentPartitioning_of_pairwise_noDoubledParentConflict
    (S : StickyScaleCover fine rho)
    (hpairwise : Set.Pairwise (↑S.activeCoarse : Set (Fin S.coarseCard))
      (fun k l ↦ ¬ DoubledParentConflict S k l)) :
    IsDoubledParentPartitioning S := by
  intro k hk l hl hkl
  rw [Finset.disjoint_left]
  intro i hik hil
  have hik' := (mem_doubledFiber S i k).mp hik
  have hil' := (mem_doubledFiber S i l).mp hil
  exact hpairwise hk hl hkl ⟨i, hik'.1, hik'.2, hil'.2⟩

/-- A literal doubled-parent partition has no doubled-parent conflict between
distinct active parents. -/
theorem pairwise_noDoubledParentConflict_of_isDoubledParentPartitioning
    (S : StickyScaleCover fine rho)
    (hpartition : IsDoubledParentPartitioning S) :
    Set.Pairwise (↑S.activeCoarse : Set (Fin S.coarseCard))
      (fun k l ↦ ¬ DoubledParentConflict S k l) := by
  intro k hk l hl hkl hconflict
  obtain ⟨i, hi, hik, hil⟩ := hconflict
  have hikFiber : i ∈ doubledFiber S k :=
    (mem_doubledFiber S i k).2 ⟨hi, hik⟩
  have hilFiber : i ∈ doubledFiber S l :=
    (mem_doubledFiber S i l).2 ⟨hi, hil⟩
  exact (Finset.disjoint_left.mp (hpartition k hk l hl hkl))
    hikFiber hilFiber

/-- Exact characterization of the structural partitioning datum. -/
theorem isDoubledParentPartitioning_iff_pairwise_noDoubledParentConflict
    (S : StickyScaleCover fine rho) :
    IsDoubledParentPartitioning S ↔
      Set.Pairwise (↑S.activeCoarse : Set (Fin S.coarseCard))
        (fun k l ↦ ¬ DoubledParentConflict S k l) := by
  constructor
  · exact pairwise_noDoubledParentConflict_of_isDoubledParentPartitioning S
  · exact isDoubledParentPartitioning_of_pairwise_noDoubledParentConflict S

/-- One witnessed conflict between distinct active parents is a formal
obstruction to doubled-parent partitioning. -/
theorem not_isDoubledParentPartitioning_of_doubledParentConflict
    (S : StickyScaleCover fine rho)
    {k l : Fin S.coarseCard}
    (hk : k ∈ S.activeCoarse) (hl : l ∈ S.activeCoarse) (hkl : k ≠ l)
    (hconflict : DoubledParentConflict S k l) :
    ¬ IsDoubledParentPartitioning S := by
  intro hpartition
  exact
    (pairwise_noDoubledParentConflict_of_isDoubledParentPartitioning
      S hpartition) hk hl hkl hconflict

#print axioms pairwise_noDoubledParentConflict_of_isDoubledParentPartitioning
#print axioms isDoubledParentPartitioning_iff_pairwise_noDoubledParentConflict
#print axioms not_isDoubledParentPartitioning_of_doubledParentConflict

end ScaleCover
end
end Family8DoubledParentPartitioningConflictIffV1
