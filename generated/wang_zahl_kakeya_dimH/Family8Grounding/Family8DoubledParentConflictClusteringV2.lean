import Family8Grounding.Family8Def212ConvexWolffAtEveryScaleV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55FiniteMaximalIncomparableClusteringV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal BigOperators

namespace Family8DoubledParentConflictClusteringV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32Lemma55FiniteMaximalIncomparableClusteringV1

noncomputable section

/-! The literal finite obstruction to Definition 2.10 partitioning. -/

namespace ScaleCover

variable {delta rho : NNReal} {index : Type} [Fintype index]
  [DecidableEq index] {fine : UniformTubeFamily delta index}

def DoubledParentConflict (S : StickyScaleCover fine rho)
    (k l : Fin S.coarseCard) : Prop :=
  ∃ i, i ∈ S.activeFine ∧
    (fine.tubes i).carrier ⊆ twoFoldTubeCarrier (S.coarse.tubes k) ∧
    (fine.tubes i).carrier ⊆ twoFoldTubeCarrier (S.coarse.tubes l)

theorem doubledParentConflict_symm (S : StickyScaleCover fine rho) :
    Std.Symm (DoubledParentConflict S) := by
  constructor
  rintro k l ⟨i, hi, hik, hil⟩
  exact ⟨i, hi, hil, hik⟩

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

/-- Maximal independent selection with exact parent-cardinality and arbitrary
ENNReal mass partitions. -/
structure DoubledParentConflictClustering
    (S : StickyScaleCover fine rho)
    (weight : Fin S.coarseCard → ENNReal) where
  selected : Finset (Fin S.coarseCard)
  owner : Fin S.coarseCard → Fin S.coarseCard
  selected_subset : selected ⊆ S.activeCoarse
  selected_nonempty : S.activeCoarse.Nonempty → selected.Nonempty
  selected_pairwise : Set.Pairwise (↑selected : Set (Fin S.coarseCard))
    (fun k l ↦ ¬ DoubledParentConflict S k l)
  owner_selected : ∀ k, k ∈ S.activeCoarse → owner k ∈ selected
  owner_eq_or_conflict : ∀ k, k ∈ S.activeCoarse →
    owner k = k ∨ DoubledParentConflict S (owner k) k
  card_partition : S.activeCoarse.card =
    ∑ l ∈ selected, (S.activeCoarse.filter fun k ↦ owner k = l).card
  mass_partition : (∑ k ∈ S.activeCoarse, weight k) =
    ∑ l ∈ selected,
      ∑ k ∈ S.activeCoarse.filter (fun k ↦ owner k = l), weight k

theorem exists_doubledParentConflictClustering
    (S : StickyScaleCover fine rho)
    (weight : Fin S.coarseCard → ENNReal) :
    Nonempty (DoubledParentConflictClustering S weight) := by
  classical
  obtain ⟨selected, owner, hsubset, hnonempty, hpairwise, howner,
      hownerConflict, hcard, hmass⟩ :=
    exists_maximal_pairwise_not_relation_clustering S.activeCoarse
      (DoubledParentConflict S) (doubledParentConflict_symm S) weight
  exact ⟨{
    selected := selected
    owner := owner
    selected_subset := hsubset
    selected_nonempty := hnonempty
    selected_pairwise := hpairwise
    owner_selected := howner
    owner_eq_or_conflict := hownerConflict
    card_partition := hcard
    mass_partition := hmass }⟩

#print axioms doubledParentConflict_symm
#print axioms isDoubledParentPartitioning_of_pairwise_noDoubledParentConflict
#print axioms exists_doubledParentConflictClustering

end ScaleCover
end
end Family8DoubledParentConflictClusteringV2
