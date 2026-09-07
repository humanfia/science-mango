import Family8Grounding.Family8PaperEssentialDistinctConstantExtractionV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55FiniteMaximalIncomparableClusteringV1
import FamilyStickyGrounding.FamilyStickyAtEveryScaleCoreV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal BigOperators

namespace Family8PaperEssentialDistinctOwnerClusterRetentionV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8PaperConflictAnisotropicBoundsV4
open Family8PaperEssentialDistinctConstantExtractionV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32Lemma55FiniteMaximalIncomparableClusteringV1

noncomputable section

/-!
# Honest owner-cluster retention for paper-distinct extraction

A global paper-distinct subfamily cannot in general retain a fixed fraction
inside every arbitrary parent fibre: two conflicting tubes placed in two
singleton fibres are the elementary obstruction.  The correct unconditional
statement keeps an owner map.  Every raw tube is owned by a selected tube
which is equal to it or paper-conflicting with it.  Since a paper-conflict
closed neighbourhood has absolute cardinality, every owner cluster has the
same absolute cap.

Consequently every parent fibre is bounded by the absolute loss times the
number of selected owners which meet that fibre.  The owners need not lie in
the original fibre; moving/reconstructing parents so that they contain these
owners is the remaining geometric hierarchy seam.  This file does not hide
that seam behind a same-fibre retention assumption.
-/

/-- A produced maximal paper-distinct family with literal owner partitions
of cardinality and arbitrary ENNReal mass. -/
structure PaperConflictOwnerClustering
    {delta : NNReal} {index : Type} [DecidableEq index]
    (vertices : Finset index) (tube : index → Tube delta)
    (weight : index → ENNReal) where
  selected : Finset index
  owner : index → index
  selected_subset : selected ⊆ vertices
  selected_nonempty : vertices.Nonempty → selected.Nonempty
  selected_pairwise_paper :
    Set.Pairwise (↑selected : Set index) fun i j =>
      PaperEssentiallyDistinct (tube i) (tube j)
  owner_selected : ∀ a, a ∈ vertices → owner a ∈ selected
  owner_eq_or_conflict : ∀ a, a ∈ vertices →
    owner a = a ∨ PaperConflict (tube (owner a)) (tube a)
  card_partition : vertices.card =
    ∑ b ∈ selected, (vertices.filter fun a => owner a = b).card
  mass_partition : (∑ a ∈ vertices, weight a) =
    ∑ b ∈ selected,
      ∑ a ∈ vertices.filter (fun a => owner a = b), weight a

/-- Maximal independent-set clustering specialized to literal paper
conflict.  Unlike the weighted one-pivot extraction, this returns the owner
partition needed to state local retention honestly. -/
theorem exists_paperConflictOwnerClustering
    {delta : NNReal} {index : Type} [DecidableEq index]
    (vertices : Finset index) (tube : index → Tube delta)
    (weight : index → ENNReal) :
    Nonempty (PaperConflictOwnerClustering vertices tube weight) := by
  classical
  have hsymm : Std.Symm (fun i j => PaperConflict (tube i) (tube j)) := by
    constructor
    intro i j hij
    exact paperConflict_symm.symm (tube i) (tube j) hij
  obtain ⟨selected, owner, hselected, hnonempty, hpairwise,
      hownerSelected, hownerConflict, hcard, hmass⟩ :=
    exists_maximal_pairwise_not_relation_clustering vertices
      (fun i j => PaperConflict (tube i) (tube j)) hsymm weight
  refine ⟨
    { selected := selected
      owner := owner
      selected_subset := hselected
      selected_nonempty := hnonempty
      selected_pairwise_paper := ?_
      owner_selected := hownerSelected
      owner_eq_or_conflict := hownerConflict
      card_partition := hcard
      mass_partition := hmass }⟩
  intro i hi j hj hij
  by_contra hnotPaper
  exact hpairwise hi hj hij
    ((paperConflict_iff_not_paperEssentiallyDistinct (tube i) (tube j)).2
      hnotPaper)

namespace PaperConflictOwnerClustering

variable {delta : NNReal} {index : Type} [DecidableEq index]
  {vertices : Finset index} {tube : index → Tube delta}
  {weight : index → ENNReal}

/-- Each literal owner cluster is contained in the closed paper-conflict
neighbourhood of its selected pivot. -/
theorem ownerCluster_subset_closedConflict
    (C : PaperConflictOwnerClustering vertices tube weight) (b : index) :
    vertices.filter (fun a => C.owner a = b) ⊆
      paperClosedConflictIndices vertices tube b := by
  classical
  intro a ha
  have haData := Finset.mem_filter.mp ha
  have howner := C.owner_eq_or_conflict a haData.1
  rw [haData.2] at howner
  rcases howner with hEq | hconflict
  · exact Finset.mem_filter.mpr ⟨haData.1, Or.inl hEq.symm⟩
  · exact Finset.mem_filter.mpr ⟨haData.1, Or.inr hconflict⟩

/-- Under the original repo overlap distinctness, every owner cluster has an
absolute, scale-independent cardinality cap. -/
theorem ownerCluster_card_le_constant
    (C : PaperConflictOwnerClustering vertices tube weight)
    (hdeltaPos : 0 < delta) (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (hpairwise : Set.Pairwise (↑vertices : Set index) fun i j =>
      EssentiallyDistinct (tube i) (tube j))
    (b : index) :
    (vertices.filter fun a => C.owner a = b).card ≤
      paperConflictConstantCodeLoss + 1 := by
  exact (Finset.card_le_card (C.ownerCluster_subset_closedConflict b)).trans
    (paperClosedConflictIndices_card_le_constant vertices tube hdeltaPos
      hdeltaSmall hpairwise b)

/-- The selected owners met by a source fibre.  This is deliberately an
image, rather than the intersection of `selected` with `source`: an owner may
lie outside the old parent and must later be geometrically reassigned. -/
def sourceOwnerImage
    (C : PaperConflictOwnerClustering vertices tube weight)
    (source : Finset index) : Finset index :=
  source.image C.owner

theorem sourceOwnerImage_subset_selected
    (C : PaperConflictOwnerClustering vertices tube weight)
    {source : Finset index} (hsource : source ⊆ vertices) :
    C.sourceOwnerImage source ⊆ C.selected := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
  exact C.owner_selected a (hsource ha)

/-- Honest per-fibre retention: a source fibre has at most the absolute
conflict loss times the number of selected owners meeting it. -/
theorem source_card_le_constant_mul_ownerImage_card
    (C : PaperConflictOwnerClustering vertices tube weight)
    (hdeltaPos : 0 < delta) (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (hpairwise : Set.Pairwise (↑vertices : Set index) fun i j =>
      EssentiallyDistinct (tube i) (tube j))
    (source : Finset index) (hsource : source ⊆ vertices) :
    source.card ≤
      (paperConflictConstantCodeLoss + 1) *
        (C.sourceOwnerImage source).card := by
  classical
  have hmaps : (↑source : Set index).MapsTo C.owner
      (↑(C.sourceOwnerImage source) : Set index) := by
    intro a ha
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hpartition : source.card =
      ∑ b ∈ C.sourceOwnerImage source,
        (source.filter fun a => C.owner a = b).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber : ∀ b, b ∈ C.sourceOwnerImage source →
      (source.filter fun a => C.owner a = b).card ≤
        paperConflictConstantCodeLoss + 1 := by
    intro b _hb
    have hsubset : (source.filter fun a => C.owner a = b) ⊆
        vertices.filter (fun a => C.owner a = b) := by
      intro a ha
      exact Finset.mem_filter.mpr
        ⟨hsource (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2⟩
    exact (Finset.card_le_card hsubset).trans
      (C.ownerCluster_card_le_constant hdeltaPos hdeltaSmall hpairwise b)
  rw [hpartition]
  calc
    (∑ b ∈ C.sourceOwnerImage source,
        (source.filter fun a => C.owner a = b).card) ≤
        ∑ _b ∈ C.sourceOwnerImage source,
          (paperConflictConstantCodeLoss + 1) := by
      exact Finset.sum_le_sum fun b hb => hfiber b hb
    _ = (C.sourceOwnerImage source).card *
        (paperConflictConstantCodeLoss + 1) := by simp
    _ = (paperConflictConstantCodeLoss + 1) *
        (C.sourceOwnerImage source).card := Nat.mul_comm _ _

/-- Specialization of the honest owner-image bound to every parent fibre of
an existing scale cover.  No same-parent claim about the selected owners is
made. -/
theorem scaleCover_fiber_card_le_constant_mul_ownerImage_card
    [Fintype index]
    {rho : NNReal} {fine : UniformTubeFamily delta index}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho)
    (hdeltaPos : 0 < delta) (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (hpairwise : Set.Pairwise (Set.univ : Set index) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    (k : Fin S.coarseCard) :
    (S.fiber k).card ≤
      (paperConflictConstantCodeLoss + 1) *
        (C.sourceOwnerImage (S.fiber k)).card := by
  have hpairwise' : Set.Pairwise
      (↑(Finset.univ : Finset index) : Set index) fun i j =>
        EssentiallyDistinct (fine.tubes i) (fine.tubes j) := by
    intro i _hi j _hj hij
    exact hpairwise (Set.mem_univ i) (Set.mem_univ j) hij
  exact source_card_le_constant_mul_ownerImage_card
    (vertices := (Finset.univ : Finset index)) (tube := fine.tubes)
    (weight := weight) C hdeltaPos hdeltaSmall hpairwise'
    (S.fiber k) (by simp)

end PaperConflictOwnerClustering

#print axioms exists_paperConflictOwnerClustering
#print axioms PaperConflictOwnerClustering.ownerCluster_card_le_constant
#print axioms PaperConflictOwnerClustering.source_card_le_constant_mul_ownerImage_card
#print axioms PaperConflictOwnerClustering.scaleCover_fiber_card_le_constant_mul_ownerImage_card

end
end Family8PaperEssentialDistinctOwnerClusterRetentionV3
