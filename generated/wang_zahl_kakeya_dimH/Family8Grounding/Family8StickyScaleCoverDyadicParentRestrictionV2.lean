import Family8Grounding.Family8Def212CUniformDyadicBridgeV2
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55OwnerClusterDyadicRefinementV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal BigOperators

namespace Family8StickyScaleCoverDyadicParentRestrictionV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32Lemma55OwnerClusterDyadicRefinementV1

noncomputable section

/-!
# Heterogeneous parent-fibre dyadic restriction

The cinematic pigeonhole theorem is stated for an endomap on one finite
type.  A sticky cover has a heterogeneous parent map from fine indices to
coarse indices.  We embed the two sides into `Sum`, invoke that theorem
unchanged, and decode its selected pivots before constructing the honest
restricted cover.
-/

universe u v

/-- Cardinality of a heterogeneous owner fibre. -/
def parentClusterCard {alpha : Type u} {beta : Type v}
    [DecidableEq alpha] [DecidableEq beta]
    (vertices : Finset alpha) (owner : alpha → beta) (b : beta) : Nat :=
  (vertices.filter fun a ↦ owner a = b).card

/-- Fine vertices above selected heterogeneous parents. -/
def parentClusterUnion {alpha : Type u} {beta : Type v}
    [DecidableEq alpha] [DecidableEq beta]
    (vertices : Finset alpha) (selected : Finset beta) (owner : alpha → beta) :
    Finset alpha :=
  vertices.filter fun a ↦ owner a ∈ selected

/-- A fine/coarse bipartite set embedded into a common type. -/
def ownerNodeVertices {alpha : Type u} {beta : Type v}
    [DecidableEq alpha] [DecidableEq beta] (vertices : Finset alpha) :
    Finset (Sum alpha beta) :=
  vertices.map ⟨Sum.inl, Sum.inl_injective⟩

def ownerNodePivots {alpha : Type u} {beta : Type v}
    [DecidableEq alpha] [DecidableEq beta] (pivots : Finset beta) :
    Finset (Sum alpha beta) :=
  pivots.map ⟨Sum.inr, Sum.inr_injective⟩

def ownerNodeMap {alpha : Type u} {beta : Type v}
    (owner : alpha → beta) : Sum alpha beta → Sum alpha beta
  | Sum.inl a => Sum.inr (owner a)
  | Sum.inr b => Sum.inr b

/-- The heterogeneous content of the existing owner-cluster selection. -/
structure ParentClusterDyadicRefinement
    {alpha : Type u} {beta : Type v}
    [DecidableEq alpha] [DecidableEq beta]
    (vertices : Finset alpha) (pivots : Finset beta) (owner : alpha → beta) where
  level : Nat
  selectedPivots : Finset beta
  selectedPivots_nonempty : selectedPivots.Nonempty
  selectedPivots_subset : selectedPivots ⊆ pivots
  clusterCard_bounds : ∀ b, b ∈ selectedPivots →
    2 ^ level ≤ parentClusterCard vertices owner b ∧
      parentClusterCard vertices owner b < 2 * 2 ^ level
  full_card_le_loss_mul_retained_card :
    vertices.card ≤ ownerClusterBucketLoss vertices *
      (parentClusterUnion vertices selectedPivots owner).card
  retained_nonempty :
    (parentClusterUnion vertices selectedPivots owner).Nonempty

/-- Decode the selected right-hand vertices of a homogeneous `Sum`
refinement. -/
def decodedSelectedPivots
    {alpha : Type u} {beta : Type v}
    [DecidableEq alpha] [DecidableEq beta]
    (vertices : Finset alpha) (pivots : Finset beta) (owner : alpha → beta)
    (R : OwnerClusterDyadicRefinement
      (ownerNodeVertices vertices) (ownerNodePivots pivots) (ownerNodeMap owner)) :
    Finset beta :=
  pivots.filter fun b ↦ Sum.inr b ∈ R.selectedPivots

theorem mem_decodedSelectedPivots_iff
    {alpha : Type u} {beta : Type v}
    [DecidableEq alpha] [DecidableEq beta]
    (vertices : Finset alpha) (pivots : Finset beta) (owner : alpha → beta)
    (R : OwnerClusterDyadicRefinement
      (ownerNodeVertices vertices) (ownerNodePivots pivots) (ownerNodeMap owner))
    (b : beta) :
    b ∈ decodedSelectedPivots vertices pivots owner R ↔
      Sum.inr b ∈ R.selectedPivots := by
  constructor
  · intro hb
    exact (Finset.mem_filter.mp hb).2
  · intro hb
    refine Finset.mem_filter.mpr ⟨?_, hb⟩
    have hp := R.selectedPivots_subset hb
    rcases Finset.mem_map.mp hp with ⟨b', hb', hEq⟩
    have hbb : b' = b := Sum.inr_injective hEq
    simpa only [hbb] using hb'

theorem selectedPivots_eq_map_decoded
    {alpha : Type u} {beta : Type v}
    [DecidableEq alpha] [DecidableEq beta]
    (vertices : Finset alpha) (pivots : Finset beta) (owner : alpha → beta)
    (R : OwnerClusterDyadicRefinement
      (ownerNodeVertices vertices) (ownerNodePivots pivots) (ownerNodeMap owner)) :
    R.selectedPivots =
      (decodedSelectedPivots vertices pivots owner R).map
        ⟨Sum.inr, Sum.inr_injective⟩ := by
  ext n
  cases n with
  | inl a =>
      constructor
      · intro hn
        have hp := R.selectedPivots_subset hn
        rcases Finset.mem_map.mp hp with ⟨b, _hb, hEq⟩
        cases hEq
      · intro hn
        rcases Finset.mem_map.mp hn with ⟨b, _hb, hEq⟩
        cases hEq
  | inr b =>
      constructor
      · intro hb
        exact Finset.mem_map.mpr
          ⟨b, (mem_decodedSelectedPivots_iff
            vertices pivots owner R b).mpr hb, rfl⟩
      · intro hb
        rcases Finset.mem_map.mp hb with ⟨b', hb', hEq⟩
        have hbb : b' = b := Sum.inr_injective hEq
        subst b'
        exact (mem_decodedSelectedPivots_iff
          vertices pivots owner R b).mp hb'

theorem ownerNode_clusterCard_eq
    {alpha : Type u} {beta : Type v}
    [DecidableEq alpha] [DecidableEq beta]
    (vertices : Finset alpha) (owner : alpha → beta) (b : beta) :
    ownerClusterCard (ownerNodeVertices vertices) (ownerNodeMap owner)
        (Sum.inr b) = parentClusterCard vertices owner b := by
  classical
  unfold ownerClusterCard parentClusterCard
  rw [show
    (ownerNodeVertices vertices).filter
        (fun n => ownerNodeMap owner n = Sum.inr b) =
      (vertices.filter fun a => owner a = b).map
        ⟨Sum.inl, Sum.inl_injective⟩ by
      ext n
      cases n with
      | inl a =>
          constructor
          · intro h
            have hd := Finset.mem_filter.mp h
            rcases Finset.mem_map.mp hd.1 with ⟨a', ha', hEq⟩
            have haa : a' = a := Sum.inl_injective hEq
            subst a'
            exact Finset.mem_map.mpr
              ⟨a, Finset.mem_filter.mpr
                ⟨ha', Sum.inr_injective hd.2⟩, rfl⟩
          · intro h
            rcases Finset.mem_map.mp h with ⟨a', ha', hEq⟩
            have haa : a' = a := Sum.inl_injective hEq
            subst a'
            have hd := Finset.mem_filter.mp ha'
            refine Finset.mem_filter.mpr
              ⟨Finset.mem_map.mpr ⟨a, hd.1, rfl⟩, ?_⟩
            exact congrArg Sum.inr hd.2
      | inr b =>
          constructor
          · intro h
            rcases Finset.mem_map.mp (Finset.mem_filter.mp h).1 with
              ⟨a, _ha, hEq⟩
            cases hEq
          · intro h
            rcases Finset.mem_map.mp h with ⟨a, _ha, hEq⟩
            cases hEq]
  rw [Finset.card_map]

theorem ownerNode_union_card_eq
    {alpha : Type u} {beta : Type v}
    [DecidableEq alpha] [DecidableEq beta]
    (vertices : Finset alpha) (pivots : Finset beta) (owner : alpha → beta)
    (R : OwnerClusterDyadicRefinement
      (ownerNodeVertices vertices) (ownerNodePivots pivots) (ownerNodeMap owner)) :
    (ownerClusterUnion (ownerNodeVertices vertices) R.selectedPivots
      (ownerNodeMap owner)).card =
      (parentClusterUnion vertices
        (decodedSelectedPivots vertices pivots owner R) owner).card := by
  rw [selectedPivots_eq_map_decoded vertices pivots owner R]
  unfold ownerClusterUnion parentClusterUnion
  rw [show
    (ownerNodeVertices vertices).filter
        (fun n => ownerNodeMap owner n ∈
          (decodedSelectedPivots vertices pivots owner R).map
            ⟨Sum.inr, Sum.inr_injective⟩) =
      (vertices.filter fun a =>
        owner a ∈ decodedSelectedPivots vertices pivots owner R).map
          ⟨Sum.inl, Sum.inl_injective⟩ by
      ext n
      cases n with
      | inl a =>
          constructor
          · intro h
            have hd := Finset.mem_filter.mp h
            rcases Finset.mem_map.mp hd.1 with ⟨a', ha', hEq⟩
            have haa : a' = a := Sum.inl_injective hEq
            subst a'
            have howner : owner a ∈
                decodedSelectedPivots vertices pivots owner R := by
              rcases Finset.mem_map.mp hd.2 with ⟨b, hb, hEqOwner⟩
              have hba : b = owner a := Sum.inr_injective hEqOwner
              simpa only [hba] using hb
            exact Finset.mem_map.mpr
              ⟨a, Finset.mem_filter.mpr ⟨ha', howner⟩, rfl⟩
          · intro h
            rcases Finset.mem_map.mp h with ⟨a', ha', hEq⟩
            have haa : a' = a := Sum.inl_injective hEq
            subst a'
            have hd := Finset.mem_filter.mp ha'
            refine Finset.mem_filter.mpr
              ⟨Finset.mem_map.mpr ⟨a, hd.1, rfl⟩, ?_⟩
            exact Finset.mem_map.mpr ⟨owner a, hd.2, rfl⟩
      | inr b =>
          constructor
          · intro h
            rcases Finset.mem_map.mp (Finset.mem_filter.mp h).1 with
              ⟨a, _ha, hEq⟩
            cases hEq
          · intro h
            rcases Finset.mem_map.mp h with ⟨a, _ha, hEq⟩
            cases hEq]
  rw [Finset.card_map]

/-- The old homogeneous pigeonhole theorem, transported without loss to a
heterogeneous fine-to-coarse owner map. -/
theorem exists_parentCluster_dyadic_refinement
    {alpha : Type u} {beta : Type v}
    [DecidableEq alpha] [DecidableEq beta]
    (vertices : Finset alpha) (pivots : Finset beta) (owner : alpha → beta)
    (hvertices : vertices.Nonempty)
    (hmaps : (vertices : Set alpha).MapsTo owner pivots) :
    Nonempty (ParentClusterDyadicRefinement vertices pivots owner) := by
  classical
  have hnodeMaps :
      (ownerNodeVertices (beta := beta) vertices :
        Set (Sum alpha beta)).MapsTo
        (ownerNodeMap owner)
          (ownerNodePivots (alpha := alpha) pivots :
            Set (Sum alpha beta)) := by
    intro n hn
    rcases Finset.mem_map.mp hn with ⟨a, ha, rfl⟩
    exact Finset.mem_map.mpr ⟨owner a, hmaps ha, rfl⟩
  have hnodeNonempty :
      (ownerNodeVertices (beta := beta) vertices).Nonempty := by
    obtain ⟨a, ha⟩ := hvertices
    exact ⟨Sum.inl a, Finset.mem_map.mpr ⟨a, ha, rfl⟩⟩
  obtain ⟨R⟩ := exists_ownerCluster_dyadic_refinement
    (ownerNodeVertices (beta := beta) vertices)
      (ownerNodePivots (alpha := alpha) pivots)
      (ownerNodeMap owner) hnodeNonempty
      (Finset.card_eq_sum_card_fiberwise hnodeMaps)
  let selected := decodedSelectedPivots vertices pivots owner R
  have hselectedNonempty : selected.Nonempty := by
    obtain ⟨n, hn⟩ := R.selectedPivots_nonempty
    have hp := R.selectedPivots_subset hn
    rcases Finset.mem_map.mp hp with ⟨b, hb, hbn⟩
    subst n
    exact ⟨b, (mem_decodedSelectedPivots_iff
      vertices pivots owner R b).mpr hn⟩
  refine ⟨{
    level := R.level
    selectedPivots := selected
    selectedPivots_nonempty := hselectedNonempty
    selectedPivots_subset := Finset.filter_subset _ _
    clusterCard_bounds := ?_
    full_card_le_loss_mul_retained_card := ?_
    retained_nonempty := ?_ }⟩
  · intro b hb
    have hbR := (mem_decodedSelectedPivots_iff
      vertices pivots owner R b).mp hb
    simpa only [ownerNode_clusterCard_eq] using
      R.clusterCard_bounds (Sum.inr b) hbR
  · have h := R.full_card_le_loss_mul_retained_card
    have hverticesCard : (ownerNodeVertices (beta := beta) vertices).card = vertices.card := by
      simp [ownerNodeVertices]
    have hloss : ownerClusterBucketLoss (ownerNodeVertices (beta := beta) vertices) =
        ownerClusterBucketLoss vertices := by
      simp [ownerClusterBucketLoss, ownerNodeVertices]
    rw [hverticesCard, hloss,
      ownerNode_union_card_eq vertices pivots owner R] at h
    exact h
  · apply Finset.card_pos.mp
    have hpos := Finset.card_pos.mpr R.retained_nonempty
    rw [ownerNode_union_card_eq vertices pivots owner R] at hpos
    exact hpos

#print axioms exists_parentCluster_dyadic_refinement

end

end Family8StickyScaleCoverDyadicParentRestrictionV2
