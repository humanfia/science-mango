import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55CompactC2SymmetricComparabilityV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Lemma55FiniteMaximalIncomparableClusteringV1

open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Lemma55CompactC2SymmetricComparabilityV1

noncomputable section

/-!
# Finite maximal incomparable clustering for PYZ Lemma 5.5

A maximal independent subfamily need not retain a fixed fraction of the raw
vertices when comparability degrees are unbounded.  The correct lossless
statement assigns every raw vertex to a comparable selected pivot.  Both
cardinality and arbitrary nonnegative mass are then preserved exactly as
sums over the resulting pivot fibres.  Later geometric arguments may replace
each fibre by one enlarged pivot container.
-/

universe u

/-- Every finite symmetric graph admits an independent dominating set,
together with a literal owner map.  The owner fibres partition both raw
cardinality and arbitrary `ENNReal` mass exactly; no false bounded-degree
claim is used. -/
theorem exists_maximal_pairwise_not_relation_clustering
    {alpha : Type u} [DecidableEq alpha]
    (vertices : Finset alpha)
    (comparable : alpha -> alpha -> Prop) [DecidableRel comparable]
    (hsymm : Std.Symm comparable)
    (weight : alpha -> ENNReal) :
    exists selected : Finset alpha, exists owner : alpha -> alpha,
      selected ⊆ vertices ∧
      (vertices.Nonempty -> selected.Nonempty) ∧
      Set.Pairwise (selected : Set alpha) (fun a b => ¬ comparable a b) ∧
      (forall a, a ∈ vertices -> owner a ∈ selected) ∧
      (forall a, a ∈ vertices ->
        owner a = a ∨ comparable (owner a) a) ∧
      vertices.card =
        ∑ b ∈ selected, (vertices.filter fun a => owner a = b).card ∧
      (∑ a ∈ vertices, weight a) =
        ∑ b ∈ selected,
          ∑ a ∈ vertices.filter (fun a => owner a = b), weight a := by
  classical
  have aux : forall s : Finset alpha, s ⊆ vertices ->
      exists selected : Finset alpha,
        selected ⊆ s ∧
        Set.Pairwise (selected : Set alpha) (fun a b => ¬ comparable a b) ∧
        forall x, x ∈ s ->
          exists b, b ∈ selected ∧ (b = x ∨ comparable b x) := by
    intro s hsvertices
    induction s using Finset.strongInduction with
    | H s ih =>
      by_cases hs : s.Nonempty
      · obtain ⟨a, ha⟩ := hs
        let rest := s.filter fun b => ¬ (b = a ∨ comparable a b)
        have hrestStrict : rest ⊂ s := by
          rw [Finset.filter_ssubset]
          exact ⟨a, ha, by simp⟩
        have hrestVertices : rest ⊆ vertices :=
          (Finset.filter_subset _ _).trans hsvertices
        obtain ⟨selectedRest, hselectedRest, hpairRest, hcoverRest⟩ :=
          ih rest hrestStrict hrestVertices
        have haNotSelected : a ∉ selectedRest := by
          intro hamem
          have haRest := hselectedRest hamem
          exact (Finset.mem_filter.mp haRest).2 (Or.inl rfl)
        have hpairSelected :
            Set.Pairwise ((insert a selectedRest : Finset alpha) : Set alpha)
              (fun x y => ¬ comparable x y) := by
          rw [Finset.coe_insert]
          apply hpairRest.insert
          intro b hb _hab
          have hbRest := hselectedRest hb
          have hnot : ¬ comparable a b := by
            intro hab
            exact (Finset.mem_filter.mp hbRest).2 (Or.inr hab)
          exact ⟨hnot, fun hba => hnot (hsymm.symm _ _ hba)⟩
        refine ⟨insert a selectedRest, ?_, hpairSelected, ?_⟩
        · intro b hb
          rcases Finset.mem_insert.mp hb with rfl | hb
          · exact ha
          · exact Finset.filter_subset _ _ (hselectedRest hb)
        · intro x hx
          by_cases hclosed : x = a ∨ comparable a x
          · refine ⟨a, Finset.mem_insert_self a selectedRest, ?_⟩
            rcases hclosed with hxa | hcomp
            · exact Or.inl hxa.symm
            · exact Or.inr hcomp
          · have hxRest : x ∈ rest :=
              Finset.mem_filter.mpr ⟨hx, hclosed⟩
            obtain ⟨b, hb, hbcover⟩ := hcoverRest x hxRest
            exact ⟨b, Finset.mem_insert_of_mem hb, hbcover⟩
      · have hsEmpty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        subst s
        exact ⟨∅, by simp, by simp, by simp⟩
  obtain ⟨selected, hselected, hpairwise, hcover⟩ :=
    aux vertices Finset.Subset.rfl
  let owner : alpha -> alpha := fun a =>
    if ha : a ∈ vertices then Classical.choose (hcover a ha) else a
  have hownerData : forall a, a ∈ vertices ->
      owner a ∈ selected ∧
        (owner a = a ∨ comparable (owner a) a) := by
    intro a ha
    dsimp [owner]
    rw [dif_pos ha]
    exact Classical.choose_spec (hcover a ha)
  have hmaps : (vertices : Set alpha).MapsTo owner selected := by
    intro a ha
    exact (hownerData a ha).1
  refine ⟨selected, owner, hselected, ?_, hpairwise,
    (fun a ha => (hownerData a ha).1),
    (fun a ha => (hownerData a ha).2), ?_, ?_⟩
  · intro hvertices
    obtain ⟨a, ha⟩ := hvertices
    exact ⟨owner a, (hownerData a ha).1⟩
  · exact Finset.card_eq_sum_card_fiberwise hmaps
  · exact (Finset.sum_fiberwise_of_maps_to hmaps weight).symm

/-- Rectangle specialization of the lossless Lemma 5.5 clustering step.
The selected pivots are pairwise `100`-incomparable, while every raw
rectangle is either its pivot or `100`-comparable to it. -/
theorem exists_maximal_hundred_incomparable_compactC2_clustering
    {alpha : Type u} [DecidableEq alpha]
    (vertices : Finset alpha)
    (rectangleAt : alpha -> C2GraphRectangle)
    (domain : Set Real) (center : C2GraphRectangle)
    {delta t : Real}
    (weight : alpha -> ENNReal) :
    exists selected : Finset alpha, exists owner : alpha -> alpha,
      selected ⊆ vertices ∧
      (vertices.Nonempty -> selected.Nonempty) ∧
      Set.Pairwise (selected : Set alpha)
        (fun a b =>
          ¬ compactC2SymmetricGraphLambdaComparableOn domain center
            (rectangleAt a) (rectangleAt b) delta t 100) ∧
      (forall a, a ∈ vertices -> owner a ∈ selected) ∧
      (forall a, a ∈ vertices -> owner a = a ∨
        compactC2SymmetricGraphLambdaComparableOn domain center
          (rectangleAt (owner a)) (rectangleAt a) delta t 100) ∧
      vertices.card =
        ∑ b ∈ selected, (vertices.filter fun a => owner a = b).card ∧
      (∑ a ∈ vertices, weight a) =
        ∑ b ∈ selected,
          ∑ a ∈ vertices.filter (fun a => owner a = b), weight a := by
  classical
  exact exists_maximal_pairwise_not_relation_clustering vertices
    (fun a b => compactC2SymmetricGraphLambdaComparableOn domain center
      (rectangleAt a) (rectangleAt b) delta t 100)
    ⟨fun _ _ hab => compactC2SymmetricGraphLambdaComparableOn_symm hab⟩
    weight

#print axioms exists_maximal_pairwise_not_relation_clustering
#print axioms exists_maximal_hundred_incomparable_compactC2_clustering

end

end FamilyStickyCinematicL32Lemma55FiniteMaximalIncomparableClusteringV1
