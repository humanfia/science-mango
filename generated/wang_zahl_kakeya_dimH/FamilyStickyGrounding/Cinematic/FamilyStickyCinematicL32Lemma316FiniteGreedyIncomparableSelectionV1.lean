import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32ThinReferenceCompactDomainC2BallV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55CompactC2SymmetricComparabilityV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators ENNReal

namespace FamilyStickyCinematicL32Lemma316FiniteGreedyIncomparableSelectionV1

noncomputable section

/-!
# Finite greedy incomparable selection

This is the finite combinatorial core of PYZ Lemmas 5.5 and 3.16.  At
each stage choose a remaining object of largest mass, retain it, and delete
its closed comparability neighbourhood.  A uniform bound `B` for those
neighbourhoods gives both cardinality and mass loss at most `B`.

The theorem is deliberately relation-generic.  The final rectangle adapter
below isolates the one geometric input still needed from Lemmas 3.12/3.15:
the `C`-comparability neighbourhood of a `100`-incomparable rectangle family
has uniformly bounded cardinality.
-/

universe u

/-- A largest-mass greedy independent subfamily.  The same selected family
simultaneously preserves cardinality and arbitrary nonnegative `ENNReal`
mass up to the closed-neighbourhood bound `B`. -/
theorem exists_greedy_pairwise_not_relation
    {alpha : Type u} [DecidableEq alpha]
    (vertices : Finset alpha)
    (comparable : alpha -> alpha -> Prop) [DecidableRel comparable]
    (hsymm : Std.Symm comparable)
    (weight : alpha -> ENNReal) (B : ENNReal)
    (hneighbour : forall a, a ∈ vertices ->
      ((vertices.filter fun b => b = a ∨ comparable a b).card : ENNReal) <= B) :
    exists selected : Finset alpha,
      selected ⊆ vertices ∧
      (vertices.Nonempty -> selected.Nonempty) ∧
      Set.Pairwise (selected : Set alpha) (fun a b => ¬ comparable a b) ∧
      (vertices.card : ENNReal) <= B * (selected.card : ENNReal) ∧
      (∑ a ∈ vertices, weight a) <= B * ∑ a ∈ selected, weight a := by
  classical
  have aux : forall s : Finset alpha, s ⊆ vertices ->
      exists selected : Finset alpha,
        selected ⊆ s ∧
        (s.Nonempty -> selected.Nonempty) ∧
        Set.Pairwise (selected : Set alpha) (fun a b => ¬ comparable a b) ∧
        (s.card : ENNReal) <= B * (selected.card : ENNReal) ∧
        (∑ a ∈ s, weight a) <= B * ∑ a ∈ selected, weight a := by
    intro s hsvertices
    induction s using Finset.strongInduction with
    | H s ih =>
      by_cases hs : s.Nonempty
      · obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image s weight hs
        let neighbour := s.filter fun b => b = a ∨ comparable a b
        let rest := s.filter fun b => ¬ (b = a ∨ comparable a b)
        have haNeighbour : a ∈ neighbour := by
          simp [neighbour, ha]
        have haNotRest : a ∉ rest := by
          simp [rest]
        have hrestStrict : rest ⊂ s := by
          rw [Finset.filter_ssubset]
          exact ⟨a, ha, by simp⟩
        have hrestVertices : rest ⊆ vertices :=
          (Finset.filter_subset _ _).trans hsvertices
        obtain ⟨selectedRest, hselectedRest, _hselectedRestNonempty, hpairRest,
            hcardRest, hmassRest⟩ := ih rest hrestStrict hrestVertices
        have haNotSelected : a ∉ selectedRest := fun hmem =>
          haNotRest (hselectedRest hmem)
        have hneighbourSubset : neighbour ⊆
            vertices.filter fun b => b = a ∨ comparable a b := by
          intro b hb
          have hbData := Finset.mem_filter.mp hb
          exact Finset.mem_filter.mpr
            ⟨hsvertices hbData.1, hbData.2⟩
        have hneighbourSubsetCard :
            (neighbour.card : ENNReal) <=
              ((vertices.filter fun b => b = a ∨ comparable a b).card : ENNReal) := by
          exact_mod_cast Finset.card_le_card hneighbourSubset
        have hneighbourCard : (neighbour.card : ENNReal) <= B :=
          hneighbourSubsetCard.trans (hneighbour a (hsvertices ha))
        have hneighbourMass :
            (∑ b ∈ neighbour, weight b) <= B * weight a := by
          calc
            (∑ b ∈ neighbour, weight b) <=
                neighbour.card • weight a :=
              Finset.sum_le_card_nsmul neighbour weight (weight a)
                (fun b hb => hmax b (Finset.filter_subset _ _ hb))
            _ = (neighbour.card : ENNReal) * weight a := by
              simp [nsmul_eq_mul]
            _ <= B * weight a := by gcongr
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
        refine ⟨insert a selectedRest, ?_, ?_, hpairSelected, ?_, ?_⟩
        · intro b hb
          rcases Finset.mem_insert.mp hb with rfl | hb
          · exact ha
          · exact (Finset.filter_subset _ _ (hselectedRest hb))
        · intro _hs
          exact Finset.insert_nonempty a selectedRest
        · have hsplitCard : s.card = neighbour.card + rest.card := by
            simpa [neighbour, rest, Nat.add_comm] using
              (Finset.card_filter_add_card_filter_not
                (s := s) (p := fun b => b = a ∨ comparable a b)).symm
          rw [hsplitCard, Finset.card_insert_of_notMem haNotSelected]
          push_cast
          calc
            (neighbour.card : ENNReal) + (rest.card : ENNReal) <=
                B + B * (selectedRest.card : ENNReal) :=
              add_le_add hneighbourCard hcardRest
            _ = B * (1 + (selectedRest.card : ENNReal)) := by ring
            _ = B * ((selectedRest.card : ENNReal) + 1) := by
              rw [add_comm]
        · have hsplitMass :
              (∑ b ∈ s, weight b) =
                (∑ b ∈ neighbour, weight b) +
                  ∑ b ∈ rest, weight b := by
            simpa [neighbour, rest] using
              (Finset.sum_filter_add_sum_filter_not s
                (fun b => b = a ∨ comparable a b) weight).symm
          rw [hsplitMass]
          calc
            (∑ b ∈ neighbour, weight b) +
                ∑ b ∈ rest, weight b <=
              B * weight a + B * ∑ b ∈ selectedRest, weight b :=
                add_le_add hneighbourMass hmassRest
            _ = B * (weight a + ∑ b ∈ selectedRest, weight b) := by
              rw [mul_add]
            _ = B * ∑ b ∈ insert a selectedRest, weight b := by
              rw [Finset.sum_insert haNotSelected]
      · have hsEmpty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        subst s
        exact ⟨∅, by simp, by simp, by simp, by simp, by simp⟩
  exact aux vertices Finset.Subset.rfl

#print axioms exists_greedy_pairwise_not_relation

end

end FamilyStickyCinematicL32Lemma316FiniteGreedyIncomparableSelectionV1
