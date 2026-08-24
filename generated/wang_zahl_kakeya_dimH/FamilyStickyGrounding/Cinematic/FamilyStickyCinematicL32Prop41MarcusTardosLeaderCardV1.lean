import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosLeaderCardV1

/-!
# The four-leader finite kernel in Marcus--Tardos Lemma 5

At a fixed positive dyadic depth, a leader child has a singular parent.
Lemma 2 supplies at most one singular parent pair, while binary subdivision
gives at most four child pairs over that parent.  This module proves the
cardinality implication abstractly; producing the singular-parent theorem
from intersection-reversed cyclic lists remains a separate obligation.
-/

/-- Children which are regular but whose parent is singular. -/
def leaderChildren
    {parent child : Type*} [Fintype child]
    [DecidableEq child]
    (parentOf : child → parent)
    (parentRegular : parent → Prop) [DecidablePred parentRegular]
    (childRegular : child → Prop) [DecidablePred childRegular] :
    Finset child :=
  Finset.univ.filter fun c => childRegular c ∧ ¬parentRegular (parentOf c)

/-- “At most one singular parent” plus “at most four children over a parent”
implies at most four leaders at the next depth. -/
theorem leaderChildren_card_le_four
    {parent child : Type*} [Fintype parent] [Fintype child]
    [DecidableEq parent] [DecidableEq child]
    (parentOf : child → parent)
    (parentRegular : parent → Prop) [DecidablePred parentRegular]
    (childRegular : child → Prop) [DecidablePred childRegular]
    (hsingular :
      ((Finset.univ : Finset parent).filter fun p => ¬parentRegular p).card ≤ 1)
    (hfour : ∀ p : parent,
      ((Finset.univ : Finset child).filter fun c => parentOf c = p).card ≤ 4) :
    (leaderChildren parentOf parentRegular childRegular).card ≤ 4 := by
  classical
  let singular : Finset parent :=
    (Finset.univ : Finset parent).filter fun p => ¬parentRegular p
  by_cases hempty : singular.Nonempty
  · obtain ⟨p, hp⟩ := hempty
    have hunique : ∀ q ∈ singular, q = p := by
      intro q hq
      exact (Finset.card_le_one.mp hsingular) q hq p hp
    have hsub : leaderChildren parentOf parentRegular childRegular ⊆
        (Finset.univ : Finset child).filter fun c => parentOf c = p := by
      intro c hc
      simp only [leaderChildren, Finset.mem_filter, Finset.mem_univ,
        true_and] at hc ⊢
      exact hunique (parentOf c) (by
        simp only [singular, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hc.2)
    exact (Finset.card_le_card hsub).trans (hfour p)
  · have hnot : ¬(leaderChildren parentOf parentRegular childRegular).Nonempty := by
      rintro ⟨c, hc⟩
      apply hempty
      refine ⟨parentOf c, ?_⟩
      simp only [singular, Finset.mem_filter, Finset.mem_univ, true_and]
      have hc' : childRegular c ∧ ¬parentRegular (parentOf c) := by
        simpa [leaderChildren] using hc
      exact hc'.2
    have hzero : leaderChildren parentOf parentRegular childRegular = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnot
    simp [hzero]

/-- The first dyadic depth has four block pairs, so any selected subfamily
there also has cardinal at most four. -/
theorem firstLevel_le_four_of_ambient
    {node : Type*} [Fintype node] [DecidableEq node]
    (selected : Finset node) (hambient : Fintype.card node ≤ 4) :
    selected.card ≤ 4 := by
  calc
    selected.card ≤ (Finset.univ : Finset node).card :=
      Finset.card_le_card (Finset.subset_univ selected)
    _ = Fintype.card node := Finset.card_univ
    _ ≤ 4 := hambient

#print axioms leaderChildren
#print axioms leaderChildren_card_le_four
#print axioms firstLevel_le_four_of_ambient

end FamilyStickyCinematicL32Prop41MarcusTardosLeaderCardV1
