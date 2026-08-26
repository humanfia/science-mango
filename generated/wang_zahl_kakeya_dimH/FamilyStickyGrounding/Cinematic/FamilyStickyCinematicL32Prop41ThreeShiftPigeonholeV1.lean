import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41Shift3TwoRootsV1

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32Prop41ThreeShiftPigeonholeV1

noncomputable section

/-!
# A uniform choice among the three PYZ perturbations

The pointwise shift lemma assigns to every retained rectangle one of the
three shifts `-1`, `0`, or `1`.  This module contains the finite combinatorial
step in PYZ Corollary 4.13: one label works for a subcollection containing at
least one third of all rectangles.

The predicate attached to a label is arbitrary.  In particular, no root,
tangency, or geometric conclusion is assumed globally.
-/

/-- The real multiplier represented by a three-shift label. -/
def threeShiftValue (k : Fin 3) : Real :=
  if k = 0 then -1 else if k = 1 then 0 else 1

theorem threeShiftValue_mem (k : Fin 3) :
    threeShiftValue k ∈ ({(-1 : Real), 0, 1} : Set Real) := by
  fin_cases k <;> simp [threeShiftValue]

/-- Every real multiplier in `{-1,0,1}` has a `Fin 3` label. -/
theorem exists_threeShiftLabel_of_mem
    {eta : Real} (heta : eta ∈ ({(-1 : Real), 0, 1} : Set Real)) :
    ∃ k : Fin 3, threeShiftValue k = eta := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at heta
  rcases heta with heta | heta | heta
  · exact ⟨0, by simp [threeShiftValue, heta]⟩
  · exact ⟨1, by simp [threeShiftValue, heta]⟩
  · exact ⟨2, by simp [threeShiftValue, heta]⟩

/-- The part of `items` assigned to one of the three shift labels. -/
def threeShiftFiber
    {alpha : Type*} [DecidableEq alpha]
    (items : Finset alpha) (label : alpha -> Fin 3) (k : Fin 3) :
    Finset alpha :=
  items.filter fun i => label i = k

@[simp] theorem mem_threeShiftFiber_iff
    {alpha : Type*} [DecidableEq alpha]
    (items : Finset alpha) (label : alpha -> Fin 3)
    (k : Fin 3) (i : alpha) :
    i ∈ threeShiftFiber items label k ↔ i ∈ items ∧ label i = k := by
  simp [threeShiftFiber]

/-- Choose one valid label for each item.  Outside `items` the value is
irrelevant and is fixed to zero. -/
def chosenThreeShiftLabel
    {alpha : Type*} [DecidableEq alpha]
    (items : Finset alpha) (good : alpha -> Fin 3 -> Prop)
    (hgood : forall i, i ∈ items -> ∃ k : Fin 3, good i k)
    (i : alpha) : Fin 3 :=
  if hi : i ∈ items then Classical.choose (hgood i hi) else 0

theorem chosenThreeShiftLabel_good
    {alpha : Type*} [DecidableEq alpha]
    (items : Finset alpha) (good : alpha -> Fin 3 -> Prop)
    (hgood : forall i, i ∈ items -> ∃ k : Fin 3, good i k)
    {i : alpha} (hi : i ∈ items) :
    good i (chosenThreeShiftLabel items good hgood i) := by
  simp only [chosenThreeShiftLabel, dif_pos hi]
  exact Classical.choose_spec (hgood i hi)

/-- One of three valid labels retains at least one third of a nonempty
finite carrier. -/
theorem exists_uniform_threeShift_fiber
    {alpha : Type*} [DecidableEq alpha]
    (items : Finset alpha) (good : alpha -> Fin 3 -> Prop)
    (hitems : items.Nonempty)
    (hgood : forall i, i ∈ items -> ∃ k : Fin 3, good i k) :
    ∃ k : Fin 3,
      let fiber := threeShiftFiber items
        (chosenThreeShiftLabel items good hgood) k
      fiber.Nonempty ∧ items.card <= 3 * fiber.card ∧
        forall i, i ∈ fiber -> good i k := by
  let label := chosenThreeShiftLabel items good hgood
  let fiberCard : Fin 3 -> Nat := fun k =>
    (threeShiftFiber items label k).card
  obtain ⟨k, _hk, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin 3)) fiberCard
      Finset.univ_nonempty
  have hcard : items.card <= 3 * fiberCard k := by
    calc
      items.card = ∑ j ∈ (Finset.univ : Finset (Fin 3)), fiberCard j := by
        change items.card = ∑ j ∈ (Finset.univ : Finset (Fin 3)),
          (items.filter fun i => label i = j).card
        exact Finset.card_eq_sum_card_fiberwise
          (fun i hi => Finset.mem_univ (label i))
      _ <= ∑ _j ∈ (Finset.univ : Finset (Fin 3)), fiberCard k := by
        apply Finset.sum_le_sum
        intro j hj
        exact hmax j hj
      _ = 3 * fiberCard k := by simp
  have hnonempty : (threeShiftFiber items label k).Nonempty := by
    by_contra hempty
    have hzero : fiberCard k = 0 := by
      simp only [fiberCard, Finset.card_eq_zero]
      exact Finset.not_nonempty_iff_eq_empty.mp hempty
    rw [hzero, mul_zero] at hcard
    exact hitems.ne_empty (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard))
  refine ⟨k, hnonempty, ?_, ?_⟩
  · simpa only [label, fiberCard] using hcard
  · intro i hi
    have hi' := (mem_threeShiftFiber_iff items label k i).mp hi
    have hchosen := chosenThreeShiftLabel_good items good hgood hi'.1
    simpa only [label, hi'.2] using hchosen

#print axioms threeShiftValue_mem
#print axioms exists_threeShiftLabel_of_mem
#print axioms exists_uniform_threeShift_fiber

end

end FamilyStickyCinematicL32Prop41ThreeShiftPigeonholeV1
