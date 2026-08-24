import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosTripleSublistBridgeV1
import Mathlib.Data.List.Sort
import Mathlib.Tactic

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosTripleLinearOrderV1

open List
open FamilyStickyCinematicL32Prop41MarcusTardosTripleSublistBridgeV1

/-! # Finite two-symbol order in a nodup list -/

/-- Two distinct members of a finite list occur in one of the two possible
linear orders. -/
theorem pair_sublist_or_swap_of_mem_of_ne
    {symbol : Type*} [DecidableEq symbol]
    {a b : symbol} {l : List symbol}
    (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    [a, b] <+ l ∨ [b, a] <+ l := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
      simp only [List.mem_cons] at ha hb
      rcases ha with hax | ha
      · subst x
        rcases hb with hba | hb
        · exact False.elim (hab hba.symm)
        · exact Or.inl ((List.singleton_sublist.mpr hb).cons_cons a)
      · rcases hb with hbx | hb
        · subst x
          exact Or.inr ((List.singleton_sublist.mpr ha).cons_cons b)
        · exact (ih ha hb).imp (Sublist.cons x) (Sublist.cons x)

/-- A nodup target list is uniquely determined among its permutations by
the order of every literal two-element sublist. -/
theorem eq_of_perm_of_pair_sublist
    {symbol : Type*} [DecidableEq symbol]
    {target candidate : List symbol}
    (htarget : target.Nodup)
    (hperm : target ~ candidate)
    (horder : ∀ {a b}, [a, b] <+ candidate -> [a, b] <+ target) :
    target = candidate := by
  let R : symbol -> symbol -> Prop := fun a b =>
    a = b ∨ [a, b] <+ target
  have htargetR : target.Pairwise R := by
    apply List.pairwise_of_forall_sublist
    intro a b hab
    exact Or.inr hab
  have hcandidateR : candidate.Pairwise R := by
    apply List.pairwise_of_forall_sublist
    intro a b hab
    exact Or.inr (horder hab)
  apply hperm.eq_of_pairwise (le := R) _ htargetR hcandidateR
  intro a b ha hb hab hba
  rcases hab with hab | hab
  · exact hab
  rcases hba with hba | hba
  · exact hba.symm
  have hfilterAB := filter_toFinset_eq_of_sublist_of_nodup hab htarget
  have hfilterBA := filter_toFinset_eq_of_sublist_of_nodup hba htarget
  have hsupport : ([a, b] : List symbol).toFinset = [b, a].toFinset := by
    ext x
    simp [or_comm]
  rw [hsupport] at hfilterAB
  have hpair : [a, b] = [b, a] := hfilterAB.symm.trans hfilterBA
  simpa using congrArg List.head? hpair

#print axioms pair_sublist_or_swap_of_mem_of_ne
#print axioms eq_of_perm_of_pair_sublist

end FamilyStickyCinematicL32Prop41MarcusTardosTripleLinearOrderV1
