import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosFinitePairSupportSumCleanV1

/-! # Restricting a zero-extended finite pair sum to its support subtype -/

theorem sum_pair_eq_sum_support_subtype
    {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (f : α → α → Real)
    (hleft : ∀ a, a ∉ s → ∀ b, f a b = 0)
    (hright : ∀ a b, b ∉ s → f a b = 0) :
    (∑ a : α, ∑ b : α, f a b) =
      ∑ a : ↥s, ∑ b : ↥s, f a.1 b.1 := by
  classical
  calc
    (∑ a : α, ∑ b : α, f a b) =
        ∑ a ∈ s, ∑ b : α, f a b := by
      symm
      exact Finset.sum_subset (Finset.subset_univ s) fun a ha hnot => by
        simp [hleft a hnot]
    _ = ∑ a ∈ s, ∑ b ∈ s, f a b := by
      apply Finset.sum_congr rfl
      intro a ha
      symm
      exact Finset.sum_subset (Finset.subset_univ s) fun b hb hnot =>
        hright a b hnot
    _ = ∑ a : ↥s, ∑ b ∈ s, f a.1 b := by
      symm
      rw [← Finset.attach_eq_univ]
      exact Finset.sum_attach s (fun a => ∑ b ∈ s, f a b)
    _ = ∑ a : ↥s, ∑ b : ↥s, f a.1 b.1 := by
      apply Finset.sum_congr rfl
      intro a ha
      symm
      rw [← Finset.attach_eq_univ]
      exact Finset.sum_attach s (fun b => f a.1 b)

#print axioms sum_pair_eq_sum_support_subtype

end FamilyStickyCinematicL32Prop41MarcusTardosFinitePairSupportSumCleanV1
