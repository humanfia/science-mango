import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosSigmaDiagonalSumCleanV1

/-!
# Diagonal fibre decomposition for a finite dependent sum

This is the purely finite reindexing used when a common symbol is assigned
to its unique pair of blocks.  It contains no cyclic-order input.
-/

theorem sum_sigma_same_fibre
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (fibre : ι → α → Prop)
    [∀ i, DecidablePred (fibre i)] [∀ i, Fintype {a : α // fibre i a}]
    (g : α → α → Real) :
    (∑ x : Σ i, {a : α // fibre i a},
      ∑ y : Σ i, {a : α // fibre i a},
        if x.1 = y.1 then g x.2.1 y.2.1 else 0) =
      ∑ i : ι, ∑ x : {a : α // fibre i a},
        ∑ y : {a : α // fibre i a}, g x.1 y.1 := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro x hx
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [Ne.symm hji]
  · intro hi'
    exact (hi' (Finset.mem_univ i)).elim

#print axioms sum_sigma_same_fibre

end FamilyStickyCinematicL32Prop41MarcusTardosSigmaDiagonalSumCleanV1
