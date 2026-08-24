import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosDegreeNumericsV1
import Mathlib

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosPerfectSquareV1

open FamilyStickyCinematicL32Prop41MarcusTardosDegreeNumericsV1

/-!
# Perfect-square core of Marcus--Tardos Lemma 4

For fixed symbol pair and dyadic depth, the sum over all ordered list pairs
is a square.  Summing these Gram kernels against nonnegative weights remains
nonnegative; deleting the diagonal therefore costs at most the diagonal.
-/

/-- The elementary all-pairs factorization. -/
theorem sum_sum_mul_eq_sum_sq
    {index : Type*} [Fintype index]
    (x : index → Real) :
    (∑ i, ∑ j, x i * x j) = (∑ i, x i) ^ 2 := by
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, pow_two]

/-- A finite nonnegative weighted sum of all-pairs Gram kernels is
nonnegative. -/
theorem weighted_allPairs_nonneg
    {index feature : Type*} [Fintype index] [Fintype feature]
    (weight : feature → Real) (term : index → feature → Real)
    (hweight : ∀ q, 0 ≤ weight q) :
    0 ≤ ∑ i, ∑ j, ∑ q, weight q * term i q * term j q := by
  calc
    0 ≤ ∑ q, weight q * (∑ i, term i q) ^ 2 := by
      exact Finset.sum_nonneg fun q _ ↦
        mul_nonneg (hweight q) (sq_nonneg _)
    _ = ∑ q, weight q * (∑ i, ∑ j, term i q * term j q) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [sum_sum_mul_eq_sum_sq]
    _ = ∑ i, ∑ j, ∑ q, weight q * term i q * term j q := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro q _
      ring

/-- Off-diagonal Gram mass is bounded below by minus the diagonal mass. -/
theorem weighted_offDiag_ge_neg_diagonal
    {index feature : Type*} [Fintype index] [Fintype feature]
    [DecidableEq index]
    (weight : feature → Real) (term : index → feature → Real)
    (hweight : ∀ q, 0 ≤ weight q) :
    -(∑ i, ∑ q, weight q * term i q ^ 2) ≤
      ∑ ij ∈ orderedDistinctPairs index,
        ∑ q, weight q * term ij.1 q * term ij.2 q := by
  have hall := weighted_allPairs_nonneg weight term hweight
  have hsplit :
      (∑ i, ∑ j, ∑ q, weight q * term i q * term j q) =
        (∑ i, ∑ q, weight q * term i q ^ 2) +
          ∑ ij ∈ orderedDistinctPairs index,
            ∑ q, weight q * term ij.1 q * term ij.2 q := by
    classical
    simp only [orderedDistinctPairs]
    rw [← Finset.sum_product']
    rw [← Finset.diag_union_offDiag]
    rw [Finset.sum_union (Finset.disjoint_diag_offDiag _)]
    rw [Finset.sum_diag]
    simp [pow_two, mul_assoc]
  rw [hsplit] at hall
  linarith

/-- Connector to the paper's explicit diagonal estimate. -/
theorem weighted_offDiag_ge_neg_budget
    {index feature : Type*} [Fintype index] [Fintype feature]
    [DecidableEq index]
    (weight : feature → Real) (term : index → feature → Real)
    (budget : Real) (hweight : ∀ q, 0 ≤ weight q)
    (hdiag : (∑ i, ∑ q, weight q * term i q ^ 2) ≤ budget) :
    -budget ≤ ∑ ij ∈ orderedDistinctPairs index,
      ∑ q, weight q * term ij.1 q * term ij.2 q := by
  exact (neg_le_neg hdiag).trans
    (weighted_offDiag_ge_neg_diagonal weight term hweight)

#print axioms sum_sum_mul_eq_sum_sq
#print axioms weighted_allPairs_nonneg
#print axioms weighted_offDiag_ge_neg_diagonal
#print axioms weighted_offDiag_ge_neg_budget

end FamilyStickyCinematicL32Prop41MarcusTardosPerfectSquareV1
