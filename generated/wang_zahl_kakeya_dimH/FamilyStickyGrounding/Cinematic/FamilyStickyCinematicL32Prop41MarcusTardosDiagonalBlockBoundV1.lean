import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosDiagonalBlockBoundV1

/-!
# Equal-block diagonal estimate in Marcus--Tardos Lemma 4

At depth `l`, the almost-equal blocks satisfy
`blockSize - 1 ≤ d / 2^l`.  Since their sizes sum to `d`, their ordered
within-block pair count is at most `d² / 2^l`.  The theorem below isolates
exactly this calculation.
-/

theorem sum_size_mul_pred_le_sq_div
    {block : Type*} [Fintype block]
    (size : block → Real) (d parts : Real)
    (hsize : ∀ b, 0 ≤ size b)
    (hsum : (∑ b, size b) = d)
    (halmost : ∀ b, size b - 1 ≤ d / parts) :
    (∑ b, size b * (size b - 1)) ≤ d ^ 2 / parts := by
  calc
    (∑ b, size b * (size b - 1)) ≤
        ∑ b, size b * (d / parts) := by
      exact Finset.sum_le_sum fun b _ ↦
        mul_le_mul_of_nonneg_left (halmost b) (hsize b)
    _ = d * (d / parts) := by rw [← Finset.sum_mul, hsum]
    _ = d ^ 2 / parts := by ring

/-- Weighted one-level version used after inserting `parts = 2^l`. -/
theorem weight_mul_sum_size_mul_pred_le
    {block : Type*} [Fintype block]
    (size : block → Real) (d parts weight : Real)
    (hweight : 0 ≤ weight)
    (hsize : ∀ b, 0 ≤ size b)
    (hsum : (∑ b, size b) = d)
    (halmost : ∀ b, size b - 1 ≤ d / parts) :
    weight * (∑ b, size b * (size b - 1)) ≤
      d ^ 2 * (weight / parts) := by
  calc
    weight * (∑ b, size b * (size b - 1)) ≤
        weight * (d ^ 2 / parts) :=
      mul_le_mul_of_nonneg_left
        (sum_size_mul_pred_le_sq_div size d parts hsize hsum halmost)
        hweight
    _ = d ^ 2 * (weight / parts) := by ring

#print axioms sum_size_mul_pred_le_sq_div
#print axioms weight_mul_sum_size_mul_pred_le

end FamilyStickyCinematicL32Prop41MarcusTardosDiagonalBlockBoundV1
