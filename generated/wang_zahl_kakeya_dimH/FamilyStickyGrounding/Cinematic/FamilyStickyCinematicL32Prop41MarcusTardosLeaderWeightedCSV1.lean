import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosLeaderWeightedCSV1

/-!
# The weighted leader Cauchy--Schwarz kernel in Marcus--Tardos Lemma 5

This module isolates the finite algebra used after leaders have been selected.
It does not assume the geometric/block assertion that supplies those leaders.
-/

/-- Weighted Cauchy--Schwarz in the exact form used for leader multiplicities:
the total squared mass is controlled by weighted square mass times reciprocal
weight mass. -/
theorem sum_sq_le_weightedSquare_mul_reciprocal
    {leader : Type*} [DecidableEq leader]
    (s : Finset leader) (weight mass : leader → Real)
    (hweight : ∀ i ∈ s, 0 < weight i) :
    (∑ i ∈ s, mass i) ^ 2 ≤
      (∑ i ∈ s, weight i * mass i ^ 2) *
        ∑ i ∈ s, (weight i)⁻¹ := by
  have hnonneg : ∀ i ∈ s, 0 ≤ weight i * mass i ^ 2 := by
    intro i hi
    exact mul_nonneg (hweight i hi).le (sq_nonneg _)
  have hinv : ∀ i ∈ s, 0 ≤ (weight i)⁻¹ := by
    intro i hi
    exact inv_nonneg.mpr (hweight i hi).le
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s hnonneg hinv ?_
  intro i hi
  have hw : weight i * (weight i)⁻¹ = 1 :=
    mul_inv_cancel₀ (hweight i hi).ne'
  have heq : mass i ^ 2 =
      (weight i * mass i ^ 2) * (weight i)⁻¹ := by
    calc
      mass i ^ 2 = mass i ^ 2 * 1 := by ring
      _ = mass i ^ 2 * (weight i * (weight i)⁻¹) := by rw [hw]
      _ = (weight i * mass i ^ 2) * (weight i)⁻¹ := by ring
  exact heq.le

/-- If the reciprocal-weight mass is at most `4V`, the paper's factor-four
lower bound follows without division. -/
theorem sum_mass_sq_le_four_mul_weightedSquare_mul
    {leader : Type*} [DecidableEq leader]
    (s : Finset leader) (weight mass : leader → Real) (V : Real)
    (hweight : ∀ i ∈ s, 0 < weight i)
    (hreciprocal : ∑ i ∈ s, (weight i)⁻¹ ≤ 4 * V) :
    (∑ i ∈ s, mass i) ^ 2 ≤
      4 * V * ∑ i ∈ s, weight i * mass i ^ 2 := by
  have hweighted : 0 ≤ ∑ i ∈ s, weight i * mass i ^ 2 := by
    exact Finset.sum_nonneg fun i hi ↦
      mul_nonneg (hweight i hi).le (sq_nonneg _)
  calc
    (∑ i ∈ s, mass i) ^ 2 ≤
        (∑ i ∈ s, weight i * mass i ^ 2) *
          ∑ i ∈ s, (weight i)⁻¹ :=
      sum_sq_le_weightedSquare_mul_reciprocal s weight mass hweight
    _ ≤ (∑ i ∈ s, weight i * mass i ^ 2) * (4 * V) := by
      exact mul_le_mul_of_nonneg_left hreciprocal hweighted
    _ = 4 * V * ∑ i ∈ s, weight i * mass i ^ 2 := by ring

#print axioms sum_sq_le_weightedSquare_mul_reciprocal
#print axioms sum_mass_sq_le_four_mul_weightedSquare_mul

end FamilyStickyCinematicL32Prop41MarcusTardosLeaderWeightedCSV1
