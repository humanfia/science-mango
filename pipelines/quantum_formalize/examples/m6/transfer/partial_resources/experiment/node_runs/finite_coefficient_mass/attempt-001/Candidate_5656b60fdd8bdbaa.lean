import FrozenTarget_5656b60fdd8bdbaa
theorem M6.Transfer.finite_coefficient_mass : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (p : Polynomial ℤ) (L : ℕ), (∑ d : Fin L, (p.coeff d.val).natAbs) ≤ M6.Transfer.polynomialMass p
  intro p L
  change (∑ d : Fin L, (p.coeff d.val).natAbs) ≤ ∑ i ∈ p.support, (p.coeff i).natAbs
  rw [Fin.sum_univ_eq_sum_range]
  calc
    (∑ i ∈ Finset.range L, (p.coeff i).natAbs) ≤
        ∑ i ∈ Finset.range L ∪ p.support, (p.coeff i).natAbs := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      intro i hi hnot
      exact Nat.zero_le _
    _ = ∑ i ∈ p.support, (p.coeff i).natAbs := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro i hi hnot
      have hz : p.coeff i = 0 := by
        simpa only [Polynomial.mem_support_iff, not_not] using hnot
      simp [hz]
