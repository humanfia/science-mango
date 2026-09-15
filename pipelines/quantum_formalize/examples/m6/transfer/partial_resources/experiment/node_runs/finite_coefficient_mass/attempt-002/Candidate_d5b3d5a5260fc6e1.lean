import FrozenTarget_d5b3d5a5260fc6e1
theorem M6.Transfer.finite_coefficient_mass : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (p : Polynomial ℤ) (L : ℕ), (∑ d : Fin L, (p.coeff d.val).natAbs) ≤ M6.Transfer.polynomialMass p
  intro p L
  change (∑ d : Fin L, (p.coeff d.val).natAbs) ≤ ∑ d ∈ p.support, (p.coeff d).natAbs
  have hfin : (∑ d : Fin L, (p.coeff d.val).natAbs) = ∑ d ∈ Finset.range L, (p.coeff d).natAbs :=
    Fin.sum_univ_eq_sum_range (fun d : ℕ => (p.coeff d).natAbs) L
  rw [hfin]
  calc
    (∑ d ∈ Finset.range L, (p.coeff d).natAbs) ≤
        ∑ d ∈ p.support ∪ Finset.range L, (p.coeff d).natAbs := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_union_right
      · intros
        exact Nat.zero_le _
    _ = ∑ d ∈ p.support, (p.coeff d).natAbs := by
      symm
      apply Finset.sum_subset Finset.subset_union_left
      intro d hd hnot
      have hz : p.coeff d = 0 := by
        simpa only [Polynomial.mem_support_iff, not_not] using hnot
      simp [hz]
