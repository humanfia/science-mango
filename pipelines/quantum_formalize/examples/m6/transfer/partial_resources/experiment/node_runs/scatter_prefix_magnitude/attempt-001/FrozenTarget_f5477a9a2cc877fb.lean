import M6TransferPartialResourcesReady

theorem M6.Transfer.finite_coefficient_mass : ∀ (p : Polynomial ℤ) (L : ℕ), (∑ d : Fin L, (p.coeff d.val).natAbs) ≤ M6.Transfer.polynomialMass p := by
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

theorem M6.Transfer.event_mass_bound : ∀ (R N : ℕ) (W : M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (input : M6.Transfer.CoefficientArray R N), (∀ m t, M6.Transfer.polynomialMass (W m t) ≤ 4) → M6.Transfer.eventMass W input ≤ 8 * M6.Transfer.arrayMass input := by
  classical
  change ∀ (R N : ℕ) (W : M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (input : M6.Transfer.CoefficientArray R N), (∀ m t, M6.Transfer.polynomialMass (W m t) ≤ 4) → M6.Transfer.eventMass W input ≤ 8 * M6.Transfer.arrayMass input
  intro R N W input hW
  unfold M6.Transfer.eventMass M6.Transfer.arrayMass
  simp only [M6.Transfer.ScatterEvent, M6.Transfer.CoefficientAddress,
    Fintype.sum_prod_type, M6.Transfer.eventTerm, Int.natAbs_mul]
  calc
    _ ≤ ∑ m : M6.Transfer.Memory R, ∑ t : M6.Transfer.Bit,
        ∑ i : Fin (2 * N + 1), (input (m, i)).natAbs * 4 := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro t ht
      apply Finset.sum_le_sum
      intro i hi
      rw [← Finset.mul_sum]
      exact Nat.mul_le_mul_left _
        ((M6.Transfer.finite_coefficient_mass (W m t) 3).trans (hW m t))
    _ = _ := by
      simp [M6.Transfer.Bit, ← Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] <;> ring
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (R N : ℕ) (W : M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (input : M6.Transfer.CoefficientArray R N) (k : ℕ) (addr : M6.Transfer.CoefficientAddress R N), (∀ m t, M6.Transfer.polynomialMass (W m t) ≤ 4) → (((M6.Transfer.scatterEventList R N).take k).foldl (M6.Transfer.scatterUpdate W input) (fun _ => 0) addr).natAbs ≤ 8 * M6.Transfer.arrayMass input
