import FrozenTarget_a07763490d902c42
theorem M6.Transfer.event_mass_bound : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (R N : ℕ) (W : M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ)
      (input : M6.Transfer.CoefficientArray R N),
      (∀ m t, M6.Transfer.polynomialMass (W m t) ≤ 4) →
      M6.Transfer.eventMass W input ≤ 8 * M6.Transfer.arrayMass input
  intro R N W input hW
  unfold M6.Transfer.eventMass M6.Transfer.arrayMass
  simp only [M6.Transfer.ScatterEvent, M6.Transfer.CoefficientAddress,
    Fintype.sum_prod_type, M6.Transfer.eventTerm, Int.natAbs_mul]
  calc
    _ ≤ ∑ m : M6.Transfer.Memory R, ∑ t : M6.Transfer.Bit,
        ∑ d : Fin (2 * N + 1), (input (m, d)).natAbs * 4 := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro t ht
      apply Finset.sum_le_sum
      intro d hd
      rw [← Finset.mul_sum]
      exact Nat.mul_le_mul_left _
        ((M6.Transfer.finite_coefficient_mass (W m t) 3).trans (hW m t))
    _ = _ := by
      simp [M6.Transfer.Bit, ← Finset.sum_mul, ← Finset.mul_sum,
        mul_comm, mul_left_comm, mul_assoc]
