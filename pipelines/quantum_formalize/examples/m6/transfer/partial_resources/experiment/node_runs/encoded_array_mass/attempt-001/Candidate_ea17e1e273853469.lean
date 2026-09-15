import FrozenTarget_ea17e1e273853469
theorem M6.Transfer.encoded_array_mass : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (R N : ℕ) (v : M6.Transfer.Memory R → Polynomial ℤ), M6.Transfer.arrayMass (M6.Transfer.encodeCoefficients (N := N) v) ≤ M6.Transfer.rowMass v
  intro R N v
  change (∑ addr : M6.Transfer.Memory R × Fin (2 * N + 1), ((v addr.1).coeff addr.2.val).natAbs) ≤ ∑ m : M6.Transfer.Memory R, M6.Transfer.polynomialMass (v m)
  rw [Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro m hm
  exact M6.Transfer.finite_coefficient_mass (v m) (2 * N + 1)
