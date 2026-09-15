import FrozenTarget_92dfc6bcce2cac52
theorem M6.Transfer.trace_coefficient_bound : QuantumHarnessFrozenTarget := by
  change ∀ (R N : ℕ) (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (d : ℕ), (∀ i m t, M6.Transfer.polynomialMass (W i m t) ≤ 4) → ((M6.Transfer.arrayTrace W N).coeff d).natAbs ≤ 2 ^ R * 8 ^ N
  intro R N W d hW
  classical
  have hc : Fintype.card (M6.Transfer.Memory R) = 2 ^ R := by
    simp [M6.Transfer.Memory, M6.Transfer.Bit]
  calc
    ((M6.Transfer.arrayTrace W N).coeff d).natAbs
        ≤ M6.Transfer.polynomialMass (M6.Transfer.arrayTrace W N) :=
      M6.Transfer.mass_basic.2.2.2 _ d
    _ ≤ ∑ start : M6.Transfer.Memory R,
        M6.Transfer.polynomialMass (M6.Transfer.layers W start N start) := by
      unfold M6.Transfer.arrayTrace
      exact M6.Transfer.mass_sum _ Finset.univ _
    _ ≤ ∑ start : M6.Transfer.Memory R, 8 ^ N := by
      apply Finset.sum_le_sum
      intro start hstart
      have hd : M6.Transfer.polynomialMass (M6.Transfer.layers W start N start) ≤
          M6.Transfer.rowMass (M6.Transfer.layers W start N) := by
        unfold M6.Transfer.rowMass
        exact Finset.single_le_sum
          (fun m _ => Nat.zero_le (M6.Transfer.polynomialMass (M6.Transfer.layers W start N m)))
          (Finset.mem_univ start)
      exact hd.trans (M6.Transfer.layers_mass R W start N hW)
    _ = 2 ^ R * 8 ^ N := by
      simp only [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul]
