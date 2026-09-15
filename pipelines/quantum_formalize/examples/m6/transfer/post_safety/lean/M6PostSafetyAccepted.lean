import M6PostSafety

theorem M6.Transfer.division_difference_fits : ∀ (R N : ℕ) (z w : ℤ) (j k : ℕ), z.natAbs ≤ 2^R*8^N → w.natAbs ≤ 2^R*8^N → (z/(2:ℤ)^j - w/(2:ℤ)^k).natAbs < 2^(M6.Transfer.queryCoefficientBits R N - 1) := by
  change ∀ (R N : ℕ) (z w : ℤ) (j k : ℕ), z.natAbs ≤ 2^R*8^N → w.natAbs ≤ 2^R*8^N → (z/(2:ℤ)^j - w/(2:ℤ)^k).natAbs < 2^(M6.Transfer.queryCoefficientBits R N - 1)
  intro R N z w j k hz hw
  have hz' := Int.natAbs_ediv_le_natAbs z ((2 : ℤ)^j)
  have hw' := Int.natAbs_ediv_le_natAbs w ((2 : ℤ)^k)
  have htri : (z/(2:ℤ)^j - w/(2:ℤ)^k).natAbs ≤
      (z/(2:ℤ)^j).natAbs + (w/(2:ℤ)^k).natAbs := by
    simpa only [sub_eq_add_neg, Int.natAbs_neg] using
      (Int.natAbs_add_le (z/(2:ℤ)^j) (-(w/(2:ℤ)^k)))
  have hbound : (z/(2:ℤ)^j - w/(2:ℤ)^k).natAbs ≤ 2 * (2^R*8^N) := by
    omega
  have hcap := M6.Transfer.actual_signed_capacity R N
  have hdouble : 2 * (2^R*8^N) < 2^((M6.Transfer.coefficientBits R N - 1) + 1) := by
    rw [pow_succ]
    omega
  have hexp : (M6.Transfer.coefficientBits R N - 1) + 1 ≤
      M6.Transfer.queryCoefficientBits R N - 1 := by
    unfold M6.Transfer.queryCoefficientBits
    omega
  have hpow : (2 : ℕ)^((M6.Transfer.coefficientBits R N - 1) + 1) ≤
      2^(M6.Transfer.queryCoefficientBits R N - 1) :=
    Nat.pow_le_pow_right (by decide) hexp
  exact lt_of_le_of_lt hbound (lt_of_lt_of_le hdouble hpow)

theorem M6.ActualTransfer.query_coefficients_fit : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (P : M6.Pinned.Pins (2*N)) (d : ℕ), ((M6.ActualTransfer.Q N a b P).coeff d).natAbs < 2^(M6.Transfer.queryCoefficientBits (M6.ActualTransfer.span a b) N - 1) := by
  change ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (P : M6.Pinned.Pins (2*N)) (d : ℕ), ((M6.ActualTransfer.Q N a b P).coeff d).natAbs < 2^(M6.Transfer.queryCoefficientBits (M6.ActualTransfer.span a b) N - 1)
  intro N inst a b P d
  have hb : ((M6.ActualTransfer.boundaryTrace N a b P).coeff d).natAbs ≤ 2^(M6.ActualTransfer.span a b) * 8^N := by
    have hdeg : ∀ i m t, (M6.ActualTransfer.boundaryWeight (M6.ActualTransfer.span a b) N a b P i m t).natDegree ≤ 2 := by
      intro i m t
      exact (M6.Transfer.boundary_edge_bounds _ _ _ _ _ _).2
    unfold M6.ActualTransfer.boundaryTrace
    rw [M6.Transfer.scalar_trace_polynomial _ _ _ hdeg]
    apply M6.Transfer.trace_coefficient_bound
    intro i m t
    exact (M6.Transfer.boundary_edge_bounds _ _ _ _ _ _).1
  have hc : ((M6.ActualTransfer.characterTrace N a b P).coeff d).natAbs ≤ 2^(M6.ActualTransfer.span a b) * 8^N := by
    have hdeg : ∀ i m t, (M6.ActualTransfer.characterWeight (M6.ActualTransfer.span a b) N a b P i m t).natDegree ≤ 2 := by
      intro i m t
      exact (M6.Transfer.character_edge_bounds _ _ _ _ _ _).2
    unfold M6.ActualTransfer.characterTrace
    rw [M6.Transfer.scalar_trace_polynomial _ _ _ hdeg]
    apply M6.Transfer.trace_coefficient_bound
    intro i m t
    exact (M6.Transfer.character_edge_bounds _ _ _ _ _ _).1
  unfold M6.ActualTransfer.Q
  simp only [Polynomial.coeff_sub, M6.Normalize.divide_coeff]
  apply M6.Transfer.division_difference_fits <;> assumption
#print axioms M6.Transfer.division_difference_fits
#print axioms M6.ActualTransfer.query_coefficients_fit
