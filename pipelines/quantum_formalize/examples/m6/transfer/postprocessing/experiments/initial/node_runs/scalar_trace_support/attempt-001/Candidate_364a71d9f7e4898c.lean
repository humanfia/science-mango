import FrozenTarget_364a71d9f7e4898c
theorem M6.ActualTransfer.scalar_trace_support : QuantumHarnessFrozenTarget := by
  intro R N W d hd
  classical
  unfold M6.Transfer.scalarTracePolynomial
  rw [Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  have hne : (i : ℕ) ≠ d := by
    have hi_lt := i.isLt
    omega
  simp [Polynomial.coeff_monomial, hne]
