import FrozenTarget_f395d21934be5522
theorem M6.ActualTransfer.shifted_output_exact : QuantumHarnessFrozenTarget := by
  intro N inst a b P
  classical
  have hsupport : ∀ d, 2 * N < d → (M6.ActualTransfer.Q N a b P).coeff d = 0 := by
    intro d hd
    simp [M6.ActualTransfer.Q, Polynomial.coeff_sub,
      M6.Normalize.divide_coeff, M6.ActualTransfer.boundaryTrace,
      M6.ActualTransfer.characterTrace,
      M6.ActualTransfer.scalar_trace_support, hd]
  apply Polynomial.ext
  intro d
  unfold M6.ActualTransfer.shiftedOutput
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial,
    M6.ActualTransfer.shifted_coefficient_exact]
  by_cases hd : d < 2 * N + 1
  · simp [Fin.sum_univ_eq_sum_range, hd]
  · have hz : (M6.ActualTransfer.Q N a b P).coeff d = 0 :=
      hsupport d (by omega)
    simp [Fin.sum_univ_eq_sum_range, hd, hz]
