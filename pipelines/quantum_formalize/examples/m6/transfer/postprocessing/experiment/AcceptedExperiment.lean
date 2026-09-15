import M6Postprocessing

theorem M6.ActualTransfer.scalar_trace_support : ∀ (R N : ℕ) (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (d : ℕ), 2*N < d → (M6.Transfer.scalarTracePolynomial W N).coeff d = 0 := by
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

theorem M6.ActualTransfer.shift_division : ∀ (z : ℤ) (k : ℕ), Int.shiftRight z k = z / (2:ℤ)^k := by
  intro z k
  simpa only [Int.shiftRight_eq, Nat.cast_pow, Nat.cast_ofNat] using Int.shiftRight_eq_div_pow z k

theorem M6.ActualTransfer.shifted_coefficient_exact : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (P : M6.Pinned.Pins (2*N)) (d : ℕ), M6.ActualTransfer.shiftedCoefficient N a b P d = (M6.ActualTransfer.Q N a b P).coeff d := by
  intro N inst a b P d
  simp [M6.ActualTransfer.shiftedCoefficient, M6.ActualTransfer.Q,
    Polynomial.coeff_sub, M6.Normalize.divide_coeff,
    M6.ActualTransfer.shift_division]

theorem M6.ActualTransfer.shifted_output_exact : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (P : M6.Pinned.Pins (2*N)), M6.ActualTransfer.shiftedOutput N a b P = M6.ActualTransfer.Q N a b P := by
  intro N inst a b P
  classical
  have hsupport : ∀ d, 2 * N < d → (M6.ActualTransfer.Q N a b P).coeff d = 0 := by
    intro d hd
    simp only [M6.ActualTransfer.Q, Polynomial.coeff_sub,
      M6.Normalize.divide_coeff, M6.ActualTransfer.boundaryTrace,
      M6.ActualTransfer.characterTrace]
    rw [M6.ActualTransfer.scalar_trace_support _ N _ d hd,
      M6.ActualTransfer.scalar_trace_support _ N _ d hd]
    simp
  apply Polynomial.ext
  intro d
  unfold M6.ActualTransfer.shiftedOutput
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_monomial,
    M6.ActualTransfer.shifted_coefficient_exact]
  by_cases hd : d < 2 * N + 1
  · rw [Finset.sum_eq_single (⟨d, hd⟩ : Fin (2 * N + 1))]
    · simp
    · intro i hi hne
      have hval : (i : ℕ) ≠ d := by
        intro h
        apply hne
        exact Fin.ext h
      simp [hval]
    · simp
  · rw [hsupport d (by omega)]
    apply Finset.sum_eq_zero
    intro i hi
    have hval : (i : ℕ) ≠ d := by
      have hi_lt := i.isLt
      omega
    simp [hval]

theorem M6.ActualTransfer.shifted_scan_exact : ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (P : M6.Pinned.Pins (2*N)), M6.ActualTransfer.shiftedScan N a b P = M6.Pinned.firstPositive (2*N) (M6.ActualTransfer.Q N a b P) := by
  intro N inst a b P
  classical
  simp only [M6.ActualTransfer.shiftedScan, M6.Pinned.firstPositive,
    M6.ActualTransfer.shifted_coefficient_exact]
#print axioms M6.ActualTransfer.scalar_trace_support
#print axioms M6.ActualTransfer.shift_division
#print axioms M6.ActualTransfer.shifted_coefficient_exact
#print axioms M6.ActualTransfer.shifted_output_exact
#print axioms M6.ActualTransfer.shifted_scan_exact
