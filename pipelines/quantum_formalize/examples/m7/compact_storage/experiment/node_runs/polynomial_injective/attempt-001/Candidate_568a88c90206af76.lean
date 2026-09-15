import FrozenTarget_568a88c90206af76
theorem M7.CompactStorage.polynomial_injective : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) (F G : M5.BinaryPolynomial), F.natDegree ≤ N → G.natDegree ≤ N → M7.CompactStorage.polynomialBits N F = M7.CompactStorage.polynomialBits N G → F = G
  intro N F G hF hG hbits
  have hinj : ∀ a b : ZMod 2, decide (a = 1) = decide (b = 1) → a = b := by
    decide
  apply Polynomial.ext
  intro i
  by_cases hi : i ≤ N
  · have h := congrFun hbits (⟨i, by omega⟩ : Fin (N + 1))
    change decide (F.coeff i = 1) = decide (G.coeff i = 1) at h
    exact hinj (F.coeff i) (G.coeff i) h
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (show F.natDegree < i by omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (show G.natDegree < i by omega)]
