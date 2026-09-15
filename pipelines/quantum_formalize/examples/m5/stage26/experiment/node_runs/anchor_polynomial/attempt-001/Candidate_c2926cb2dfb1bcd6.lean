import FrozenTarget_c2926cb2dfb1bcd6
theorem M5.AnchoredCount.anchor_polynomial : QuantumHarnessFrozenTarget := by
  change ∀ U : Finset ℕ, 0 ∉ U → M5.SupportPolynomial.ofSupport (insert 0 U) = 1 + M5.SupportPolynomial.ofSupport U
  intro U hU
  simp [M5.SupportPolynomial.ofSupport, Finset.sum_insert, hU]
