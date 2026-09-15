import M5AnchoredCount

theorem M5.AnchoredCount.anchor_polynomial : ∀ U : Finset ℕ, 0 ∉ U → M5.SupportPolynomial.ofSupport (insert 0 U) = 1 + M5.SupportPolynomial.ofSupport U := by
  change ∀ U : Finset ℕ, 0 ∉ U → M5.SupportPolynomial.ofSupport (insert 0 U) = 1 + M5.SupportPolynomial.ofSupport U
  intro U hU
  simp [M5.SupportPolynomial.ofSupport, Finset.sum_insert, hU]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (P : M5.BinaryPolynomial) (U : Finset ℕ), 0 ∉ U → (P ∣ M5.SupportPolynomial.ofSupport (insert 0 U) ↔ AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport U) = 1)
