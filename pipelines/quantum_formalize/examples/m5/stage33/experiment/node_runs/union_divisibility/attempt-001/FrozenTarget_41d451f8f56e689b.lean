import M5CompletionBlock

theorem M5.CompletionBlock.support_union : ∀ A U : Finset ℕ, Disjoint A U → M5.SupportPolynomial.ofSupport (A ∪ U) = M5.SupportPolynomial.ofSupport A + M5.SupportPolynomial.ofSupport U := by
  change ∀ A U : Finset ℕ, Disjoint A U → M5.SupportPolynomial.ofSupport (A ∪ U) = M5.SupportPolynomial.ofSupport A + M5.SupportPolynomial.ofSupport U
  intro A U h
  unfold M5.SupportPolynomial.ofSupport
  exact Finset.sum_union h
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (P : M5.BinaryPolynomial) (A U : Finset ℕ), Disjoint A U → (P ∣ M5.SupportPolynomial.ofSupport (A ∪ U) ↔ AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport U) = AdjoinRoot.mk P (M5.SupportPolynomial.ofSupport A))
