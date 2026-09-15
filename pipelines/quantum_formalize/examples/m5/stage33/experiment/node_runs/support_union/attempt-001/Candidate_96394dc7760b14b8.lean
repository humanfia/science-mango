import FrozenTarget_96394dc7760b14b8
theorem M5.CompletionBlock.support_union : QuantumHarnessFrozenTarget := by
  change ∀ A U : Finset ℕ, Disjoint A U → M5.SupportPolynomial.ofSupport (A ∪ U) = M5.SupportPolynomial.ofSupport A + M5.SupportPolynomial.ofSupport U
  intro A U h
  unfold M5.SupportPolynomial.ofSupport
  exact Finset.sum_union h
