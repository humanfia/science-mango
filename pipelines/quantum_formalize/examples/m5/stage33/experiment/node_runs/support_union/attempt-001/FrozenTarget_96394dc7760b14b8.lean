import M5CompletionBlock


def QuantumHarnessFrozenTarget : Prop :=
  ∀ A U : Finset ℕ, Disjoint A U → M5.SupportPolynomial.ofSupport (A ∪ U) = M5.SupportPolynomial.ofSupport A + M5.SupportPolynomial.ofSupport U
