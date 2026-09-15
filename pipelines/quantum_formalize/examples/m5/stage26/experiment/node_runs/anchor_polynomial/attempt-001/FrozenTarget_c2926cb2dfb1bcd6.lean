import M5AnchoredCount


def QuantumHarnessFrozenTarget : Prop :=
  ∀ U : Finset ℕ, 0 ∉ U → M5.SupportPolynomial.ofSupport (insert 0 U) = 1 + M5.SupportPolynomial.ofSupport U
