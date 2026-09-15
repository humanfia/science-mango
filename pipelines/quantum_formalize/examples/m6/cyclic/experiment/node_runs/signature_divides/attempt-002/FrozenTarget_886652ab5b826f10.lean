import M6Cyclic


def QuantumHarnessFrozenTarget : Prop :=
  ∀ a b M : M6.Cyclic.BinaryPolynomial, M6.Cyclic.signature a b M ∣ a ∧ M6.Cyclic.signature a b M ∣ b ∧ M6.Cyclic.signature a b M ∣ M
