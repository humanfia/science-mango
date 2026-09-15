import M6ZeroSpan


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (a b : M6.Final.BP), a.coeff 0 = 1 → b.coeff 0 = 1 → M6.ActualTransfer.span a b = 0 → a = 1 ∧ b = 1
