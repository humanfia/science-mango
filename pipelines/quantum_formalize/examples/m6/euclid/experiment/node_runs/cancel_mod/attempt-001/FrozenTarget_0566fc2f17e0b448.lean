import M6Euclid


def QuantumHarnessFrozenTarget : Prop :=
  ∀ p q : M6.Euclid.BP, M6.Euclid.cancel p q % q = p % q
