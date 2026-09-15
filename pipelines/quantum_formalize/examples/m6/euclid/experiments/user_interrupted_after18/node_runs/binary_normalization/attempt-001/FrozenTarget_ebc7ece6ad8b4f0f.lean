import M6Euclid


def QuantumHarnessFrozenTarget : Prop :=
  ∀ p : M6.Euclid.BP, (p ≠ 0 → p.Monic) ∧ normalize p = p
