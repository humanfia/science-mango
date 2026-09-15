import M5FactorProduct


def QuantumHarnessFrozenTarget : Prop :=
  ∀ p q : M5.BinaryPolynomial, p.Monic → q.Monic → Irreducible p → Irreducible q → p ≠ q → IsCoprime p q
