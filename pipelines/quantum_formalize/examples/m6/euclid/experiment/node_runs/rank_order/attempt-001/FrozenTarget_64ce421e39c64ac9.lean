import M6Euclid


def QuantumHarnessFrozenTarget : Prop :=
  ∀ p q : M6.Euclid.BP, (M6.Euclid.rank p < M6.Euclid.rank q ↔ p.degree < q.degree) ∧ (M6.Euclid.rank p ≤ M6.Euclid.rank q ↔ p.degree ≤ q.degree)
