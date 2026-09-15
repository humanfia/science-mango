import M6Euclid


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) (p q : M6.Euclid.BP), M6.Euclid.rank p ≤ N + 1 → M6.Euclid.rank q ≤ N + 1 → M6.Euclid.dense N p = M6.Euclid.dense N q → p = q
