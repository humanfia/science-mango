import M6Euclid


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (width : ℕ) (p : M6.Euclid.BP), M6.Euclid.rank p ≤ width → M6.Euclid.scanRank width p = M6.Euclid.rank p
