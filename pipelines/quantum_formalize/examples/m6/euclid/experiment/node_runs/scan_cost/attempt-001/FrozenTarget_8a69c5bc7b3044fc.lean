import M6Euclid


def QuantumHarnessFrozenTarget : Prop :=
  ∀ width : ℕ, M6.Euclid.scanCost width = width * (6 * width + 4) ∧ (0 < width → M6.Euclid.scanCost width ≤ 10 * width ^ 2)
