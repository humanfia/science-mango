import M5Foundation


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (total excluded included : ℕ), total = excluded + included → 0 < total → excluded = 0 → 0 < included
