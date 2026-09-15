import M5Foundation


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (w T E N : ℕ), N < M5.packingCutoff w T + E → E ≤ 2 ^ (w * T) → N < M5.birthBound w T
