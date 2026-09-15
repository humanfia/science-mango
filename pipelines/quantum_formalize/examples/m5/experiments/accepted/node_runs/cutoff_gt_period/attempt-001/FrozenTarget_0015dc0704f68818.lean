import M5Foundation


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (w T : ℕ), 2 ≤ w → 0 < T → T < M5.packingCutoff w T
