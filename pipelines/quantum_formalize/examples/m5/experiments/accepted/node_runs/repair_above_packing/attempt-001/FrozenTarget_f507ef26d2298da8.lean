import M5Foundation


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (w T e k : ℕ), 0 < T → w ≤ k → w * T ≤ e + k * T
