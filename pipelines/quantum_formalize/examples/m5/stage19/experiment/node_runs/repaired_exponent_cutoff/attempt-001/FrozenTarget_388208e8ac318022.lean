import M5PhysicalBridge


def QuantumHarnessFrozenTarget : Prop :=
  ∀ w T e δ k : ℕ, 0 < T → e < w * T → δ < w * T → k < w + δ → e + k * T < M5.packingCutoff w T
