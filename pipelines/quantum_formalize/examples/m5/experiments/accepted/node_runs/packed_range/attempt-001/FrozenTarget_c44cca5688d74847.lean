import M5Foundation


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (w T r j : ℕ), r < T → j < w → M5.packedExponent T r j < w * T
