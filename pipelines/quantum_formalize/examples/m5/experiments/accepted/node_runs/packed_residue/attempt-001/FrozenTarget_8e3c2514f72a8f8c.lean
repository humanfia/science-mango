import M5Foundation


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (T r j : ℕ), r < T → M5.packedExponent T r j % T = r
