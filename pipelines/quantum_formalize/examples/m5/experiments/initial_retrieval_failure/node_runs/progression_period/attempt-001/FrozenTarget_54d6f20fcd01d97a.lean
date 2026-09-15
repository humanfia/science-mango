import M5Foundation


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (T E j : ℕ), T ∣ E → T ∣ T + j * E
