import M8AntipodalFamily


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (v : ℕ), 3 ≤ v → M8.Cutoff.limit (2^v) = v ∧ v < 2^(v-1)
