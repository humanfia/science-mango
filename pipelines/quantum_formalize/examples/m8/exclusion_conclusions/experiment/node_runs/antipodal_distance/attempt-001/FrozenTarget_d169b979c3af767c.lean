import M8Exclusion


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (v : ℕ), 3 ≤ v → N = 2^v → M7.Transport.distance (M8.AntipodalFamily.recipe N) = some 2
