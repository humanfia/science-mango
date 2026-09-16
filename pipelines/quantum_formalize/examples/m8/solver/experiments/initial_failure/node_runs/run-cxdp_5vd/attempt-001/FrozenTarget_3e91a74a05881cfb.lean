import M8Solver


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ w : ℕ, 0 < w → M8.PhysicalBridge.Valid w c → (M8.Discovery.discover c ≠ none ↔ M8.OrbitSpan.value c ≤ M8.Cutoff.limit N)
