import M8Cutoff


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N a b : ℕ), a ≤ N → b ≤ N → 2*N*a*b ≤ 2*N^3
