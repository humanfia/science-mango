import M8Cutoff


def QuantumHarnessFrozenTarget : Prop :=
  ∀ N : ℕ, M8.Cutoff.limit N = min (N-1) (Nat.log2 (N+1))
