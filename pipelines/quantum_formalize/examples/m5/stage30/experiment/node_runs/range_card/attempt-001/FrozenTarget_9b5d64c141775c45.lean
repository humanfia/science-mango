import M5OrderBoundary


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (S : Finset ℕ) (N : ℕ), (∀ e ∈ S, e < N) → S.card ≤ N
