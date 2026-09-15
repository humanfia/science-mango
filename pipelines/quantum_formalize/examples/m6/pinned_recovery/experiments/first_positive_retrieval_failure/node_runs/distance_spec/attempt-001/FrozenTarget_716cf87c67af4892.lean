import M6Pinned


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)), (M6.Pinned.distance L = none ↔ L = ∅) ∧ ∀ d : ℕ, (M6.Pinned.distance L = some d ↔ (∃ v ∈ L, M6.Pinned.weight v = d) ∧ ∀ v ∈ L, d ≤ M6.Pinned.weight v)
