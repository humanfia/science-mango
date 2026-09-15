import M6Pinned


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (P : M6.Pinned.Pins m) (d : ℕ), 0 ≤ M6.Pinned.count L P d ∧ (0 < M6.Pinned.count L P d ↔ ∃ v ∈ L, M6.Pinned.agrees P v ∧ M6.Pinned.weight v = d)
