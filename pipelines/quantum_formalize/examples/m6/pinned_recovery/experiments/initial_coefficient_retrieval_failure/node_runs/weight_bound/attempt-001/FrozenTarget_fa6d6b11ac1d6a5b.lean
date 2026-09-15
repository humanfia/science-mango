import M6Pinned


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (v : M6.Pinned.Vector m), M6.Pinned.weight v ≤ m
