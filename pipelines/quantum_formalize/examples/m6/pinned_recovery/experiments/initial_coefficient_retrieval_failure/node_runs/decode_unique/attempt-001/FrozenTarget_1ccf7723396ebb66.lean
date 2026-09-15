import M6Pinned


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (P : M6.Pinned.Pins m), M6.Pinned.assigned P → ∀ v : M6.Pinned.Vector m, (M6.Pinned.agrees P v ↔ v = M6.Pinned.decode P)
