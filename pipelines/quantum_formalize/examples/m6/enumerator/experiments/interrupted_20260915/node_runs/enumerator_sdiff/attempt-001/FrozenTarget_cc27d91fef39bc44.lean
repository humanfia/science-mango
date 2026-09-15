import M6Enumerator


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (B C : Finset (M6.Pinned.Vector m)) (P : M6.Pinned.Pins m), B ⊆ C → M6.Pinned.enumerator (C \ B) P = M6.Pinned.enumerator C P - M6.Pinned.enumerator B P
