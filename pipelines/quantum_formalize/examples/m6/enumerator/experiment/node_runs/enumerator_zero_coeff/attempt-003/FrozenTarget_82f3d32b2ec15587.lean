import M6Enumerator


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)) (P : M6.Pinned.Pins m), (0 : M6.Pinned.Vector m) ∉ L → (M6.Pinned.enumerator L P).coeff 0 = 0
