import M6Enumerator


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (L : Finset (M6.Pinned.Vector m)), Polynomial.eval 1 (M6.Pinned.enumerator L (M6.Pinned.free m)) = (L.card : ℤ)
