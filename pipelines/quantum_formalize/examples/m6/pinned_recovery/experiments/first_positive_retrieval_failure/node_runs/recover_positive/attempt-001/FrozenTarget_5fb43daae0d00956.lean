import M6Pinned


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (m : ℕ) (c : M6.Pinned.Pins m → ℤ), M6.Pinned.partitions c → ∀ (P : M6.Pinned.Pins m) (xs : List (Fin m)), 0 < c P → 0 < c (M6.Pinned.recover c P xs).1
