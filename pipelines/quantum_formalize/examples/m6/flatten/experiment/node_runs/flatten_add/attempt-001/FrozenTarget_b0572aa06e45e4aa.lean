import M6Flatten


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) (z w : M6.Physical.Word N), M6.Flatten.flatten N (z+w) = M6.Flatten.flatten N z + M6.Flatten.flatten N w
