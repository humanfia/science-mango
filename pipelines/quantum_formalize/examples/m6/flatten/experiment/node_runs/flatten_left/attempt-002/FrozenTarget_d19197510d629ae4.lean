import M6Flatten


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (z : M6.Physical.Word N), M6.Flatten.unflatten N (M6.Flatten.flatten N z) = z
