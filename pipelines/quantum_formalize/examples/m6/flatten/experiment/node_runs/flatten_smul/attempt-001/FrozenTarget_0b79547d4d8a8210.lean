import M6Flatten


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) (c : ZMod 2) (z : M6.Physical.Word N), M6.Flatten.flatten N (c • z) = c • M6.Flatten.flatten N z
