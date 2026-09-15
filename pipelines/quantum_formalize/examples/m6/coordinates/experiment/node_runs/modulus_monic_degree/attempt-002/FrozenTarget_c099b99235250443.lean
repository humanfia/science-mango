import M6Coordinates


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], (M6.Cyclic.modulus N).Monic ∧ (M6.Cyclic.modulus N).natDegree = N
