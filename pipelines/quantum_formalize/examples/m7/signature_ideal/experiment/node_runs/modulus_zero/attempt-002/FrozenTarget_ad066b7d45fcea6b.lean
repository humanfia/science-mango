import M7SignatureIdeal


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], M6.Cyclic.image N (M6.Cyclic.modulus N) = 0
