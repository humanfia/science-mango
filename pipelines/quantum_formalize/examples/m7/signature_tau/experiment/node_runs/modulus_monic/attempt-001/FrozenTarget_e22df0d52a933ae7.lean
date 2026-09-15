import M7SignatureTau


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], (M6.Cyclic.modulus N).Monic
