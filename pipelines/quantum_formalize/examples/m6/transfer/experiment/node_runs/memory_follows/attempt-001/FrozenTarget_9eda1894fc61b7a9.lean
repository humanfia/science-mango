import M6Transfer


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (R N : ℕ) [NeZero N] (h : M6.Transfer.Input N), M6.Transfer.Follows R N (M6.Transfer.memoryAt h) h
