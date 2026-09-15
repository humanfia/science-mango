import M6KernelFibers


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (F : M6.KernelFibers.BP), F.Monic → Nat.card (AdjoinRoot F) = 2^F.natDegree
