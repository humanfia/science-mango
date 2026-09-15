import M6BoundaryFibers


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (F M : M6.BoundaryFibers.BP), F.Monic → F ∣ M → M ≠ 0 → Nat.card {h : AdjoinRoot M // AdjoinRoot.mk M F * h = 0} = 2^F.natDegree
