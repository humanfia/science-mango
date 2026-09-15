import M7OrbitResidual


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ C0 C1 bases : Finset (M7.Action.Recipe N), M7.OrbitResidual.remaining (C0 ∪ C1) bases = M7.OrbitResidual.remaining C0 bases ∪ M7.OrbitResidual.remaining C1 bases
