import M7ActualOrbit


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ y ∈ M7.ActualOrbit.orbit c, M7.ActualOrbit.fiberCount c y = M7.ActualOrbit.stabilizerCount c
