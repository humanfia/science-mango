import M7ActualOrbit


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), 0 < M7.ActualOrbit.stabilizerCount c
