import M7ActualOrbit


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ P : M7.Action.Recipe N → Prop, M7.ActualOrbit.actionCount c P = M7.ActualOrbit.distinctCount c P * M7.ActualOrbit.stabilizerCount c
