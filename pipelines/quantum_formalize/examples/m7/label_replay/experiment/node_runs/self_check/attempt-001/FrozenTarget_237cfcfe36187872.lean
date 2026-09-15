import M7LabelReplay


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), M7.LabelReplay.check c (M7.LabelReplay.expected c) = true
