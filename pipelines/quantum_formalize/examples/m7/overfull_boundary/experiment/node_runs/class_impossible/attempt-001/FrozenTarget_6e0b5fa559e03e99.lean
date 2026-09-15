import M7OverfullBoundary


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N], N < w → ∀ c : M7.Action.Recipe N, ¬ M7.PrefixOrbit.ClassValid w c
