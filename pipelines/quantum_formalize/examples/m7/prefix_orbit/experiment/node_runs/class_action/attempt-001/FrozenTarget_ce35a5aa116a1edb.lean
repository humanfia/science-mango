import M7PrefixOrbit


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (w : ℕ) (c : M7.Action.Recipe N) (g : M7.Action.Record N), M7.PrefixOrbit.ClassValid w c → M7.PrefixOrbit.ClassValid w (M7.Action.act g c)
