import M7OrbitResidual


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (c : M7.Action.Recipe N) (g : M7.Action.Record N), M7.ActualOrbit.orbit (M7.Action.act g c) = M7.ActualOrbit.orbit c
