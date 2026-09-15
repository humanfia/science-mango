import M7OrbitResidual


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (C bases : Finset (M7.Action.Recipe N)) (c : M7.Action.Recipe N), M7.OrbitResidual.remaining C (insert c bases) = M7.OrbitResidual.remaining C bases \ M7.ActualOrbit.orbit c
