import M7OrbitResidual


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (bases : Finset (M7.Action.Recipe N)) (y : M7.Action.Recipe N), y ∈ M7.OrbitResidual.covered bases ↔ ∃ c ∈ bases, y ∈ M7.ActualOrbit.orbit c
