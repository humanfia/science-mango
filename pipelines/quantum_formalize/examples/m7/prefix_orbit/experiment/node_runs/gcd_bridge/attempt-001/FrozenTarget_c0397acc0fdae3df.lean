import M7PrefixOrbit


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ y : M7.Action.Recipe N, M7.Domain.connectivityGcd y.1 y.2 = M5.Connectivity.supportGcd N (M7.ResiduePrefix.encode y.1) (M7.ResiduePrefix.encode y.2)
