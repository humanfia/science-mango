import M8SequentialResources


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ c : M7.Action.Recipe N, M8.SequentialStore.prefixCharge (M8.SequentialResources.primitiveCharge N) (M8.WholeResources.run c).charges = M8.WholeResources.indexedWork c * M8.SequentialResources.primitiveCharge N
