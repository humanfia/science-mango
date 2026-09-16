import M8WholeResources


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), (M8.WholeResources.run c).outcome = M8.Solver.run c
