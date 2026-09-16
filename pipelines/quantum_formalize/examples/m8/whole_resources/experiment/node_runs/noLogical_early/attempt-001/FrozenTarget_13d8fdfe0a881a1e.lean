import M8WholeResources


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), M8.Solver.originalF c = 1 → (M8.WholeResources.run c).charges = [M8.WholeResources.setupWork N,M8.WholeResources.originalWork c] ∧ (M8.WholeResources.run c).discoveryCalls = 0 ∧ (M8.WholeResources.run c).optimizerCalls = 0
