import M8Solver


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ w : ℕ, 0 < w → M8.PhysicalBridge.Valid w c → M8.PhysicalBridge.signature c ≠ 1 → ∀ choice : M8.Discovery.Choice N, M8.Discovery.discover c = some choice → M8.PhysicalBridge.solve (M8.Discovery.transformed c choice) ≠ none
