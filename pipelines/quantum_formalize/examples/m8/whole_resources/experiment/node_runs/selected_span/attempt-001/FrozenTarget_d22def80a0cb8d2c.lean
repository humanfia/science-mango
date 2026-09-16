import M8WholeResources


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ w : ℕ, 0 < w → M8.PhysicalBridge.Valid w c → ∀ choice : M8.Discovery.Choice N, M8.Discovery.discover c = some choice → M6.ActualTransfer.span (M7.Supports.polynomial (M8.Discovery.transformed c choice).1) (M7.Supports.polynomial (M8.Discovery.transformed c choice).2) ≤ M8.Cutoff.limit N
