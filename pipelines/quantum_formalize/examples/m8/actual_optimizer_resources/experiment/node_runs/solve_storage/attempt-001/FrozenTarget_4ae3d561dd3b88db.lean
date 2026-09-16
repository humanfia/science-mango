import M8OptimizerResources


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b ≤ M8.Cutoff.limit N → M6.ActualTransfer.actualSolveStorage N a b ≤ 16384*(N+1)^3
