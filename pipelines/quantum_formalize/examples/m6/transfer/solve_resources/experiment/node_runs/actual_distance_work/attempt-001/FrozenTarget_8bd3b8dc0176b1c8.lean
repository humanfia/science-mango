import M6SolveResourcesReady


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), M6.ActualTransfer.span a b < N → M6.ActualTransfer.actualDistanceWork N a b ≤ 50000*N^3*4^(M6.ActualTransfer.span a b)
