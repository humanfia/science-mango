import M8OptimizerResources


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), ∀ (d : ℕ) (v : M6.Pinned.Vector (2*N)) (k : ℕ), M6.ActualTransfer.span a b ≤ M8.Cutoff.limit N → M6.ActualTransfer.solve N a b = some (d,v,k) → M6.ActualTransfer.actualWitnessWork N a b k ≤ 200000*(N+1)^6
