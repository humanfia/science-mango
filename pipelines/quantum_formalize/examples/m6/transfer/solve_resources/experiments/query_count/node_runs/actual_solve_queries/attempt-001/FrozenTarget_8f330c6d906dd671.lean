import M6SolveResources


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP) (d : ℕ) (v : M6.Pinned.Vector (2*N)) (k : ℕ), M6.ActualTransfer.solve N a b = some (d,v,k) → k ≤ 2*N
