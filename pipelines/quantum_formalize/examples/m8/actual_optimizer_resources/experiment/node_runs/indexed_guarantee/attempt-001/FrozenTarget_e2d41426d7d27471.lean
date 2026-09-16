import M8OptimizerResources


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), ∀ (pins : M6.Pinned.Pins (2*N)) (character : Bool), M6.ActualTransfer.span a b ≤ M8.Cutoff.limit N → M6.Transfer.IndexedArrayGuarantee (M6.ActualTransfer.span a b) N (M8.OptimizerResources.weight N a b pins character)
