import M8OptimizerResources


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), ∀ (pins : M6.Pinned.Pins (2*N)) (character : Bool), ∀ i m t, M6.Transfer.polynomialMass ((M8.OptimizerResources.weight N a b pins character) i m t) ≤ 4 ∧ ((M8.OptimizerResources.weight N a b pins character) i m t).natDegree ≤ 2
