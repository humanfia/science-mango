import M6ActualCardinality
import M6ActualCountsAccepted


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.ActualCounts.BP), M6.ActualCounts.f N a b ≤ N
