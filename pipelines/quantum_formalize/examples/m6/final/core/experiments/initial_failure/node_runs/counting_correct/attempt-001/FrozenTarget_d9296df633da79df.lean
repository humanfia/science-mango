import M6FinalReady


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (a b : M6.Final.BP), M6.Final.Admissible N a b → M6.Final.CountingCorrect N a b
