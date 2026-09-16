import M8Solver


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), M8.Solver.originalF c = M8.PhysicalBridge.signature c
