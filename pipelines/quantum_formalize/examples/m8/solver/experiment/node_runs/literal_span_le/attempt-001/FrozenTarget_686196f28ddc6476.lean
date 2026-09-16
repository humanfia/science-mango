import M8Solver


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ∀ w : ℕ, 0 < w → M8.PhysicalBridge.Valid w c → M6.ActualTransfer.span (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2) ≤ M8.Anchor.span c
