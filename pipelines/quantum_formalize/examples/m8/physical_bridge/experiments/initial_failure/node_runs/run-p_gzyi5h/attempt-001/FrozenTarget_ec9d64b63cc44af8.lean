import M8PhysicalBridge


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M8.PhysicalBridge.Recipe N) (g : M7.Action.Record N), ∀ w : ℕ, M8.PhysicalBridge.Valid w c → M8.PhysicalBridge.Anchored (M7.Action.act g c) → M6.Final.PointwiseCorrect N (M7.Supports.polynomial (M7.Action.act g c).1) (M7.Supports.polynomial (M7.Action.act g c).2)
