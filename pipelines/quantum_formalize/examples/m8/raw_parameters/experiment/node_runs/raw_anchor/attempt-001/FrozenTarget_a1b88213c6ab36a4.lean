import M8RawParameters


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N] (c : M8.PhysicalBridge.Recipe N), 0 < w → M8.PhysicalBridge.Valid w c → ∃ g : M7.Action.Record N, M8.PhysicalBridge.Anchored (M7.Action.act g c)
