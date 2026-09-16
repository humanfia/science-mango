import M8PhysicalBridge


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N] (c : M8.PhysicalBridge.Recipe N) (g : M7.Action.Record N), (M8.PhysicalBridge.signature (M7.Action.act g c)).natDegree = (M8.PhysicalBridge.signature c).natDegree
