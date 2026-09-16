import M8RawParameters


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N w : ℕ) [NeZero N] (c : M8.PhysicalBridge.Recipe N), 0 < w → M8.PhysicalBridge.Valid w c → M6.Final.encodedQubits N (M7.Supports.polynomial c.1) (M7.Supports.polynomial c.2) = 2*(M8.PhysicalBridge.signature c).natDegree
