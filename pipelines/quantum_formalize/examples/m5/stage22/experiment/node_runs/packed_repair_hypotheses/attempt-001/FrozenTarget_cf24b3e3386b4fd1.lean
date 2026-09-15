import M5BoundedConstructionReady


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (w T : ℕ) (r s : Fin w → Fin T), 2 ≤ w → 0 < T → M5.BoundedConstruction.anchoredTuple r → M5.BoundedConstruction.anchoredTuple s → M5.BoundedConstruction.tupleSupportGcd r s = 1 → ∃ e ∈ (M5.Packing.packedSupport r), 0 < e ∧ 0 < (M5.PhysicalBridge.remainingGcd (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e) ∧ (M5.PhysicalBridge.remainingGcd (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e) < w * T ∧ Nat.gcd (Nat.gcd T (M5.PhysicalBridge.remainingGcd (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e)) e = 1
