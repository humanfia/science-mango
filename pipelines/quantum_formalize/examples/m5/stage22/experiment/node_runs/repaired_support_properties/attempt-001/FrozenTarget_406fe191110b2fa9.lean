import M5BoundedConstructionReady


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (w T : ℕ) (r s : Fin w → Fin T), 2 ≤ w → 0 < T → M5.BoundedConstruction.anchoredTuple r → M5.BoundedConstruction.anchoredTuple s → ∀ e k : ℕ, e ∈ (M5.Packing.packedSupport r) → 0 < e → e + k * T ∉ (M5.Packing.packedSupport r) → e + k * T < M5.packingCutoff w T → Nat.gcd (M5.PhysicalBridge.remainingGcd (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e) (e + k * T) = 1 → (M5.RepairSupport.repaired (M5.Packing.packedSupport r) e (e + k * T)).card = w ∧ 0 ∈ (M5.RepairSupport.repaired (M5.Packing.packedSupport r) e (e + k * T)) ∧ (∀ a ∈ (M5.RepairSupport.repaired (M5.Packing.packedSupport r) e (e + k * T)), a < M5.packingCutoff w T) ∧ M5.RepairSupport.combinedGcd (M5.RepairSupport.repaired (M5.Packing.packedSupport r) e (e + k * T)) (M5.Packing.packedSupport s) = 1
