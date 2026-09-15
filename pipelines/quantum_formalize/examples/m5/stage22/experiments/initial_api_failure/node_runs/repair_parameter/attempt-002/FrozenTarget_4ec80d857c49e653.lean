import M5BoundedConstruction


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (w T : ℕ) (r s : Fin w → Fin T) (e : ℕ), 0 < T → e ∈ (M5.Packing.packedSupport r) → 0 < (M5.PhysicalBridge.remainingGcd (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e) → (M5.PhysicalBridge.remainingGcd (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e) < w * T → Nat.gcd (Nat.gcd T (M5.PhysicalBridge.remainingGcd (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e)) e = 1 → ∃ k : ℕ, w ≤ k ∧ e + k * T ∉ (M5.Packing.packedSupport r) ∧ e + k * T < M5.packingCutoff w T ∧ Nat.gcd (M5.PhysicalBridge.remainingGcd (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e) (e + k * T) = 1
