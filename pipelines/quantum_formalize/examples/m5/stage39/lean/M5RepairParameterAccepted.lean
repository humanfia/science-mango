import M5BoundedConstruction

theorem M5.BoundedConstruction.repair_parameter : ∀ (w T : ℕ) (r s : Fin w → Fin T) (e : ℕ), 0 < T → e ∈ (M5.Packing.packedSupport r) → 0 < (M5.PhysicalBridge.remainingGcd (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e) → (M5.PhysicalBridge.remainingGcd (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e) < w * T → Nat.gcd (Nat.gcd T (M5.PhysicalBridge.remainingGcd (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e)) e = 1 → ∃ k : ℕ, w ≤ k ∧ e + k * T ∉ (M5.Packing.packedSupport r) ∧ e + k * T < M5.packingCutoff w T ∧ Nat.gcd (M5.PhysicalBridge.remainingGcd (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e) (e + k * T) = 1 := by
  intro w T r s e hT he hδpos hδlt hcop
  have he_bound : e < w * T := by
    first
    | exact M5.Packing.packed_support_range r e he
    | exact?
  obtain ⟨k, hk, hk_bound, hk_coprime⟩ :
      ∃ k : ℕ, w ≤ k ∧
        k < w + M5.PhysicalBridge.remainingGcd
          (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e ∧
        Nat.gcd (M5.PhysicalBridge.remainingGcd
          (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) e)
          (e + k * T) = 1 := by
    exact?
  refine ⟨k, hk, ?_, ?_, hk_coprime⟩
  · intro hmem
    have hbound : e + k * T < w * T := by
      first
      | exact M5.Packing.packed_support_range r (e + k * T) hmem
      | exact?
    have hmul : w * T ≤ k * T := Nat.mul_le_mul_right T hk
    omega
  · exact?
#print axioms M5.BoundedConstruction.repair_parameter
