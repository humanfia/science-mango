import FrozenTarget_3c55d9a1cd80b513
theorem M5.BoundedConstruction.repair_parameter : QuantumHarnessFrozenTarget := by
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
