import FrozenTarget_901c7404710c8d47
theorem M5.PhysicalBridge.packed_divisibility : QuantumHarnessFrozenTarget := by
  change ∀ (w T d : ℕ) (r : Fin w → Fin T), d ∣ T → ((∀ a ∈ M5.Packing.packedSupport r, d ∣ a) ↔ ∀ i, d ∣ (r i).val)
  intro w T d r hT
  classical
  have hmul : ∀ k : ℕ, d ∣ k * T := fun k => dvd_mul_of_dvd_right hT k
  have hmul' : ∀ k : ℕ, d ∣ T * k := fun k => dvd_mul_of_dvd_left hT k
  simp [M5.Packing.packedSupport, M5.Packing.packedValue,
    Nat.dvd_add_iff_left, Nat.dvd_add_iff_right, hmul, hmul']
