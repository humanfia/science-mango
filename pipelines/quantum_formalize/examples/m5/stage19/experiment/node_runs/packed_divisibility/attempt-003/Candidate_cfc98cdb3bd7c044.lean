import FrozenTarget_cfc98cdb3bd7c044
theorem M5.PhysicalBridge.packed_divisibility : QuantumHarnessFrozenTarget := by
  change ∀ (w T d : ℕ) (r : Fin w → Fin T), d ∣ T → ((∀ a ∈ M5.Packing.packedSupport r, d ∣ a) ↔ ∀ i, d ∣ (r i).val)
  intro w T d r hd
  have ht : T % d = 0 := Nat.mod_eq_zero_of_dvd hd
  simp [M5.Packing.packedSupport, M5.Packing.packedValue,
    Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, ht]
