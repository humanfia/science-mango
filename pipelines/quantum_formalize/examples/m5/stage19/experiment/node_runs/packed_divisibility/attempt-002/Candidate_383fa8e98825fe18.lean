import FrozenTarget_383fa8e98825fe18
theorem M5.PhysicalBridge.packed_divisibility : QuantumHarnessFrozenTarget := by
  change ∀ (w T d : ℕ) (r : Fin w → Fin T), d ∣ T → ((∀ a ∈ M5.Packing.packedSupport r, d ∣ a) ↔ ∀ i, d ∣ (r i).val)
  intro w T d r hT
  have hmul (n : ℕ) : d ∣ n * T := by
    obtain ⟨k, hk⟩ := hT
    refine ⟨n * k, ?_⟩
    rw [hk]
    ac_rfl
  simp [M5.Packing.packedSupport, M5.Packing.packedValue]
  constructor
  · intro h i
    have hm := hmul (M5.Packing.occurrenceTag r i)
    first
    | exact (Nat.dvd_add_iff_left hm).mp (h i)
    | exact (Nat.dvd_add_iff_right hm).mp (h i)
  · intro h i
    exact dvd_add (h i) (hmul (M5.Packing.occurrenceTag r i))
