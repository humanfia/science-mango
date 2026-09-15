import M5PhysicalBridge

theorem M5.PhysicalBridge.packed_divisibility : ∀ (w T d : ℕ) (r : Fin w → Fin T), d ∣ T → ((∀ a ∈ M5.Packing.packedSupport r, d ∣ a) ↔ ∀ i, d ∣ (r i).val) := by
  change ∀ (w T d : ℕ) (r : Fin w → Fin T), d ∣ T → ((∀ a ∈ M5.Packing.packedSupport r, d ∣ a) ↔ ∀ i, d ∣ (r i).val)
  intro w T d r hd
  have ht : T % d = 0 := Nat.mod_eq_zero_of_dvd hd
  simp [M5.Packing.packedSupport, M5.Packing.packedValue,
    Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, ht]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (w T : ℕ) (r s : Fin w → Fin T), M5.Connectivity.supportGcd T (M5.Packing.packedSupport r) (M5.Packing.packedSupport s) = Nat.gcd T (Nat.gcd (Finset.univ.gcd (fun i : Fin w => (r i).val)) (Finset.univ.gcd (fun i : Fin w => (s i).val)))
