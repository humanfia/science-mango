import FrozenTarget_85035691709011b3
theorem M5.RepairSupport.replacement_connected : QuantumHarnessFrozenTarget := by
  intro A B e q h
  rw [M5.RepairSupport.replacement_combined_gcd]
  rw [Nat.gcd_comm q]
  exact h
