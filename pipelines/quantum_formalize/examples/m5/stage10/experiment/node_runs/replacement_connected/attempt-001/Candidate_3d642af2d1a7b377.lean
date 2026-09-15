import FrozenTarget_3d642af2d1a7b377
theorem M5.RepairSupport.replacement_connected : QuantumHarnessFrozenTarget := by
  intro A B e q h
  rw [M5.RepairSupport.replacement_combined_gcd, Nat.gcd_comm q]
  exact h
