import FrozenTarget_d4f6eab3a47dae97
theorem M5.RepairSupport.replacement_combined_gcd : QuantumHarnessFrozenTarget := by
  intro A B e q
  simp [M5.RepairSupport.combinedGcd, M5.RepairSupport.repaired, Finset.gcd_insert, Nat.gcd_assoc]
