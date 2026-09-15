import FrozenTarget_165878b43635e40d
theorem M5.RepairSupport.replacement_combined_gcd : QuantumHarnessFrozenTarget := by
  intro A B e q
  unfold M5.RepairSupport.combinedGcd M5.RepairSupport.repaired
  rw [Finset.gcd_insert]
  change Nat.gcd (Nat.gcd q ((A.erase e).gcd id)) (B.gcd id) = Nat.gcd q (Nat.gcd ((A.erase e).gcd id) (B.gcd id))
  exact Nat.gcd_assoc q ((A.erase e).gcd id) (B.gcd id)
