import FrozenTarget_9eb28722706a0d86
theorem M5.Connectivity.support_gcd_dvd : QuantumHarnessFrozenTarget := by
  intro N d A B
  simp [M5.Connectivity.supportGcd, Nat.dvd_gcd_iff, Finset.dvd_gcd_iff, and_assoc]
