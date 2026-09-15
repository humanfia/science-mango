import FrozenTarget_f68532d614612e03
theorem M5.PhysicalBridge.remaining_gcd_feasible : QuantumHarnessFrozenTarget := by
  intro T A B e he h
  have h' : M5.Connectivity.supportGcd T (insert e (A.erase e)) B = 1 := by
    simpa only [Finset.insert_erase he] using h
  simpa [M5.Connectivity.supportGcd, M5.PhysicalBridge.remainingGcd,
    Finset.gcd_insert, Nat.gcd_assoc, Nat.gcd_comm, Nat.gcd_left_comm] using h'
