import FrozenTarget_e7848c10d496ce0e
theorem M5.PhysicalRecovery.state_domains : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) (p : List Bool), 0 < N → p.length ≤ M5.PhysicalRecovery.decisionCount N → M5.PhysicalRecovery.StateOK N p
  intro N p hN hp
  simp only [M5.PhysicalRecovery.StateOK,
    M5.PhysicalRecovery.selectedA, M5.PhysicalRecovery.selectedB,
    M5.PhysicalRecovery.availableA, M5.PhysicalRecovery.availableB,
    M5.PhysicalRecovery.selected, M5.PhysicalRecovery.available,
    Finset.subset_iff, Finset.disjoint_left, Finset.mem_insert,
    Finset.mem_image, Finset.mem_filter, Finset.mem_range,
    Finset.mem_singleton]
  aesop (config := { terminal := false }) <;> omega
