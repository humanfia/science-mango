import FrozenTarget_86c3ce60d7156401
theorem M5.OrderCount.divisor_subset_domain : QuantumHarnessFrozenTarget := by
  change ∀ (N d k : ℕ), (M5.OrderCount.divisorPositions N d).powersetCard k = ((M5.OrderCount.positivePositions N).powersetCard k).filter (fun U => ∀ s ∈ U, d ∣ s)
  intro N d k
  classical
  ext U
  simp [M5.OrderCount.divisorPositions, Finset.mem_powersetCard, Finset.subset_iff, forall_and, and_assoc, and_left_comm, and_comm]
