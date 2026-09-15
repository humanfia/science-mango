import FrozenTarget_6c85bba7458d023d
theorem M5.RepairSupport.replacement_anchor : QuantumHarnessFrozenTarget := by
  change ∀ (A : Finset ℕ) (e q : ℕ), e ≠ 0 → 0 ∈ A → 0 ∈ M5.RepairSupport.repaired A e q
  intro A e q he h0
  simp [M5.RepairSupport.repaired, he, Ne.symm he, h0]
