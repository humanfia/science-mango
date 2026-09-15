import FrozenTarget_e6c12b55b4fc99b7
theorem M5.RepairSupport.replacement_anchor : QuantumHarnessFrozenTarget := by
  change ∀ (A : Finset ℕ) (e q : ℕ), e ≠ 0 → 0 ∈ A → 0 ∈ M5.RepairSupport.repaired A e q
  intro A e q he hA
  simp [M5.RepairSupport.repaired, he, Ne.symm he, hA]
