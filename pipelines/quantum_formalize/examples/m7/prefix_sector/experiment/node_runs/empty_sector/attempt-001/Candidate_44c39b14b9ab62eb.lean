import FrozenTarget_44c39b14b9ab62eb
theorem M7.PrefixSector.empty_sector : QuantumHarnessFrozenTarget := by
  change ∀ (N w : ℕ) (A B WA WB : Finset ℕ), M7.PrefixSector.count N w ∅ A B WA WB = 0 ∧ M7.PrefixSector.completions N w ∅ A B WA WB = ∅
  intro N w A B WA WB
  classical
  simp [M7.PrefixSector.count, M7.PrefixSector.completions]
