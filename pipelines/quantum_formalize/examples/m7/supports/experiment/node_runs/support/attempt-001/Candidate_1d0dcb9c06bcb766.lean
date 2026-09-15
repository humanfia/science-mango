import FrozenTarget_1d0dcb9c06bcb766
theorem M7.Supports.support : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (N : ℕ) [NeZero N] (A : M7.Supports.Support N), (M7.Supports.polynomial A).support = M7.Supports.natSupport A
  intro N inst A
  ext n
  rw [Polynomial.mem_support_iff, M7.Supports.coefficient N A n]
  simp only [M7.Supports.natSupport, Finset.mem_image]
  by_cases h : ∃ i ∈ A, i.val = n
  · simp [h]
  · simp [h]
