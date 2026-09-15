import FrozenTarget_bf77139a7ebc63ea
theorem M6.EuclidStorage.layout_bound : QuantumHarnessFrozenTarget := by
  change ∀ N : ℕ, M6.EuclidStorage.polynomialSlots.length = 4 ∧ M6.EuclidStorage.controlSlots.length = 16 ∧ M6.EuclidStorage.actualPreprocessStorage N ≤ 512 * (N + 1) ^ 2
  intro N
  refine ⟨rfl, rfl, ?_⟩
  norm_num [M6.EuclidStorage.actualPreprocessStorage, M6.EuclidStorage.registerBits, M6.EuclidStorage.polynomialSlots, M6.EuclidStorage.controlSlots] <;> nlinarith [Nat.zero_le (N * N)]
