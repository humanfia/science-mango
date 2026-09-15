import FrozenTarget_235ed4cf13603362
theorem M6.EuclidStorage.control_values_fit : QuantumHarnessFrozenTarget := by
  change ∀ (width : ℕ) (s : M6.EuclidStorage.Slots) (fuel c e t : ℕ), M6.EuclidStorage.slotsFit width s → fuel ≤ 32 * width → c ≤ 32 * width → e ≤ 32 * width → t ≤ 32 * width → ∀ v ∈ M6.EuclidStorage.controlValues s fuel c e t, v < 2 ^ M6.EuclidStorage.registerBits width
  intro width s fuel c e t hs hf hc he ht v hv
  apply M6.EuclidStorage.control_encoding width v
  simp only [M6.EuclidStorage.slotsFit, M6.Euclid.rank] at hs
  simp only [M6.EuclidStorage.controlValues, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, M6.Euclid.rank] at hv
  split_ifs at hs hv <;> simp_all <;> omega
