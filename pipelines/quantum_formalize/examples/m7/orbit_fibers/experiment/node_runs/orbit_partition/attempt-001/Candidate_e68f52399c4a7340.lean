import FrozenTarget_e68f52399c4a7340
theorem M7.OrbitFibers.orbit_partition : QuantumHarnessFrozenTarget := by
  classical
  intro G _ _ X _ c P test
  unfold M7.OrbitFibers.orbitCount
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  have hb : ∀ b : Bool, b ≠ false → b = true := by decide
  by_cases hp : P y
  · by_cases ht : test y = false
    · simp [hp, ht]
    · have ht' : test y = true := hb (test y) ht
      simp [hp, ht']
  · simp [hp]
