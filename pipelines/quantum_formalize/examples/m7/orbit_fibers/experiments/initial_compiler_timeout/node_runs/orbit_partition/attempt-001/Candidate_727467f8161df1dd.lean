import FrozenTarget_727467f8161df1dd
theorem M7.OrbitFibers.orbit_partition : QuantumHarnessFrozenTarget := by
  classical
  intro G _ _ X _ c P test
  unfold M7.OrbitFibers.orbitCount
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases h : P y <;> cases ht : test y <;> simp [h, ht]
