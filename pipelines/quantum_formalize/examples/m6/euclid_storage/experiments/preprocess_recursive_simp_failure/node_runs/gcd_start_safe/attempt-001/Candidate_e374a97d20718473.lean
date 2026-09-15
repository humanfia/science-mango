import FrozenTarget_e374a97d20718473
theorem M6.EuclidStorage.gcd_start_safe : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro p q saved c e t width hwidth hp hq hs hc he ht
  have hz : M6.Euclid.rank (0 : M6.Euclid.BP) = 0 := by
    simp [M6.Euclid.rank]
  dsimp [M6.Euclid.euclid] at hc he ht
  apply M6.EuclidStorage.gcd_loop_safe
  · exact hwidth
  · simp [M6.EuclidStorage.slotsFit, hz, hp, hq, hs]
  · rfl
  · omega
  · exact hc
  · exact he
  · dsimp only
    omega
