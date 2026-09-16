import FrozenTarget_64329d0ffc663ae9
theorem M8.AntipodalFamily.valid : QuantumHarnessFrozenTarget := by
  classical
  intro N inst hN hEven
  have hd := M8.AntipodalFamily.support_data N hN hEven
  have hf := M8.AntipodalFamily.full_direction N hN hEven
  have hc : M7.Connectivity.connected (M8.AntipodalFamily.recipe N) := by
    simpa only [M7.Connectivity.connected, M8.AntipodalFamily.recipe,
      M8.CoverageFoundation.FullDirection, M8.CoverageFoundation.direction,
      Set.union_self] using hf
  simp_all [M8.PhysicalBridge.Valid, M8.AntipodalFamily.recipe]
