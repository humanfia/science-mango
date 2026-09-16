import FrozenTarget_0c0f9990120d2d00
theorem M8.P3Family.valid : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], 3 ≤ N → M8.PhysicalBridge.Valid 3 (M8.P3Family.recipe N)
  intro N inst hN
  classical
  have hs := M8.P3Family.support_data N hN
  have hf := M8.P3Family.full_direction N hN
  have hc : M7.Connectivity.connected (M8.P3Family.support N, M8.P3Family.support N) := by
    simpa only [M7.Connectivity.connected, Set.union_self,
      M8.CoverageFoundation.FullDirection, M8.CoverageFoundation.direction] using hf
  simp_all [M8.PhysicalBridge.Valid, M8.P3Family.recipe]
