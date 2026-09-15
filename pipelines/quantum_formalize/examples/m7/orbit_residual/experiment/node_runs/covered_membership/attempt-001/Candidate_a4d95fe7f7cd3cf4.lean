import FrozenTarget_a4d95fe7f7cd3cf4
theorem M7.OrbitResidual.covered_membership : QuantumHarnessFrozenTarget := by
  intro N inst bases y
  classical
  simp only [M7.OrbitResidual.covered, Finset.mem_biUnion]
