import FrozenTarget_98b7f856630d6072
theorem M7.OrbitResidual.covered_membership : QuantumHarnessFrozenTarget := by
  intro N inst bases y
  classical
  simp only [M7.OrbitResidual.covered, Finset.mem_biUnion]
