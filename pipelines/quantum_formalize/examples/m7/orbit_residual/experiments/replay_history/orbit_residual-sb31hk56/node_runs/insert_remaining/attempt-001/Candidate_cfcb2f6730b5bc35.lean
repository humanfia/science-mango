import FrozenTarget_cfcb2f6730b5bc35
theorem M7.OrbitResidual.insert_remaining : QuantumHarnessFrozenTarget := by
  classical
  intro N inst C bases c
  ext x
  simp only [M7.OrbitResidual.remaining, M7.OrbitResidual.covered,
    Finset.biUnion_insert, Finset.mem_sdiff, Finset.mem_union]
  tauto
