import FrozenTarget_bfa9cbf487d82a03
theorem M6.Physical.boundary_pairing : QuantumHarnessFrozenTarget := by
  intro N inst a b h z
  classical
  simp only [M6.Physical.pairing, M6.Physical.J, M6.Physical.boundary,
    Prod.fst, Prod.snd, M6.Physical.conv_adjoint]
  simp [M6.Physical.syndrome, M6.Physical.dot, mul_add,
    Finset.sum_add_distrib, add_comm]
