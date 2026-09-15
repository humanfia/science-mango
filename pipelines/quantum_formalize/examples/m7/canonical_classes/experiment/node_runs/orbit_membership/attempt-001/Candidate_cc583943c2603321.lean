import FrozenTarget_cc583943c2603321
theorem M7.CanonicalClasses.orbit_membership : QuantumHarnessFrozenTarget := by
  by
    classical
    intro N inst c y
    simp only [M7.ActualOrbit.orbit, Finset.mem_image, Finset.mem_univ, true_and]
    exact (M7.CanonicalOuter.orbit_complete N c y).trans eq_comm
