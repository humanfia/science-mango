import FrozenTarget_8ea14b81f490ecd6
theorem M7.CanonicalBlock.shift_add : QuantumHarnessFrozenTarget := by
  intro N inst s t A
  simp only [M7.CanonicalBlock.shift, Finset.image_image, add_assoc, add_comm t s]
