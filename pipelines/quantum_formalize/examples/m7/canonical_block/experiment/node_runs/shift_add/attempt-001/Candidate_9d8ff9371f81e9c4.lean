import FrozenTarget_9d8ff9371f81e9c4
theorem M7.CanonicalBlock.shift_add : QuantumHarnessFrozenTarget := by
  intro N inst s t A
  classical
  simp only [M7.CanonicalBlock.shift, Finset.image_image, Function.comp_def, add_assoc, add_comm t s]
