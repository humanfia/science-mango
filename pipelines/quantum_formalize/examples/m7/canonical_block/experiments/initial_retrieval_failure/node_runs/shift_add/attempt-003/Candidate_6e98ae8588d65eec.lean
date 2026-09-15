import FrozenTarget_6e98ae8588d65eec
theorem M7.CanonicalBlock.shift_add : QuantumHarnessFrozenTarget := by
  intro N inst s t A
  classical
  simp only [M7.CanonicalBlock.shift, Finset.image_image, Function.comp_def, add_assoc, add_comm t s]
