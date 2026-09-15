import FrozenTarget_62325c789d48e795
theorem M7.CanonicalBlock.shift_add : QuantumHarnessFrozenTarget := by
  intro N inst s t A
  classical
  simp [M7.CanonicalBlock.shift, Finset.image_image, add_assoc, add_comm, add_left_comm]
