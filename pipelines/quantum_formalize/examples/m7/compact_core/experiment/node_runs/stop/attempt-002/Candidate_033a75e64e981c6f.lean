import FrozenTarget_033a75e64e981c6f
theorem M7.CompactGeneration.stop : QuantumHarnessFrozenTarget := by
  unfold QuantumHarnessFrozenTarget
  intro N inst w E bases fuel root hroot
  have hnonpos : ¬ (0 < root) := not_lt_of_ge hroot
  cases fuel <;> simp [M7.CompactGeneration.run, hnonpos]
