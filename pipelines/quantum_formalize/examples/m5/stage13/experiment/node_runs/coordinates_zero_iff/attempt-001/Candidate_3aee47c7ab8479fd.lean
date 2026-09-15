import FrozenTarget_3aee47c7ab8479fd
theorem M5.QuotientCharacter.coordinates_zero_iff : QuantumHarnessFrozenTarget := by
  intro P hP z
  first
  | exact (M5.QuotientCharacter.coordinates P hP).map_eq_zero_iff
  | simp [M5.QuotientCharacter.coordinates]
