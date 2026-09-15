import FrozenTarget_097ddb5fa597e8df
theorem M5.QuotientCharacter.character_orthogonality : QuantumHarnessFrozenTarget := by
  intro P hP z
  classical
  unfold M5.QuotientCharacter.value
  rw [M5.Character.character_orthogonality,
    M5.QuotientCharacter.coordinates_zero_iff]
