import FrozenTarget_431dd76ff56c5afe
theorem M5.QuotientCharacter.character_orthogonality : QuantumHarnessFrozenTarget := by
  intro P hP z
  classical
  unfold M5.QuotientCharacter.value
  rw [M5.Character.character_orthogonality]
  simp only [M5.QuotientCharacter.coordinates_zero_iff]
