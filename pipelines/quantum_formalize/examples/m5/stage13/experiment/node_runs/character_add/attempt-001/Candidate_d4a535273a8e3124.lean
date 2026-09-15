import FrozenTarget_d4a535273a8e3124
theorem M5.QuotientCharacter.character_add : QuantumHarnessFrozenTarget := by
  intro P hP lam z u
  unfold M5.QuotientCharacter.value
  simp only [map_add, M5.Character.character_add]
