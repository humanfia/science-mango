import FrozenTarget_0b438089b6775475
theorem M7.CompactCorrectness.run_cache : QuantumHarnessFrozenTarget := by
  intro N inst w E bases fuel root hroot
  induction fuel generalizing bases root with
  | zero =>
      simpa [M7.CompactGeneration.run] using hroot
  | succ fuel ih =>
      simp only [M7.CompactGeneration.run]
      split <;> dsimp only
      · first | exact hroot | exact ih _ _ rfl
      · first | exact hroot | exact ih _ _ rfl
