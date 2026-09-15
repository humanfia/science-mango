import FrozenTarget_a8e6316aba449b06
theorem M7.GenerationCalls.run_projection : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N] (w : ℕ) (E : Finset M5.BinaryPolynomial) (bases : Finset (M7.Action.Recipe N)) (fuel : ℕ) (root : ℤ), (M7.GenerationCalls.runMeasured w E fuel bases root).1 = M7.CompactGeneration.run w E fuel bases root
  classical
  intro N inst w E bases fuel root
  induction fuel generalizing bases root with
  | zero => rfl
  | succ fuel ih =>
      by_cases h : 0 < root
      · simp [M7.GenerationCalls.runMeasured, M7.CompactGeneration.run, h,
          M7.GenerationCalls.emission_projection, ih]
      · simp [M7.GenerationCalls.runMeasured, M7.CompactGeneration.run, h]
