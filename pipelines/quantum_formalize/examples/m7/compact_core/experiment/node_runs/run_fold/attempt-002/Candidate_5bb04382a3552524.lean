import FrozenTarget_5bb04382a3552524
theorem M7.CompactGeneration.run_fold : QuantumHarnessFrozenTarget := by
  classical
  unfold QuantumHarnessFrozenTarget
  intro N inst w E bases fuel root
  induction fuel generalizing bases root with
  | zero =>
      rfl
  | succ fuel ih =>
      by_cases h : 0 < root
      · simp only [M7.CompactGeneration.run, if_pos h, List.foldl_cons]
        exact ih _ _
      · simp only [M7.CompactGeneration.run, if_neg h, List.foldl_nil]
