import FrozenTarget_f0fc06a5b35350fe
theorem M7.CompactGeneration.run_fold : QuantumHarnessFrozenTarget := by
  by
    classical
    intro N inst w E bases fuel root
    induction fuel generalizing bases root with
    | zero => rfl
    | succ fuel ih =>
        by_cases h : 0 < root
        · simp only [M7.CompactGeneration.run, if_pos h, List.foldl_cons]
          exact ih _ _
        · simp [M7.CompactGeneration.run, h]
