import FrozenTarget_85bf9b09ae02abc4
theorem M7.CompactGeneration.run_length : QuantumHarnessFrozenTarget := by
  by
    classical
    intro N inst w E bases fuel root
    induction fuel generalizing bases root with
    | zero =>
        simp [M7.CompactGeneration.run]
    | succ fuel ih =>
        by_cases h : 0 < root
        · simp only [M7.CompactGeneration.run, if_pos h, List.length_cons]
          exact Nat.succ_le_succ (ih _ _)
        · simp [M7.CompactGeneration.run, h]
