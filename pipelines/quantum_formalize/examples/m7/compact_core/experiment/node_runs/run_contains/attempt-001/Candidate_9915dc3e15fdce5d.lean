import FrozenTarget_9915dc3e15fdce5d
theorem M7.CompactGeneration.run_contains : QuantumHarnessFrozenTarget := by
  by
    classical
    intro N inst w E bases fuel root
    induction fuel generalizing bases root with
    | zero =>
        change bases ⊆ bases
        exact fun _ h => h
    | succ fuel ih =>
        by_cases h : 0 < root
        · simp only [M7.CompactGeneration.run, if_pos h]
          intro c hc
          exact (ih _ _) (Finset.mem_insert_of_mem hc)
        · simpa only [M7.CompactGeneration.run, if_neg h] using
            (show bases ⊆ bases from fun _ hc => hc)
