import FrozenTarget_fd5e7e9865cbe0b3
theorem M7.CompactCorrectness.run_records : QuantumHarnessFrozenTarget := by
  classical
  intro N inst w E bases fuel root e he
  induction fuel generalizing bases root with
  | zero =>
      simpa [M7.CompactGeneration.run] using he
  | succ fuel ih =>
      simp only [M7.CompactGeneration.run] at he
      split at he <;> simp only [List.mem_cons, List.not_mem_nil] at he
      all_goals first | contradiction | skip
      all_goals rcases he with rfl | he
      · exact ⟨(M7.CompactGeneration.emission_action N w E bases).1,
          (M7.CompactGeneration.emission_action N w E bases).2,
          rfl, rfl, rfl,
          (M7.CompactGeneration.emission_stabilizer N w E bases).1⟩
      · exact ih _ _ he
