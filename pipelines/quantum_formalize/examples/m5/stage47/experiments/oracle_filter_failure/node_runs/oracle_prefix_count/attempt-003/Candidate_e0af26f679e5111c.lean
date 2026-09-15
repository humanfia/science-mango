import FrozenTarget_e0af26f679e5111c
theorem M5.ArithmeticResidueRecovery.oracle_prefix_count : QuantumHarnessFrozenTarget := by
  intro w F hw hF hF0 u hu
  classical
  have hfit : M5.ConditionalResidueCount.fits w (u.take (w - 1)) (u.drop (w - 1)) := by
    simp only [M5.ConditionalResidueCount.fits, List.length_take, List.length_drop]
    omega
  rw [← M5.ArithmeticResidueRecovery.completion_prefix_card (w - 1) u
    (M5.ArithmeticResidueRecovery.wordValid w F) hu]
  unfold M5.ArithmeticResidueRecovery.oracle
  rw [(M5.ConditionalResidueCount.period_conditionalA_exact w F
    (u.take (w - 1)) (u.drop (w - 1)) hw hF hF0).1]
  unfold M5.ConditionalResidueCount.validCompletions
  rw [if_pos hfit]
  unfold M5.ArithmeticResidueRecovery.completionCount
  apply congrArg (fun n : ℕ => (n : ℤ))
  apply congrArg Finset.card
  ext ab
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact M5.ArithmeticResidueRecovery.completion_feasible
    (M5.signaturePeriod F) w F u ab.1 ab.2 hu
