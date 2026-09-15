import FrozenTarget_5687b967e8253d6c
theorem M5.ArithmeticResidueRecovery.completion_feasible : QuantumHarnessFrozenTarget := by
  intro T w F u a b hu
  classical
  have hs := M5.ArithmeticResidueRecovery.completion_word_split (w - 1) u a b hu
  have ha := M5.ArithmeticResidueRecovery.prefix_algebra T _ (u.take (w - 1)) a
  have hb := M5.ArithmeticResidueRecovery.prefix_algebra T _ (u.drop (w - 1)) b
  have ht : (u.take (w - 1)).length ≤ w - 1 := by
    simp only [List.length_take]
    omega
  have hd : (u.drop (w - 1)).length ≤ w - 1 := by
    simp only [List.length_drop]
    omega
  simp [M5.ArithmeticResidueRecovery.wordValid,
    M5.ConditionalResidueCount.feasible,
    M5.ConditionalResidueCount.selectedGcd,
    M5.ConditionalResidueCount.fits,
    hs.1, hs.2.2.1, hs.2.2.2,
    ha.1, ha.2, hb.1, hb.2, ht, hd,
    Nat.gcd_assoc, Nat.gcd_comm, Nat.gcd_left_comm]
