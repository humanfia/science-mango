import FrozenTarget_b486924477555572
theorem M5.ArithmeticResidueRecovery.completion_feasible : QuantumHarnessFrozenTarget := by
  intro T w F u a b hu
  classical
  rcases M5.ArithmeticResidueRecovery.completion_word_split (w - 1) u a b hu with
    ⟨hlen, hprefix, htake, hdrop⟩
  have ha := M5.ArithmeticResidueRecovery.prefix_algebra T _ (u.take (w - 1)) a
  have hb := M5.ArithmeticResidueRecovery.prefix_algebra T _ (u.drop (w - 1)) b
  simp [M5.ArithmeticResidueRecovery.wordValid,
    M5.ConditionalResidueCount.feasible,
    hlen, htake, hdrop,
    M5.ConditionalResidueCount.selectedGcd,
    ha.1, ha.2, hb.1, hb.2,
    Nat.gcd_assoc, Nat.gcd_comm, Nat.gcd_left_comm]
