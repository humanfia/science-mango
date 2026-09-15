import FrozenTarget_0551ceca3833507b
theorem M5.ArithmeticResidueRecovery.completion_feasible : QuantumHarnessFrozenTarget := by
  intro T w F u a b hu
  classical
  rcases M5.ArithmeticResidueRecovery.completion_word_split (w - 1) u a b hu with ⟨hlen, hprefix, htake, hdrop⟩
  rcases M5.ArithmeticResidueRecovery.prefix_algebra T _ (u.take (w - 1)) a with ⟨hpa, hga⟩
  rcases M5.ArithmeticResidueRecovery.prefix_algebra T _ (u.drop (w - 1)) b with ⟨hpb, hgb⟩
  have hta : (u.take (w - 1)).length ≤ w - 1 := by
    simp only [List.length_take]
    omega
  have hdb : (u.drop (w - 1)).length ≤ w - 1 := by
    simp only [List.length_drop]
    omega
  simp [M5.ArithmeticResidueRecovery.wordValid,
    M5.ConditionalResidueCount.feasible,
    M5.ConditionalResidueCount.selectedGcd,
    M5.ConditionalResidueCount.fits,
    hlen, htake, hdrop, hpa, hpb, hga, hgb, hta, hdb,
    Nat.gcd_assoc, Nat.gcd_comm, Nat.gcd_left_comm]
