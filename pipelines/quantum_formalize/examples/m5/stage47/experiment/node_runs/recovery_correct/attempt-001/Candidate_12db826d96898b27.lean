import FrozenTarget_12db826d96898b27
theorem M5.ArithmeticResidueRecovery.recovery_correct : QuantumHarnessFrozenTarget := by
  intro w F hw hF hF0 hA
  have h := M5.ArithmeticResidueRecovery.oracle_partition_terminal w F hw hF hF0
  have hpos : 0 < M5.ArithmeticResidueRecovery.oracle w F [] := by
    rw [M5.ArithmeticResidueRecovery.oracle_initial]
    exact hA
  simpa only [M5.ArithmeticResidueRecovery.recover] using
    (M5.ResidueRecovery.recover_valid (M5.signaturePeriod F)
      (M5.ArithmeticResidueRecovery.oracle w F)
      (M5.ArithmeticResidueRecovery.wordValid w F)
      (2 * (w - 1)) h.1 h.2 hpos)
