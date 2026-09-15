import FrozenTarget_12ef98da40f319c6
theorem M5.Final.actual_residue_recovery : QuantumHarnessFrozenTarget := by
  change ∀ (w : ℕ) (F : M5.BinaryPolynomial), 0 < w → F.Monic → F.coeff 0 = 1 → M5.Final.ResidueRecoveryClause w F
  intro w F hw hmonic hcoeff
  unfold M5.Final.ResidueRecoveryClause
  exact M5.ArithmeticResidueRecovery.recovery_correct w F hw hmonic hcoeff
