import FrozenTarget_da78b580c563bef2
theorem M5.ArithmeticResidueRecovery.oracle_initial : QuantumHarnessFrozenTarget := by
  change ∀ (w : ℕ) (F : M5.BinaryPolynomial), M5.ArithmeticResidueRecovery.oracle w F [] = M5.ResidueCount.A w F
  intro w F
  classical
  simp [M5.ArithmeticResidueRecovery.oracle,
    M5.ConditionalResidueCount.conditionalA,
    M5.ConditionalResidueCount.conditionalAAt,
    M5.ConditionalResidueCount.rawConditionalA,
    M5.ConditionalResidueCount.fits,
    M5.ConditionalResidueCount.remaining,
    M5.ConditionalResidueCount.selectedGcd,
    M5.ConditionalResidueCount.prefixGcd,
    M5.ConditionalResidueCount.selectedPolynomial,
    M5.ConditionalResidueCount.RSelected,
    M5.ResidueCount.A, M5.ResidueCount.rawA,
    M5.ResidueCount.ROne, pow_two]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  split <;> simp_all
