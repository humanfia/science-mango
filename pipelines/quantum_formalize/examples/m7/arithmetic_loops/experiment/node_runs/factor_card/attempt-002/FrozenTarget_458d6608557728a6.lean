import M7ArithmeticLoops


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ F : M5.BinaryPolynomial, F.Monic → F ∣ M5.cyclicModulus N → (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).card ≤ M7.ArithmeticLoops.factorCount N
