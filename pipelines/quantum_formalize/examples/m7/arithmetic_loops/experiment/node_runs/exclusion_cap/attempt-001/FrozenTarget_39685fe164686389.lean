import M7ArithmeticLoops


def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (F : M5.BinaryPolynomial) (S : Finset M5.BinaryPolynomial), F.Monic → F ∣ M5.cyclicModulus N → S ⊆ M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F → (F * (∏ p ∈ S, p)).Monic ∧ (F * (∏ p ∈ S, p)).natDegree ≤ N
