import FrozenTarget_87d23c5ed6258b66
theorem M5.PolynomialIndicator.residual_factors_regular : QuantumHarnessFrozenTarget := by
  classical
  intro F N hN hF hdiv p hp
  have hq : M5.cyclicModulus N / F ≠ 0 :=
    M5.PolynomialExclusion.cyclic_quotient_nonzero F N hN hF hdiv
  have hmem : p ∈ UniqueFactorizationMonoid.normalizedFactors (M5.cyclicModulus N / F) := by
    simpa [M5.PolynomialExclusion.residualFactors, hq] using hp
  have hirr : Irreducible p :=
    UniqueFactorizationMonoid.irreducible_of_normalized_factor p hmem
  exact ⟨M5.Signature.binary_monic p hirr.ne_zero, hirr⟩
