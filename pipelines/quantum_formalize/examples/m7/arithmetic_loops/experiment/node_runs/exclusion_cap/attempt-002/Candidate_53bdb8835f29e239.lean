import FrozenTarget_53bdb8835f29e239
theorem M7.ArithmeticLoops.exclusion_cap : QuantumHarnessFrozenTarget := by
  classical
  intro N hN F S hF hFdvd hS
  have hmonic : (F * (∏ p ∈ S, p)).Monic := by
    apply hF.mul
    apply Polynomial.monic_prod_of_monic
    intro p hp
    exact (M5.PolynomialIndicator.residual_factors_regular F N hN hF hFdvd p (hS hp)).1
  have hdvd : F * (∏ p ∈ S, p) ∣ M5.cyclicModulus N := by
    apply M5.FactorProduct.cyclic_cap <;> assumption
  have hne : M5.cyclicModulus N ≠ 0 := by
    intro hz
    have hq := M5.PolynomialExclusion.cyclic_quotient_nonzero F N hN hF hFdvd
    apply hq
    simp [hz]
  have hdeg : (M5.cyclicModulus N).natDegree ≤ N := by
    simpa [M5.cyclicModulus] using
      (Polynomial.natDegree_add_le ((Polynomial.X : M5.BinaryPolynomial) ^ N) 1)
  exact ⟨hmonic, (Polynomial.natDegree_le_of_dvd hdvd hne).trans hdeg⟩
