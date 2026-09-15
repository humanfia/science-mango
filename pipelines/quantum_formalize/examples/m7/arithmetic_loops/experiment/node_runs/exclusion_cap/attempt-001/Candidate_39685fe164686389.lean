import FrozenTarget_39685fe164686389
theorem M7.ArithmeticLoops.exclusion_cap : QuantumHarnessFrozenTarget := by
  classical
  intro N hN F S hF hdiv hS
  have hprod : (∏ p ∈ S, p).Monic := by
    apply Polynomial.monic_prod_of_monic
    intro p hp
    exact (M5.PolynomialIndicator.residual_factors_regular F N hN hF hdiv p (hS hp)).1
  have hcap : F * (∏ p ∈ S, p) ∣ M5.cyclicModulus N := by
    apply M5.FactorProduct.cyclic_cap <;>
      first | assumption | exact hF.ne_zero
  have hnonzero : M5.cyclicModulus N ≠ 0 := by
    intro h
    have hc := congrArg (fun p : M5.BinaryPolynomial => p.coeff N) h
    simpa [M5.cyclicModulus, Polynomial.coeff_X_pow, Nat.ne_of_gt hN, Ne.symm (Nat.ne_of_gt hN)] using hc
  refine ⟨hF.mul hprod, (Polynomial.natDegree_le_of_dvd hcap hnonzero).trans ?_⟩
  change (Polynomial.X ^ N + (1 : M5.BinaryPolynomial)).natDegree ≤ N
  simpa using (Polynomial.natDegree_add_le ((Polynomial.X : M5.BinaryPolynomial) ^ N) 1)
