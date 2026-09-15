import FrozenTarget_8a7a4bb608645783
theorem M6.Transfer.scalar_layers_exact : QuantumHarnessFrozenTarget := by
  classical
  intro R N W start k hW
  induction k with
  | zero =>
      funext addr
      by_cases hm : addr.1 = start
      · simp only [M6.Transfer.scalarLayers, M6.Transfer.encodeCoefficients,
          M6.Transfer.layers, hm, ite_true, true_and]
        rw [show (1 : Polynomial ℤ) = Polynomial.C 1 by simp]
        simp [Polynomial.coeff_C, eq_comm]
      · simp [M6.Transfer.scalarLayers, M6.Transfer.encodeCoefficients,
          M6.Transfer.layers, hm]
  | succ k ih =>
      change M6.Transfer.scatterLayer (W k)
        (M6.Transfer.scalarLayers W start k) =
        M6.Transfer.encodeCoefficients
          (M6.Transfer.propagate (W k) (M6.Transfer.layers W start k))
      rw [ih]
      funext addr
      exact M6.Transfer.scatter_polynomial_coeff R N (W k)
        (M6.Transfer.layers W start k) addr (hW k)
