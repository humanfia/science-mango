import FrozenTarget_a2b62468a3361ec9
theorem M6.Transfer.scalar_layers_exact : QuantumHarnessFrozenTarget := by
  classical
  intro R N W start k hW
  induction k with
  | zero =>
      funext addr
      change (if addr.1 = start ∧ addr.2.val = 0 then (1 : ℤ) else 0) =
        (if addr.1 = start then (1 : Polynomial ℤ) else 0).coeff addr.2.val
      by_cases hm : addr.1 = start
      · rw [if_pos hm]
        change (if addr.1 = start ∧ addr.2.val = 0 then (1 : ℤ) else 0) =
          (Polynomial.C (1 : ℤ)).coeff addr.2.val
        rw [Polynomial.coeff_C]
        simp [hm, eq_comm]
      · simp [hm]
  | succ k ih =>
      change M6.Transfer.scatterLayer (W k) (M6.Transfer.scalarLayers W start k) =
        M6.Transfer.encodeCoefficients (M6.Transfer.propagate (W k) (M6.Transfer.layers W start k))
      rw [ih]
      funext addr
      exact M6.Transfer.scatter_polynomial_coeff R N (W k)
        (M6.Transfer.layers W start k) addr (hW k)
