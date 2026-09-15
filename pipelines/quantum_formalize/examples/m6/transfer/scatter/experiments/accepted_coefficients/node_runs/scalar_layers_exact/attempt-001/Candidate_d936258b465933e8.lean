import FrozenTarget_d936258b465933e8
theorem M6.Transfer.scalar_layers_exact : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (R N : ℕ) (W : ℕ → M6.Transfer.Memory R → M6.Transfer.Bit → Polynomial ℤ) (start : M6.Transfer.Memory R) (k : ℕ), (∀ i m t, (W i m t).natDegree ≤ 2) → M6.Transfer.scalarLayers (N := N) W start k = M6.Transfer.encodeCoefficients (M6.Transfer.layers W start k)
  intro R N W start k hW
  induction k with
  | zero =>
      funext addr
      by_cases hm : addr.1 = start <;>
        by_cases hd : addr.2.val = 0 <;>
        simp [M6.Transfer.scalarLayers, M6.Transfer.encodeCoefficients,
          M6.Transfer.layers, hm, hd]
  | succ k ih =>
      change M6.Transfer.scatterLayer (W k) (M6.Transfer.scalarLayers W start k) =
        M6.Transfer.encodeCoefficients (M6.Transfer.propagate (W k) (M6.Transfer.layers W start k))
      rw [ih]
      funext addr
      exact M6.Transfer.scatter_polynomial_coeff R N (W k)
        (M6.Transfer.layers W start k) addr (hW k)
