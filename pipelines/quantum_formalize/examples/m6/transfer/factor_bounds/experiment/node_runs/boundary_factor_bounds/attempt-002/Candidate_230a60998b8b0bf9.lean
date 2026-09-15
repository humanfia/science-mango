import FrozenTarget_230a60998b8b0bf9
theorem M6.Transfer.boundary_factor_bounds : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (m : ℕ) (P : M6.Pinned.Pins m) (i : Fin m) (s : ZMod 2), M6.Transfer.polynomialMass (M6.Character.boundaryFactor P i s) ≤ 1 ∧ (M6.Character.boundaryFactor P i s).natDegree ≤ 1
  intro m P i s
  unfold M6.Character.boundaryFactor
  split_ifs with h
  · constructor
    · have hx : Polynomial.monomial s.val (1 : ℤ) = (Polynomial.X : Polynomial ℤ) ^ s.val := by
        ext n
        simp [Polynomial.coeff_X_pow, eq_comm]
      have hm := M6.Transfer.mass_basic.2.2.1 s.val (1 : ℤ)
      rw [hx] at hm
      simpa using le_of_eq hm
    · have hs := ZMod.val_lt s
      simp only [Polynomial.natDegree_X_pow]
      omega
  · constructor
    · simp [M6.Transfer.mass_basic.1]
    · simp
