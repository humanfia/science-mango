import FrozenTarget_74fa60c806e88d4a
theorem M6.Transfer.boundary_factor_bounds : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (m : ℕ) (P : M6.Pinned.Pins m) (i : Fin m) (s : ZMod 2), _
  intro m P i s
  unfold M6.Character.boundaryFactor
  split_ifs with h
  · constructor
    · have hm := M6.Transfer.mass_basic.2.2.1 s.val (1 : ℤ)
      have hx : M6.Transfer.polynomialMass ((Polynomial.X : Polynomial ℤ) ^ s.val) = 1 := by
        simpa only [Polynomial.monomial_one_right, Int.natAbs_one] using hm
      exact hx.le
    · simpa only [Polynomial.natDegree_X_pow] using (Nat.le_of_lt_succ (ZMod.val_lt s))
  · constructor
    · rw [M6.Transfer.mass_basic.1]
      decide
    · simp
