import FrozenTarget_86eb945411486c7c
theorem M7.AffinePolynomial.rho_power_unit : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ s : ZMod N, IsUnit (M7.CyclicSubstitution.rho N ^ s.val)
  intro N inst s
  have hN : 1 ≤ N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hu : IsUnit (M7.CyclicSubstitution.rho N) := by
    refine ⟨{ val := M7.CyclicSubstitution.rho N
              inv := M7.CyclicSubstitution.rho N ^ (N - 1)
              val_inv := ?_
              inv_val := ?_ }, rfl⟩
    · rw [← pow_succ', Nat.sub_add_cancel hN, M7.CyclicSubstitution.root_power N]
    · rw [← pow_succ, Nat.sub_add_cancel hN, M7.CyclicSubstitution.root_power N]
  exact hu.pow s.val
