import FrozenTarget_23b3420477d969a4
theorem M7.CyclicSubstitution.power_mod : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ k : ℕ, M7.CyclicSubstitution.rho N ^ k = M7.CyclicSubstitution.rho N ^ (k % N)
  intro N _ k
  calc
    M7.CyclicSubstitution.rho N ^ k =
        M7.CyclicSubstitution.rho N ^ (k % N + N * (k / N)) :=
      congrArg (fun n : ℕ => M7.CyclicSubstitution.rho N ^ n) (Nat.mod_add_div k N).symm
    _ = M7.CyclicSubstitution.rho N ^ (k % N) := by
      rw [pow_add, pow_mul, M7.CyclicSubstitution.root_power N, one_pow, mul_one]
