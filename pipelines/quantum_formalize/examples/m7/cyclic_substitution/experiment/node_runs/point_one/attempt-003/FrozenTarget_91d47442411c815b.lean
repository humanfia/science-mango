import M7CyclicSubstitution

theorem M7.CyclicSubstitution.root_power : ∀ (N : ℕ) [NeZero N], M7.CyclicSubstitution.rho N ^ N = 1 := by
  change ∀ (N : ℕ) [NeZero N], M7.CyclicSubstitution.rho N ^ N = 1
  intro N _
  have hroot := AdjoinRoot.eval₂_root (M6.Cyclic.modulus N)
  change (Polynomial.X ^ N + 1 : M6.Cyclic.BinaryPolynomial).eval₂
    (AdjoinRoot.of (M6.Cyclic.modulus N)) (M7.CyclicSubstitution.rho N) = 0 at hroot
  rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_one] at hroot
  have htwo : (1 : M6.Cyclic.CycleRing N) + 1 = 0 := by
    have h := congrArg (AdjoinRoot.of (M6.Cyclic.modulus N))
      (show (1 : ZMod 2) + 1 = 0 by decide)
    simpa only [map_add, map_one, map_zero] using h
  exact add_right_cancel (hroot.trans htwo.symm)

theorem M7.CyclicSubstitution.power_mod : ∀ (N : ℕ) [NeZero N], ∀ k : ℕ, M7.CyclicSubstitution.rho N ^ k = M7.CyclicSubstitution.rho N ^ (k % N) := by
  change ∀ (N : ℕ) [NeZero N], ∀ k : ℕ, M7.CyclicSubstitution.rho N ^ k = M7.CyclicSubstitution.rho N ^ (k % N)
  intro N _ k
  calc
    M7.CyclicSubstitution.rho N ^ k =
        M7.CyclicSubstitution.rho N ^ (k % N + N * (k / N)) :=
      congrArg (fun n : ℕ => M7.CyclicSubstitution.rho N ^ n) (Nat.mod_add_div k N).symm
    _ = M7.CyclicSubstitution.rho N ^ (k % N) := by
      rw [pow_add, pow_mul, M7.CyclicSubstitution.root_power N, one_pow, mul_one]
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], M7.CyclicSubstitution.point (1 : (ZMod N)ˣ) = M7.CyclicSubstitution.rho N
