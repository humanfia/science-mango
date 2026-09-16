import M7CyclicSubstitution

theorem M7.CyclicSubstitution.hom_polynomial : ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (h : M7.CyclicSubstitution.RootCondition u) (p : M6.Cyclic.BinaryPolynomial), M7.CyclicSubstitution.hom u h (M6.Cyclic.image N p) = p.eval₂ (AdjoinRoot.of (M6.Cyclic.modulus N)) (M7.CyclicSubstitution.point u) := by
  intro N inst u h p
  unfold M7.CyclicSubstitution.hom M6.Cyclic.image
  exact AdjoinRoot.lift_mk h p

theorem M7.CyclicSubstitution.hom_root : ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (h : M7.CyclicSubstitution.RootCondition u), M7.CyclicSubstitution.hom u h (M7.CyclicSubstitution.rho N) = M7.CyclicSubstitution.point u := by
  intro N inst u h
  unfold M7.CyclicSubstitution.hom M7.CyclicSubstitution.rho
  exact AdjoinRoot.lift_root h

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

theorem M7.CyclicSubstitution.point_root : ∀ (N : ℕ) [NeZero N], ∀ u : (ZMod N)ˣ, M7.CyclicSubstitution.RootCondition u := by
  change ∀ (N : ℕ) [NeZero N], ∀ u : (ZMod N)ˣ, M7.CyclicSubstitution.RootCondition u
  intro N _ u
  change (Polynomial.X ^ N + 1 : M6.Cyclic.BinaryPolynomial).eval₂
    (AdjoinRoot.of (M6.Cyclic.modulus N))
    (M7.CyclicSubstitution.rho N ^ (u : ZMod N).val) = 0
  rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_one]
  have hp : (M7.CyclicSubstitution.rho N ^ (u : ZMod N).val) ^ N = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, M7.CyclicSubstitution.root_power, one_pow]
  rw [hp]
  have h := congrArg (AdjoinRoot.of (M6.Cyclic.modulus N))
    (show (1 : ZMod 2) + 1 = 0 by decide)
  simpa only [map_add, map_one, map_zero] using h

theorem M7.CyclicSubstitution.power_mod : ∀ (N : ℕ) [NeZero N], ∀ k : ℕ, M7.CyclicSubstitution.rho N ^ k = M7.CyclicSubstitution.rho N ^ (k % N) := by
  change ∀ (N : ℕ) [NeZero N], ∀ k : ℕ, M7.CyclicSubstitution.rho N ^ k = M7.CyclicSubstitution.rho N ^ (k % N)
  intro N _ k
  calc
    M7.CyclicSubstitution.rho N ^ k =
        M7.CyclicSubstitution.rho N ^ (k % N + N * (k / N)) :=
      congrArg (fun n : ℕ => M7.CyclicSubstitution.rho N ^ n) (Nat.mod_add_div k N).symm
    _ = M7.CyclicSubstitution.rho N ^ (k % N) := by
      rw [pow_add, pow_mul, M7.CyclicSubstitution.root_power N, one_pow, mul_one]

theorem M7.CyclicSubstitution.point_mul : ∀ (N : ℕ) [NeZero N], ∀ u v : (ZMod N)ˣ, M7.CyclicSubstitution.point u ^ (v : ZMod N).val = M7.CyclicSubstitution.point (v*u) := by
  change ∀ (N : ℕ) [NeZero N], ∀ u v : (ZMod N)ˣ, M7.CyclicSubstitution.point u ^ (v : ZMod N).val = M7.CyclicSubstitution.point (v * u)
  intro N _ u v
  change (M7.CyclicSubstitution.rho N ^ (u : ZMod N).val) ^ (v : ZMod N).val = M7.CyclicSubstitution.rho N ^ ((v : ZMod N) * (u : ZMod N)).val
  rw [← pow_mul, ZMod.val_mul]
  simpa only [Nat.mul_comm] using M7.CyclicSubstitution.power_mod N ((u : ZMod N).val * (v : ZMod N).val)

theorem M7.CyclicSubstitution.point_one : ∀ (N : ℕ) [NeZero N], M7.CyclicSubstitution.point (1 : (ZMod N)ˣ) = M7.CyclicSubstitution.rho N := by
  change ∀ (N : ℕ) [NeZero N], M7.CyclicSubstitution.point (1 : (ZMod N)ˣ) = M7.CyclicSubstitution.rho N
  intro N _
  unfold M7.CyclicSubstitution.point
  simp only [Units.val_one]
  have h : (1 : ZMod N).val = 1 % N := by
    simpa only [Nat.cast_one] using (ZMod.val_natCast N 1)
  rw [h]
  exact (M7.CyclicSubstitution.power_mod N 1).symm.trans (pow_one _)

theorem M7.CyclicSubstitution.point_inverse : ∀ (N : ℕ) [NeZero N], ∀ u : (ZMod N)ˣ, M7.CyclicSubstitution.point u ^ ((u⁻¹ : (ZMod N)ˣ) : ZMod N).val = M7.CyclicSubstitution.rho N := by
  change ∀ (N : ℕ) [NeZero N], ∀ u : (ZMod N)ˣ, M7.CyclicSubstitution.point u ^ ((u⁻¹ : (ZMod N)ˣ) : ZMod N).val = M7.CyclicSubstitution.rho N
  intro N _ u
  rw [M7.CyclicSubstitution.point_mul N u u⁻¹, inv_mul_cancel, M7.CyclicSubstitution.point_one N]
#print axioms M7.CyclicSubstitution.hom_polynomial
#print axioms M7.CyclicSubstitution.hom_root
#print axioms M7.CyclicSubstitution.root_power
#print axioms M7.CyclicSubstitution.point_root
#print axioms M7.CyclicSubstitution.power_mod
#print axioms M7.CyclicSubstitution.point_mul
#print axioms M7.CyclicSubstitution.point_one
#print axioms M7.CyclicSubstitution.point_inverse
