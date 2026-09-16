import FrozenTarget_7a138f7d75f22c87
theorem M8.P4Gcd.gcd_two_mod_four : QuantumHarnessFrozenTarget := by
  change ∀ m : ℕ, gcd M8.P4Family.polynomial (M6.Cyclic.modulus (4*m+2)) = (Polynomial.X+1)^2
  intro m
  rw [M8.P4Family.power_identity, M8.P4Gcd.factorization]
  have hmon : (((Polynomial.X : Polynomial (ZMod 2)) + 1)^2).Monic := by
    simpa using (Polynomial.monic_X_add_C (1 : ZMod 2)).pow 2
  have hpow : ((Polynomial.X : Polynomial (ZMod 2)) + 1)^3 =
      (Polynomial.X + 1)^2 * (Polynomial.X + 1) := by ring
  rw [hpow, gcd_mul_left, (M8.P4Gcd.cofactor_coprime m).gcd_eq_one, mul_one,
    hmon.normalize_eq_self]
