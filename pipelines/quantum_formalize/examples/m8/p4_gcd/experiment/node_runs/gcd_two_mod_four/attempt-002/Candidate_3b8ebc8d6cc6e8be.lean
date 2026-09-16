import FrozenTarget_3b8ebc8d6cc6e8be
theorem M8.P4Gcd.gcd_two_mod_four : QuantumHarnessFrozenTarget := by
  change ∀ m : ℕ, gcd M8.P4Family.polynomial (M6.Cyclic.modulus (4*m+2)) = (Polynomial.X+1)^2
  intro m
  have hmon : (((Polynomial.X : M6.Cyclic.BinaryPolynomial) + 1)^2).Monic := by
    exact (Polynomial.monic_X_add_C (1 : ZMod 2)).pow 2
  have hpow : ((Polynomial.X : M6.Cyclic.BinaryPolynomial) + 1)^3 = (Polynomial.X+1)^2 * (Polynomial.X+1) := by
    ring
  have hd : gcd (Polynomial.X+1) (M8.P4Gcd.oddCofactor m) ∣ 1 := by
    obtain ⟨a, b, hab⟩ := M8.P4Gcd.cofactor_coprime m
    rw [← hab]
    exact dvd_add
      (dvd_mul_of_dvd_right (gcd_dvd_left _ _) a)
      (dvd_mul_of_dvd_right (gcd_dvd_right _ _) b)
  have hg : gcd (Polynomial.X+1) (M8.P4Gcd.oddCofactor m) = 1 := by
    simpa using (gcd_eq_normalize hd (one_dvd _))
  rw [M8.P4Family.power_identity, M8.P4Gcd.factorization, hpow, gcd_mul_left,
    hmon.normalize_eq_self, hg, mul_one]
