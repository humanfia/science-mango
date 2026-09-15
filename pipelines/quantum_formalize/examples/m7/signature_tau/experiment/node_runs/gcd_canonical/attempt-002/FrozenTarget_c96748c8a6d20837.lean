import M7SignatureTau

theorem M7.SignatureTau.binary_monic : ∀ F : M6.Cyclic.BinaryPolynomial, F ≠ 0 → F.Monic := by
  change ∀ F : M6.Cyclic.BinaryPolynomial, F ≠ 0 → F.Monic
  intro F hF
  change F.leadingCoeff = 1
  have hbinary : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  exact hbinary F.leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr hF)

theorem M7.SignatureTau.modulus_monic : ∀ (N : ℕ) [NeZero N], (M6.Cyclic.modulus N).Monic := by
  change ∀ (N : ℕ) [NeZero N], (M6.Cyclic.modulus N).Monic
  intro N inst
  change (Polynomial.X ^ N + 1 : Polynomial (ZMod 2)).Monic
  simpa only [Polynomial.C_1] using
    (Polynomial.monic_X_pow_add_C (1 : ZMod 2) (NeZero.ne N))
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ p : M6.Cyclic.BinaryPolynomial, (EuclideanDomain.gcd p (M6.Cyclic.modulus N)).Monic ∧ EuclideanDomain.gcd p (M6.Cyclic.modulus N) ∣ (M6.Cyclic.modulus N) ∧ EuclideanDomain.gcd (M6.Cyclic.modulus N) p = EuclideanDomain.gcd p (M6.Cyclic.modulus N)
