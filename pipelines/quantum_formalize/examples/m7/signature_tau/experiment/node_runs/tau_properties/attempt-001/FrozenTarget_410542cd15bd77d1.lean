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

theorem M7.SignatureTau.gcd_canonical : ∀ (N : ℕ) [NeZero N], ∀ p : M6.Cyclic.BinaryPolynomial, (EuclideanDomain.gcd p (M6.Cyclic.modulus N)).Monic ∧ EuclideanDomain.gcd p (M6.Cyclic.modulus N) ∣ (M6.Cyclic.modulus N) ∧ EuclideanDomain.gcd (M6.Cyclic.modulus N) p = EuclideanDomain.gcd p (M6.Cyclic.modulus N) := by
  change ∀ (N : ℕ) [NeZero N], ∀ p : M6.Cyclic.BinaryPolynomial, (EuclideanDomain.gcd p (M6.Cyclic.modulus N)).Monic ∧ EuclideanDomain.gcd p (M6.Cyclic.modulus N) ∣ M6.Cyclic.modulus N ∧ EuclideanDomain.gcd (M6.Cyclic.modulus N) p = EuclideanDomain.gcd p (M6.Cyclic.modulus N)
  intro N inst p
  have hm : M6.Cyclic.modulus N ≠ 0 := (M7.SignatureTau.modulus_monic N).ne_zero
  have hd := EuclideanDomain.gcd_dvd_right p (M6.Cyclic.modulus N)
  have hs := EuclideanDomain.gcd_dvd_left (M6.Cyclic.modulus N) p
  have hg : EuclideanDomain.gcd p (M6.Cyclic.modulus N) ≠ 0 := by
    intro h
    apply hm
    simpa only [h, zero_dvd_iff] using hd
  have hk : EuclideanDomain.gcd (M6.Cyclic.modulus N) p ≠ 0 := by
    intro h
    apply hm
    simpa only [h, zero_dvd_iff] using hs
  have hgm := M7.SignatureTau.binary_monic _ hg
  have hkm := M7.SignatureTau.binary_monic _ hk
  have hkg : EuclideanDomain.gcd (M6.Cyclic.modulus N) p ∣ EuclideanDomain.gcd p (M6.Cyclic.modulus N) :=
    EuclideanDomain.dvd_gcd (EuclideanDomain.gcd_dvd_right _ _) hs
  have hgk : EuclideanDomain.gcd p (M6.Cyclic.modulus N) ∣ EuclideanDomain.gcd (M6.Cyclic.modulus N) p :=
    EuclideanDomain.dvd_gcd hd (EuclideanDomain.gcd_dvd_left _ _)
  refine ⟨hgm, hd, ?_⟩
  exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le hgm hkm hgk
    (Polynomial.natDegree_le_of_dvd hkg hg)
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (F : M6.Cyclic.BinaryPolynomial), (M7.SignatureTau.tau u F).Monic ∧ M7.SignatureTau.tau u F ∣ (M6.Cyclic.modulus N)
