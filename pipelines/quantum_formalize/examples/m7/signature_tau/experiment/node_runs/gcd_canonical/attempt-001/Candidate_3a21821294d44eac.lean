import FrozenTarget_3a21821294d44eac
theorem M7.SignatureTau.gcd_canonical : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ p : M6.Cyclic.BinaryPolynomial, _
  intro N inst p
  have hm : M6.Cyclic.modulus N ≠ 0 := (M7.SignatureTau.modulus_monic N).ne_zero
  have hd := EuclideanDomain.gcd_dvd_right p (M6.Cyclic.modulus N)
  have hs := EuclideanDomain.gcd_dvd_left (M6.Cyclic.modulus N) p
  have hg : EuclideanDomain.gcd p (M6.Cyclic.modulus N) ≠ 0 := by
    intro h
    rw [h] at hd
    exact hm (zero_dvd_iff.mp hd)
  have hk : EuclideanDomain.gcd (M6.Cyclic.modulus N) p ≠ 0 := by
    intro h
    rw [h] at hs
    exact hm (zero_dvd_iff.mp hs)
  have hgm := M7.SignatureTau.binary_monic _ hg
  have hkm := M7.SignatureTau.binary_monic _ hk
  refine ⟨hgm, hd, ?_⟩
  have hkg : EuclideanDomain.gcd (M6.Cyclic.modulus N) p ∣ EuclideanDomain.gcd p (M6.Cyclic.modulus N) :=
    EuclideanDomain.dvd_gcd (EuclideanDomain.gcd_dvd_right _ _) (EuclideanDomain.gcd_dvd_left _ _)
  have hgk : EuclideanDomain.gcd p (M6.Cyclic.modulus N) ∣ EuclideanDomain.gcd (M6.Cyclic.modulus N) p :=
    EuclideanDomain.dvd_gcd (EuclideanDomain.gcd_dvd_right _ _) (EuclideanDomain.gcd_dvd_left _ _)
  have hdeg := Polynomial.natDegree_le_of_dvd hgk hk
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le <;> assumption
