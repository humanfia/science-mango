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

theorem M7.SignatureTau.tau_principal : ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (F : M6.Cyclic.BinaryPolynomial), M7.SignatureIdeal.principal N (M7.SignatureTau.tau u F) = (M7.SignatureIdeal.principal N F).map (M7.QuotientAuto.substitution u) := by
  intro N inst u F
  unfold M7.SignatureTau.tau
  rw [← M7.SignatureIdeal.principal_gcd]
  simp only [M7.SignatureIdeal.principal, M7.SignatureTau.substituted,
    Ideal.map_span, Set.image_singleton,
    M7.QuotientAuto.polynomial_substitution]

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

theorem M7.SignatureTau.reduced_image : ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (F : M6.Cyclic.BinaryPolynomial), M6.Cyclic.image N (M7.SignatureTau.reduced u F) = M7.QuotientAuto.substitution u (M6.Cyclic.image N F) := by
  change ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (F : M6.Cyclic.BinaryPolynomial), M6.Cyclic.image N (M7.SignatureTau.reduced u F) = M7.QuotientAuto.substitution u (M6.Cyclic.image N F)
  intro N inst u F
  rw [← M7.QuotientAuto.polynomial_substitution N u F]
  change AdjoinRoot.mk (M6.Cyclic.modulus N) ((F.comp (Polynomial.X ^ (u : ZMod N).val)) %ₘ M6.Cyclic.modulus N) = AdjoinRoot.mk (M6.Cyclic.modulus N) (F.comp (Polynomial.X ^ (u : ZMod N).val))
  simpa only [AdjoinRoot.modByMonicHom_mk] using
    (AdjoinRoot.mk_leftInverse (M7.SignatureTau.modulus_monic N)
      (AdjoinRoot.mk (M6.Cyclic.modulus N) (F.comp (Polynomial.X ^ (u : ZMod N).val))))

theorem M7.SignatureTau.tau_properties : ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (F : M6.Cyclic.BinaryPolynomial), (M7.SignatureTau.tau u F).Monic ∧ M7.SignatureTau.tau u F ∣ (M6.Cyclic.modulus N) := by
  change ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (F : M6.Cyclic.BinaryPolynomial), (M7.SignatureTau.tau u F).Monic ∧ M7.SignatureTau.tau u F ∣ M6.Cyclic.modulus N
  intro N inst u F
  unfold M7.SignatureTau.tau
  exact ⟨(M7.SignatureTau.gcd_canonical N _).1, (M7.SignatureTau.gcd_canonical N _).2.1⟩

theorem M7.SignatureTau.source_tau_equal : ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (F : M6.Cyclic.BinaryPolynomial), M7.SignatureTau.sourceTau u F = M7.SignatureTau.tau u F := by
  change ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (F : M6.Cyclic.BinaryPolynomial), M7.SignatureTau.sourceTau u F = M7.SignatureTau.tau u F
  intro N inst u F
  change EuclideanDomain.gcd (M6.Cyclic.modulus N) (M7.SignatureTau.reduced u F) = EuclideanDomain.gcd (M7.SignatureTau.substituted u F) (M6.Cyclic.modulus N)
  rw [(M7.SignatureTau.gcd_canonical N (M7.SignatureTau.reduced u F)).2.2]
  have hr := M7.SignatureTau.gcd_canonical N (M7.SignatureTau.reduced u F)
  have hs := M7.SignatureTau.gcd_canonical N (M7.SignatureTau.substituted u F)
  apply (M7.SignatureIdeal.monic_injective N _ _ hr.1 hs.1 hr.2.1 hs.2.1).mp
  rw [← M7.SignatureIdeal.principal_gcd N (M7.SignatureTau.reduced u F),
    ← M7.SignatureIdeal.principal_gcd N (M7.SignatureTau.substituted u F)]
  have hi : M6.Cyclic.image N (M7.SignatureTau.reduced u F) = M6.Cyclic.image N (M7.SignatureTau.substituted u F) := by
    rw [M7.SignatureTau.reduced_image N u F]
    exact (M7.QuotientAuto.polynomial_substitution N u F).symm
  unfold M7.SignatureIdeal.principal
  rw [hi]

theorem M7.SignatureTau.tau_comp : ∀ (N : ℕ) [NeZero N], ∀ (u v : (ZMod N)ˣ) (F : M6.Cyclic.BinaryPolynomial), F.Monic → F ∣ (M6.Cyclic.modulus N) → M7.SignatureTau.tau v (M7.SignatureTau.tau u F) = M7.SignatureTau.tau (v*u) F := by
  change ∀ (N : ℕ) [NeZero N], ∀ (u v : (ZMod N)ˣ) (F : M6.Cyclic.BinaryPolynomial), F.Monic → F ∣ M6.Cyclic.modulus N → M7.SignatureTau.tau v (M7.SignatureTau.tau u F) = M7.SignatureTau.tau (v * u) F
  intro N inst u v F hF hdiv
  have hL := M7.SignatureTau.tau_properties N v (M7.SignatureTau.tau u F)
  have hR := M7.SignatureTau.tau_properties N (v * u) F
  apply (M7.SignatureIdeal.monic_injective N _ _ hL.1 hR.1 hL.2 hR.2).mp
  rw [M7.SignatureTau.tau_principal N v,
    M7.SignatureTau.tau_principal N u,
    M7.SignatureTau.tau_principal N (v * u),
    Ideal.map_map, M7.QuotientAuto.substitution_comp N u v]

theorem M7.SignatureTau.tau_one : ∀ (N : ℕ) [NeZero N], ∀ F : M6.Cyclic.BinaryPolynomial, F.Monic → F ∣ (M6.Cyclic.modulus N) → M7.SignatureTau.tau (1 : (ZMod N)ˣ) F = F := by
  change ∀ (N : ℕ) [NeZero N], ∀ F : M6.Cyclic.BinaryPolynomial, F.Monic → F ∣ M6.Cyclic.modulus N → M7.SignatureTau.tau (1 : (ZMod N)ˣ) F = F
  intro N inst F hF hdF
  have ht := M7.SignatureTau.tau_properties N (1 : (ZMod N)ˣ) F
  apply (M7.SignatureIdeal.monic_injective N _ F ht.1 hF ht.2 hdF).mp
  rw [M7.SignatureTau.tau_principal, M7.QuotientAuto.substitution_one, Ideal.map_id]

theorem M7.SignatureTau.tau_inverse : ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (F : M6.Cyclic.BinaryPolynomial), F.Monic → F ∣ (M6.Cyclic.modulus N) → (M7.SignatureTau.tau (u⁻¹) (M7.SignatureTau.tau u F) = F ∧ M7.SignatureTau.tau u (M7.SignatureTau.tau (u⁻¹) F) = F) := by
  change ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (F : M6.Cyclic.BinaryPolynomial), F.Monic → F ∣ M6.Cyclic.modulus N → (M7.SignatureTau.tau (u⁻¹) (M7.SignatureTau.tau u F) = F ∧ M7.SignatureTau.tau u (M7.SignatureTau.tau (u⁻¹) F) = F)
  intro N inst u F hF hdiv
  constructor
  · rw [M7.SignatureTau.tau_comp N u (u⁻¹) F hF hdiv, inv_mul_cancel]
    exact M7.SignatureTau.tau_one N F hF hdiv
  · rw [M7.SignatureTau.tau_comp N (u⁻¹) u F hF hdiv, mul_inv_cancel]
    exact M7.SignatureTau.tau_one N F hF hdiv
#print axioms M7.SignatureTau.binary_monic
#print axioms M7.SignatureTau.modulus_monic
#print axioms M7.SignatureTau.gcd_canonical
#print axioms M7.SignatureTau.reduced_image
#print axioms M7.SignatureTau.tau_principal
#print axioms M7.SignatureTau.tau_properties
#print axioms M7.SignatureTau.source_tau_equal
#print axioms M7.SignatureTau.tau_comp
#print axioms M7.SignatureTau.tau_one
#print axioms M7.SignatureTau.tau_inverse
