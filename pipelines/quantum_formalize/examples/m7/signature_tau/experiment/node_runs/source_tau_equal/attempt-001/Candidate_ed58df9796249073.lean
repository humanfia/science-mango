import FrozenTarget_ed58df9796249073
theorem M7.SignatureTau.source_tau_equal : QuantumHarnessFrozenTarget := by
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
