import FrozenTarget_465e3c9cdaee1405
theorem M7.SignatureTau.tau_principal : QuantumHarnessFrozenTarget := by
  intro N inst u F
  unfold M7.SignatureTau.tau
  rw [← M7.SignatureIdeal.principal_gcd]
  simp only [M7.SignatureIdeal.principal, M7.SignatureTau.substituted,
    Ideal.map_span, Set.image_singleton,
    M7.QuotientAuto.polynomial_substitution]
