import FrozenTarget_d1c2ce84c43f76f6
theorem M7.SignatureIdeal.monic_injective : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ F E : M6.Cyclic.BinaryPolynomial, F.Monic → E.Monic → F ∣ M6.Cyclic.modulus N → E ∣ M6.Cyclic.modulus N → (M7.SignatureIdeal.principal N F = M7.SignatureIdeal.principal N E ↔ F = E)
  intro N inst F E hFm hEm hF hE
  constructor
  · intro h
    have hFE : F ∣ E := by
      apply (M7.SignatureIdeal.quotient_membership N F E hF).mp
      rw [h]
      exact (M7.SignatureIdeal.quotient_membership N E E hE).mpr (dvd_refl E)
    have hEF : E ∣ F := by
      apply (M7.SignatureIdeal.quotient_membership N E F hE).mp
      rw [← h]
      exact (M7.SignatureIdeal.quotient_membership N F F hF).mpr (dvd_refl F)
    exact hFm.dvd_antisymm hEm hFE hEF
  · intro h
    subst E
    rfl
