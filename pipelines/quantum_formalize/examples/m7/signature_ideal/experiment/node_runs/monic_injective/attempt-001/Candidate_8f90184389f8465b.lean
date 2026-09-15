import FrozenTarget_8f90184389f8465b
theorem M7.SignatureIdeal.monic_injective : QuantumHarnessFrozenTarget := by
  by
    change ∀ (N : ℕ) [NeZero N], ∀ F E : M6.Cyclic.BinaryPolynomial, F.Monic → E.Monic → F ∣ M6.Cyclic.modulus N → E ∣ M6.Cyclic.modulus N → (M7.SignatureIdeal.principal N F = M7.SignatureIdeal.principal N E ↔ F = E)
    intro N inst F E hF hE hFM hEM
    constructor
    · intro h
      have hFE : F ∣ E := by
        apply (M7.SignatureIdeal.quotient_membership N F E hFM).mp
        rw [h]
        exact (M7.SignatureIdeal.quotient_membership N E E hEM).mpr (dvd_refl E)
      have hEF : E ∣ F := by
        apply (M7.SignatureIdeal.quotient_membership N E F hEM).mp
        rw [← h]
        exact (M7.SignatureIdeal.quotient_membership N F F hFM).mpr (dvd_refl F)
      exact Polynomial.Monic.dvd_antisymm hF hE hFE hEF
    · rintro rfl
      rfl
