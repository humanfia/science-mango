import M7SignatureTau

theorem M7.SignatureTau.modulus_monic : ∀ (N : ℕ) [NeZero N], (M6.Cyclic.modulus N).Monic := by
  change ∀ (N : ℕ) [NeZero N], (M6.Cyclic.modulus N).Monic
  intro N inst
  change (Polynomial.X ^ N + 1 : Polynomial (ZMod 2)).Monic
  simpa only [Polynomial.C_1] using
    (Polynomial.monic_X_pow_add_C (1 : ZMod 2) (NeZero.ne N))
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (F : M6.Cyclic.BinaryPolynomial), M6.Cyclic.image N (M7.SignatureTau.reduced u F) = M7.QuotientAuto.substitution u (M6.Cyclic.image N F)
