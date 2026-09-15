import FrozenTarget_12e50a43cb90211c
theorem M7.SignatureTau.tau_one : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ F : M6.Cyclic.BinaryPolynomial, F.Monic → F ∣ M6.Cyclic.modulus N → M7.SignatureTau.tau (1 : (ZMod N)ˣ) F = F
  intro N inst F hF hdF
  have ht := M7.SignatureTau.tau_properties N (1 : (ZMod N)ˣ) F
  apply (M7.SignatureIdeal.monic_injective N _ F ht.1 hF ht.2 hdF).mp
  rw [M7.SignatureTau.tau_principal, M7.QuotientAuto.substitution_one, Ideal.map_id]
