import FrozenTarget_9ffd23b5cc1a40e9
theorem M7.SignatureTau.tau_comp : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ (u v : (ZMod N)ˣ) (F : M6.Cyclic.BinaryPolynomial), F.Monic → F ∣ M6.Cyclic.modulus N → M7.SignatureTau.tau v (M7.SignatureTau.tau u F) = M7.SignatureTau.tau (v * u) F
  intro N inst u v F hF hdiv
  have hL := M7.SignatureTau.tau_properties N v (M7.SignatureTau.tau u F)
  have hR := M7.SignatureTau.tau_properties N (v * u) F
  apply (M7.SignatureIdeal.monic_injective N _ _ hL.1 hR.1 hL.2 hR.2).mp
  rw [M7.SignatureTau.tau_principal N v,
    M7.SignatureTau.tau_principal N u,
    M7.SignatureTau.tau_principal N (v * u),
    Ideal.map_map, M7.QuotientAuto.substitution_comp N u v]
