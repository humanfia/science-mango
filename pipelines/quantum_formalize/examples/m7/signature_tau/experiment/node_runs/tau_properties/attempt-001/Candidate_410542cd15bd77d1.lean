import FrozenTarget_410542cd15bd77d1
theorem M7.SignatureTau.tau_properties : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ (u : (ZMod N)ˣ) (F : M6.Cyclic.BinaryPolynomial), (M7.SignatureTau.tau u F).Monic ∧ M7.SignatureTau.tau u F ∣ M6.Cyclic.modulus N
  intro N inst u F
  unfold M7.SignatureTau.tau
  exact ⟨(M7.SignatureTau.gcd_canonical N _).1, (M7.SignatureTau.gcd_canonical N _).2.1⟩
