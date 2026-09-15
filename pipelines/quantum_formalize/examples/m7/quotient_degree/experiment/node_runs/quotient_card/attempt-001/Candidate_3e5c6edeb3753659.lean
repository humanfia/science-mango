import FrozenTarget_3e5c6edeb3753659
theorem M7.QuotientDegree.quotient_card : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ F : M6.Cyclic.BinaryPolynomial, F.Monic → F ∣ M6.Cyclic.modulus N → Nat.card (M6.Cyclic.CycleRing N ⧸ M7.SignatureIdeal.principal N F) = 2 ^ F.natDegree
  intro N _ F hF hdiv
  obtain ⟨e⟩ := M7.QuotientDegree.quotient_equiv N F hdiv
  exact (Nat.card_congr e.toEquiv).trans (M7.QuotientDegree.adjoin_card F hF)
