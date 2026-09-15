import FrozenTarget_36085c1445a954e5
theorem M7.QuotientDegree.degree_invariant : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ F E : M6.Cyclic.BinaryPolynomial, F.Monic → E.Monic → F ∣ M6.Cyclic.modulus N → E ∣ M6.Cyclic.modulus N → ∀ e : M6.Cyclic.CycleRing N ≃+* M6.Cyclic.CycleRing N, Ideal.map e.toRingHom (M7.SignatureIdeal.principal N F) = M7.SignatureIdeal.principal N E → F.natDegree = E.natDegree
  intro N _ F E hF hE hFd hEd e he
  have hc := Nat.card_congr (Ideal.quotientEquiv
    (M7.SignatureIdeal.principal N F)
    (M7.SignatureIdeal.principal N E) e he.symm).toEquiv
  rw [M7.QuotientDegree.quotient_card N F hF hFd,
    M7.QuotientDegree.quotient_card N E hE hEd] at hc
  exact Nat.pow_right_injective (by decide : 1 < 2) hc
