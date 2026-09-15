import M7QuotientDegree

theorem M7.QuotientDegree.adjoin_card : ∀ F : M6.Cyclic.BinaryPolynomial, F.Monic → Nat.card (AdjoinRoot F) = 2 ^ F.natDegree := by
  change ∀ F : M6.Cyclic.BinaryPolynomial, F.Monic → Nat.card (AdjoinRoot F) = 2 ^ F.natDegree
  intro F hF
  calc
    Nat.card (AdjoinRoot F) = Nat.card (Fin F.natDegree → ZMod 2) :=
      Nat.card_congr (AdjoinRoot.powerBasis' hF).basis.equivFun.toEquiv
    _ = 2 ^ F.natDegree := by simp [Nat.card_eq_fintype_card]

theorem M7.QuotientDegree.span_containment : ∀ (N : ℕ) [NeZero N], ∀ F : M6.Cyclic.BinaryPolynomial, F ∣ M6.Cyclic.modulus N → Ideal.span ({M6.Cyclic.modulus N} : Set M6.Cyclic.BinaryPolynomial) ≤ Ideal.span ({F} : Set M6.Cyclic.BinaryPolynomial) := by
  intro N _ F hF
  apply Ideal.span_le.mpr
  intro p hp
  rcases Set.mem_singleton_iff.mp hp with rfl
  exact Ideal.mem_span_singleton.mpr hF

theorem M7.QuotientDegree.quotient_equiv : ∀ (N : ℕ) [NeZero N], ∀ F : M6.Cyclic.BinaryPolynomial, F ∣ M6.Cyclic.modulus N → Nonempty ((M6.Cyclic.CycleRing N ⧸ M7.SignatureIdeal.principal N F) ≃+* AdjoinRoot F) := by
  intro N _ F hF
  let f : M6.Cyclic.CycleRing N →+* AdjoinRoot F :=
    Ideal.Quotient.factor (M7.QuotientDegree.span_containment N F hF)
  have hk : RingHom.ker f = M7.SignatureIdeal.principal N F := by
    ext x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change AdjoinRoot.mk F p = 0 ↔ M6.Cyclic.image N p ∈ M7.SignatureIdeal.principal N F
    rw [AdjoinRoot.mk_eq_zero]
    exact (M7.SignatureIdeal.quotient_membership N F p hF).symm
  rw [← hk]
  exact ⟨RingHom.quotientKerEquivOfSurjective (f := f)
    (Ideal.Quotient.factor_surjective (M7.QuotientDegree.span_containment N F hF))⟩

theorem M7.QuotientDegree.quotient_card : ∀ (N : ℕ) [NeZero N], ∀ F : M6.Cyclic.BinaryPolynomial, F.Monic → F ∣ M6.Cyclic.modulus N → Nat.card (M6.Cyclic.CycleRing N ⧸ M7.SignatureIdeal.principal N F) = 2 ^ F.natDegree := by
  change ∀ (N : ℕ) [NeZero N], ∀ F : M6.Cyclic.BinaryPolynomial, F.Monic → F ∣ M6.Cyclic.modulus N → Nat.card (M6.Cyclic.CycleRing N ⧸ M7.SignatureIdeal.principal N F) = 2 ^ F.natDegree
  intro N _ F hF hdiv
  obtain ⟨e⟩ := M7.QuotientDegree.quotient_equiv N F hdiv
  exact (Nat.card_congr e.toEquiv).trans (M7.QuotientDegree.adjoin_card F hF)

theorem M7.QuotientDegree.degree_invariant : ∀ (N : ℕ) [NeZero N], ∀ F E : M6.Cyclic.BinaryPolynomial, F.Monic → E.Monic → F ∣ M6.Cyclic.modulus N → E ∣ M6.Cyclic.modulus N → ∀ e : M6.Cyclic.CycleRing N ≃+* M6.Cyclic.CycleRing N, Ideal.map e.toRingHom (M7.SignatureIdeal.principal N F) = M7.SignatureIdeal.principal N E → F.natDegree = E.natDegree := by
  change ∀ (N : ℕ) [NeZero N], ∀ F E : M6.Cyclic.BinaryPolynomial, F.Monic → E.Monic → F ∣ M6.Cyclic.modulus N → E ∣ M6.Cyclic.modulus N → ∀ e : M6.Cyclic.CycleRing N ≃+* M6.Cyclic.CycleRing N, Ideal.map e.toRingHom (M7.SignatureIdeal.principal N F) = M7.SignatureIdeal.principal N E → F.natDegree = E.natDegree
  intro N _ F E hF hE hFd hEd e he
  have hc := Nat.card_congr (Ideal.quotientEquiv
    (M7.SignatureIdeal.principal N F)
    (M7.SignatureIdeal.principal N E) e he.symm).toEquiv
  rw [M7.QuotientDegree.quotient_card N F hF hFd,
    M7.QuotientDegree.quotient_card N E hE hEd] at hc
  exact Nat.pow_right_injective (by decide : 1 < 2) hc
#print axioms M7.QuotientDegree.adjoin_card
#print axioms M7.QuotientDegree.span_containment
#print axioms M7.QuotientDegree.quotient_equiv
#print axioms M7.QuotientDegree.quotient_card
#print axioms M7.QuotientDegree.degree_invariant
