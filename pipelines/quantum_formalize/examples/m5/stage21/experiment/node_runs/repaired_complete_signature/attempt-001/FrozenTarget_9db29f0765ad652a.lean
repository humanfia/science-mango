import M5SignatureCongruence

theorem M5.SignatureCongruence.divisibility_of_quotient_eq : ∀ (D a a' : M5.BinaryPolynomial) (T : ℕ), D ∣ M5.cyclicModulus T → AdjoinRoot.mk (M5.cyclicModulus T) a = AdjoinRoot.mk (M5.cyclicModulus T) a' → (D ∣ a ↔ D ∣ a') := by
  change ∀ (D a a' : M5.BinaryPolynomial) (T : ℕ), D ∣ M5.cyclicModulus T → AdjoinRoot.mk (M5.cyclicModulus T) a = AdjoinRoot.mk (M5.cyclicModulus T) a' → (D ∣ a ↔ D ∣ a')
  intro D a a' T hD heq
  have hmod : M5.cyclicModulus T ∣ a - a' := by
    simpa only [AdjoinRoot.mk_eq_mk] using heq
  have hdiff : D ∣ a - a' := dvd_trans hD hmod
  constructor
  · intro ha
    have hid : a - (a - a') = a' := by ring
    rw [← hid]
    exact dvd_sub ha hdiff
  · intro ha'
    simpa only [sub_add_cancel] using dvd_add hdiff ha'

theorem M5.SignatureCongruence.complete_signature_congruence : ∀ (a b a' b' : M5.BinaryPolynomial) (T : ℕ), AdjoinRoot.mk (M5.cyclicModulus T) a = AdjoinRoot.mk (M5.cyclicModulus T) a' → AdjoinRoot.mk (M5.cyclicModulus T) b = AdjoinRoot.mk (M5.cyclicModulus T) b' → M5.completeSignature a b T = M5.completeSignature a' b' T := by
  change ∀ (a b a' b' : M5.BinaryPolynomial) (T : ℕ), AdjoinRoot.mk (M5.cyclicModulus T) a = AdjoinRoot.mk (M5.cyclicModulus T) a' → AdjoinRoot.mk (M5.cyclicModulus T) b = AdjoinRoot.mk (M5.cyclicModulus T) b' → M5.completeSignature a b T = M5.completeSignature a' b' T
  intro a b a' b' T ha hb
  have hgcd (D x y : M5.BinaryPolynomial) :
      D ∣ EuclideanDomain.gcd x y ↔ D ∣ x ∧ D ∣ y := by
    constructor
    · intro h
      exact ⟨dvd_trans h (EuclideanDomain.gcd_dvd_left x y),
        dvd_trans h (EuclideanDomain.gcd_dvd_right x y)⟩
    · rintro ⟨hx, hy⟩
      exact EuclideanDomain.dvd_gcd hx hy
  have hs (D : M5.BinaryPolynomial) :
      D ∣ M5.completeSignature a b T ↔ D ∣ M5.completeSignature a' b' T := by
    unfold M5.completeSignature
    simp only [hgcd]
    constructor
    · rintro ⟨⟨hA, hB⟩, hD⟩
      exact ⟨⟨(M5.SignatureCongruence.divisibility_of_quotient_eq D a a' T hD ha).mp hA,
        (M5.SignatureCongruence.divisibility_of_quotient_eq D b b' T hD hb).mp hB⟩, hD⟩
    · rintro ⟨⟨hA, hB⟩, hD⟩
      exact ⟨⟨(M5.SignatureCongruence.divisibility_of_quotient_eq D a a' T hD ha).mpr hA,
        (M5.SignatureCongruence.divisibility_of_quotient_eq D b b' T hD hb).mpr hB⟩, hD⟩
  apply M5.Signature.binary_dvd_antisymm
  · exact (hs _).mp dvd_rfl
  · exact (hs _).mpr dvd_rfl
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (A B : Finset ℕ) (e k T : ℕ), e ∈ A → e + k * T ∉ A → M5.completeSignature (M5.SupportPolynomial.ofSupport (M5.RepairSupport.repaired A e (e + k * T))) (M5.SupportPolynomial.ofSupport B) T = M5.completeSignature (M5.SupportPolynomial.ofSupport A) (M5.SupportPolynomial.ofSupport B) T
