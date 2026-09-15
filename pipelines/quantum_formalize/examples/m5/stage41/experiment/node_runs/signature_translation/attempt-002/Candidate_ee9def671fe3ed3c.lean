import FrozenTarget_ee9def671fe3ed3c
theorem M5.Translation.signature_translation : QuantumHarnessFrozenTarget := by
  classical
  intro N inst S U c d
  have hforward (D : M5.BinaryPolynomial) (hD : D ∣ M5.cyclicModulus N)
      (A : Finset (ZMod N)) (e : ZMod N)
      (hA : D ∣ M5.Translation.supportPolynomial A) :
      D ∣ M5.Translation.supportPolynomial (M5.Translation.shift A e) := by
    apply (M5.SignatureCongruence.divisibility_of_quotient_eq D
      (M5.Translation.supportPolynomial (M5.Translation.shift A e))
      ((Polynomial.X : M5.BinaryPolynomial) ^ e.val *
        M5.Translation.supportPolynomial A) N hD ?_).mpr
    · simpa only [map_mul] using
        M5.Translation.shift_quotient_polynomial N A e
    · exact dvd_mul_of_dvd_right hA _
  have hshift (D : M5.BinaryPolynomial) (hD : D ∣ M5.cyclicModulus N)
      (A : Finset (ZMod N)) (e : ZMod N) :
      D ∣ M5.Translation.supportPolynomial (M5.Translation.shift A e) ↔
        D ∣ M5.Translation.supportPolynomial A := by
    constructor
    · intro h
      have hh := hforward D hD (M5.Translation.shift A e) (-e) h
      have hinv : M5.Translation.shift (M5.Translation.shift A e) (-e) = A := by
        ext x
        simp [M5.Translation.shift, add_assoc]
      rw [hinv] at hh
      exact hh
    · exact hforward D hD A e
  have hgcd (a b D : M5.BinaryPolynomial) :
      D ∣ EuclideanDomain.gcd a b ↔ D ∣ a ∧ D ∣ b := by
    constructor
    · intro h
      exact ⟨dvd_trans h (EuclideanDomain.gcd_dvd_left a b),
        dvd_trans h (EuclideanDomain.gcd_dvd_right a b)⟩
    · rintro ⟨ha, hb⟩
      exact EuclideanDomain.dvd_gcd ha hb
  have hsig (a b D : M5.BinaryPolynomial) :
      D ∣ M5.completeSignature a b N ↔
        D ∣ a ∧ D ∣ b ∧ D ∣ M5.cyclicModulus N := by
    simp only [M5.completeSignature, hgcd]
    tauto
  apply M5.Signature.binary_dvd_antisymm
  · have h := (hsig
      (M5.Translation.supportPolynomial (M5.Translation.shift S c))
      (M5.Translation.supportPolynomial (M5.Translation.shift U d))
      _).mp dvd_rfl
    apply (hsig _ _ _).mpr
    exact ⟨(hshift _ h.2.2 S c).mp h.1,
      (hshift _ h.2.2 U d).mp h.2.1, h.2.2⟩
  · have h := (hsig (M5.Translation.supportPolynomial S)
      (M5.Translation.supportPolynomial U) _).mp dvd_rfl
    apply (hsig _ _ _).mpr
    exact ⟨(hshift _ h.2.2 S c).mpr h.1,
      (hshift _ h.2.2 U d).mpr h.2.1, h.2.2⟩
