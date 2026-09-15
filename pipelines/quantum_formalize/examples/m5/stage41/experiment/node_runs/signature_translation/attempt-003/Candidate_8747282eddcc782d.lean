import FrozenTarget_8747282eddcc782d
theorem M5.Translation.signature_translation : QuantumHarnessFrozenTarget := by
  classical
  intro N inst S U c d
  have hforward (D : M5.BinaryPolynomial) (hD : D ∣ M5.cyclicModulus N)
      (A : Finset (ZMod N)) (e : ZMod N)
      (hA : D ∣ M5.Translation.supportPolynomial A) :
      D ∣ M5.Translation.supportPolynomial (M5.Translation.shift A e) := by
    have heq :
        AdjoinRoot.mk (M5.cyclicModulus N)
            (M5.Translation.supportPolynomial (M5.Translation.shift A e)) =
          AdjoinRoot.mk (M5.cyclicModulus N)
            ((Polynomial.X : M5.BinaryPolynomial) ^ e.val *
              M5.Translation.supportPolynomial A) := by
      simpa only [map_mul] using M5.Translation.shift_quotient_polynomial N A e
    exact (M5.SignatureCongruence.divisibility_of_quotient_eq D _ _ N hD heq).mpr
      (dvd_mul_of_dvd_right hA _)
  have hshift (D : M5.BinaryPolynomial) (hD : D ∣ M5.cyclicModulus N)
      (A : Finset (ZMod N)) (e : ZMod N) :
      D ∣ M5.Translation.supportPolynomial (M5.Translation.shift A e) ↔
        D ∣ M5.Translation.supportPolynomial A := by
    constructor
    · intro h
      have hback : M5.Translation.shift (M5.Translation.shift A e) (-e) = A := by
        simp [M5.Translation.shift, Finset.image_image]
      have hh := hforward D hD (M5.Translation.shift A e) (-e) h
      simpa only [hback] using hh
    · exact hforward D hD A e
  have hsig (D a b : M5.BinaryPolynomial) :
      D ∣ M5.completeSignature a b N ↔
        D ∣ a ∧ D ∣ b ∧ D ∣ M5.cyclicModulus N := by
    simp only [M5.completeSignature, EuclideanDomain.dvd_gcd_iff]
    tauto
  have hall (D : M5.BinaryPolynomial) :
      D ∣ M5.completeSignature
          (M5.Translation.supportPolynomial (M5.Translation.shift S c))
          (M5.Translation.supportPolynomial (M5.Translation.shift U d)) N ↔
        D ∣ M5.completeSignature
          (M5.Translation.supportPolynomial S)
          (M5.Translation.supportPolynomial U) N := by
    rw [hsig, hsig]
    constructor
    · rintro ⟨hS, hU, hN⟩
      exact ⟨(hshift D hN S c).mp hS, (hshift D hN U d).mp hU, hN⟩
    · rintro ⟨hS, hU, hN⟩
      exact ⟨(hshift D hN S c).mpr hS, (hshift D hN U d).mpr hU, hN⟩
  apply M5.Signature.binary_dvd_antisymm
  · exact (hall _).mp (dvd_refl _)
  · exact (hall _).mpr (dvd_refl _)
