import FrozenTarget_748d02ff93805319
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
        M5.Translation.supportPolynomial A) N hD
      (by simpa only [map_mul] using
        M5.Translation.shift_quotient_polynomial N A e)).mpr
    exact dvd_mul_of_dvd_right hA _
  have hshift (D : M5.BinaryPolynomial) (hD : D ∣ M5.cyclicModulus N)
      (A : Finset (ZMod N)) (e : ZMod N) :
      D ∣ M5.Translation.supportPolynomial (M5.Translation.shift A e) ↔
        D ∣ M5.Translation.supportPolynomial A := by
    constructor
    · intro h
      have hh := hforward D hD (M5.Translation.shift A e) (-e) h
      simpa [M5.Translation.shift, Finset.image_image, Function.comp_def] using hh
    · exact hforward D hD A e
  have hchar (a b D : M5.BinaryPolynomial) :
      D ∣ M5.completeSignature a b N ↔
        D ∣ a ∧ D ∣ b ∧ D ∣ M5.cyclicModulus N := by
    unfold M5.completeSignature
    simp only [EuclideanDomain.dvd_gcd_iff]
    tauto
  have hall (D : M5.BinaryPolynomial) :
      D ∣ M5.completeSignature
        (M5.Translation.supportPolynomial (M5.Translation.shift S c))
        (M5.Translation.supportPolynomial (M5.Translation.shift U d)) N ↔
      D ∣ M5.completeSignature
        (M5.Translation.supportPolynomial S)
        (M5.Translation.supportPolynomial U) N := by
    rw [hchar, hchar]
    constructor
    · rintro ⟨hS, hU, hN⟩
      exact ⟨(hshift D hN S c).mp hS, (hshift D hN U d).mp hU, hN⟩
    · rintro ⟨hS, hU, hN⟩
      exact ⟨(hshift D hN S c).mpr hS, (hshift D hN U d).mpr hU, hN⟩
  apply M5.Signature.binary_dvd_antisymm
  · exact (hall _).mp dvd_rfl
  · exact (hall _).mpr dvd_rfl
