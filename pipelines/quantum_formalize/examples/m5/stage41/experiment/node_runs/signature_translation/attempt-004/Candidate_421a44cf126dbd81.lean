import FrozenTarget_421a44cf126dbd81
theorem M5.Translation.signature_translation : QuantumHarnessFrozenTarget := by
  classical
  intro N inst S U c d
  have hforward (D : M5.BinaryPolynomial) (hD : D ∣ M5.cyclicModulus N)
      (A : Finset (ZMod N)) (e : ZMod N)
      (h : D ∣ M5.Translation.supportPolynomial A) :
      D ∣ M5.Translation.supportPolynomial (M5.Translation.shift A e) := by
    apply (M5.SignatureCongruence.divisibility_of_quotient_eq D
      (M5.Translation.supportPolynomial (M5.Translation.shift A e))
      ((Polynomial.X : M5.BinaryPolynomial) ^ e.val * M5.Translation.supportPolynomial A)
      N hD (by
        simpa only [map_mul] using M5.Translation.shift_quotient_polynomial N A e)).2
    exact dvd_mul_of_dvd_right h _
  have hcancel (A : Finset (ZMod N)) (e : ZMod N) :
      M5.Translation.shift (M5.Translation.shift A e) (-e) = A := by
    unfold M5.Translation.shift
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, he⟩
      have hzx : z = x := by simpa using he
      simpa [hzx] using hz
    · intro hx
      exact ⟨x + e, ⟨x, hx, rfl⟩, by simp⟩
  have hshift (D : M5.BinaryPolynomial) (hD : D ∣ M5.cyclicModulus N)
      (A : Finset (ZMod N)) (e : ZMod N) :
      D ∣ M5.Translation.supportPolynomial (M5.Translation.shift A e) ↔
        D ∣ M5.Translation.supportPolynomial A := by
    constructor
    · intro h
      have hh := hforward D hD (M5.Translation.shift A e) (-e) h
      simpa only [hcancel] using hh
    · exact hforward D hD A e
  have hg (D a b : M5.BinaryPolynomial) :
      D ∣ EuclideanDomain.gcd a b ↔ D ∣ a ∧ D ∣ b := by
    constructor
    · intro h
      exact ⟨dvd_trans h (EuclideanDomain.gcd_dvd_left a b),
        dvd_trans h (EuclideanDomain.gcd_dvd_right a b)⟩
    · rintro ⟨ha, hb⟩
      exact EuclideanDomain.dvd_gcd ha hb
  have hs (D a b : M5.BinaryPolynomial) :
      D ∣ M5.completeSignature a b N ↔
        D ∣ a ∧ D ∣ b ∧ D ∣ M5.cyclicModulus N := by
    simp only [M5.completeSignature, hg, and_assoc]
  have he (D : M5.BinaryPolynomial) :
      D ∣ M5.completeSignature
        (M5.Translation.supportPolynomial (M5.Translation.shift S c))
        (M5.Translation.supportPolynomial (M5.Translation.shift U d)) N ↔
      D ∣ M5.completeSignature
        (M5.Translation.supportPolynomial S)
        (M5.Translation.supportPolynomial U) N := by
    rw [hs, hs]
    constructor
    · rintro ⟨hS, hU, hN⟩
      exact ⟨(hshift D hN S c).1 hS, (hshift D hN U d).1 hU, hN⟩
    · rintro ⟨hS, hU, hN⟩
      exact ⟨(hshift D hN S c).2 hS, (hshift D hN U d).2 hU, hN⟩
  apply M5.Signature.binary_dvd_antisymm
  · exact (he _).1 dvd_rfl
  · exact (he _).2 dvd_rfl
