import FrozenTarget_46bf31789a42bb34
theorem M5.SignatureCongruence.complete_signature_congruence : QuantumHarnessFrozenTarget := by
  change ∀ (a b a' b' : M5.BinaryPolynomial) (T : ℕ), AdjoinRoot.mk (M5.cyclicModulus T) a = AdjoinRoot.mk (M5.cyclicModulus T) a' → AdjoinRoot.mk (M5.cyclicModulus T) b = AdjoinRoot.mk (M5.cyclicModulus T) b' → M5.completeSignature a b T = M5.completeSignature a' b' T
  intro a b a' b' T ha hb
  have hsig (D : M5.BinaryPolynomial) :
      D ∣ M5.completeSignature a b T ↔ D ∣ M5.completeSignature a' b' T := by
    simp only [M5.completeSignature, EuclideanDomain.dvd_gcd_iff]
    constructor
    · intro h
      have hD : D ∣ M5.cyclicModulus T := by tauto
      have hA := M5.SignatureCongruence.divisibility_of_quotient_eq D a a' T hD ha
      have hB := M5.SignatureCongruence.divisibility_of_quotient_eq D b b' T hD hb
      tauto
    · intro h
      have hD : D ∣ M5.cyclicModulus T := by tauto
      have hA := M5.SignatureCongruence.divisibility_of_quotient_eq D a a' T hD ha
      have hB := M5.SignatureCongruence.divisibility_of_quotient_eq D b b' T hD hb
      tauto
  apply M5.Signature.binary_dvd_antisymm
  · exact (hsig _).mp dvd_rfl
  · exact (hsig _).mpr dvd_rfl
