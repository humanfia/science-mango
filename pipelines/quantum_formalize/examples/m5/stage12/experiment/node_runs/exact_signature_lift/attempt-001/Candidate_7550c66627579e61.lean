import FrozenTarget_7550c66627579e61
theorem M5.Signature.exact_signature_lift : QuantumHarnessFrozenTarget := by
  change ∀ (a b : M5.BinaryPolynomial) (T E j : ℕ), EuclideanDomain.gcd a b ∣ M5.cyclicModulus E → M5.completeSignature a b (T+j*E) = M5.completeSignature a b T
  intro a b T E j hE
  unfold M5.completeSignature
  have hLift := M5.Lift.common_divisors_lift (a := a) (b := b) (T := T) (E := E) (j := j)
  apply M5.Signature.binary_dvd_antisymm
  all_goals
    apply EuclideanDomain.dvd_gcd
    · exact EuclideanDomain.gcd_dvd_left _ _
    · have hleft := EuclideanDomain.gcd_dvd_left (EuclideanDomain.gcd a b) (M5.cyclicModulus (T + j * E))
      have hright := EuclideanDomain.gcd_dvd_right (EuclideanDomain.gcd a b) (M5.cyclicModulus (T + j * E))
      have hleft' := EuclideanDomain.gcd_dvd_left (EuclideanDomain.gcd a b) (M5.cyclicModulus T)
      have hright' := EuclideanDomain.gcd_dvd_right (EuclideanDomain.gcd a b) (M5.cyclicModulus T)
      aesop
