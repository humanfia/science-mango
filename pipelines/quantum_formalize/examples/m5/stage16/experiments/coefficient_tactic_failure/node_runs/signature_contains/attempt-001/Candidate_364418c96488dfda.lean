import FrozenTarget_364418c96488dfda
theorem M5.PolynomialExclusion.signature_contains : QuantumHarnessFrozenTarget := by
  change ∀ (a b F : M5.BinaryPolynomial) (N : ℕ), F ∣ a → F ∣ b → F ∣ M5.cyclicModulus N → F ∣ M5.completeSignature a b N
  intro a b F N ha hb hN
  unfold M5.completeSignature
  repeat' first | assumption | apply EuclideanDomain.dvd_gcd
