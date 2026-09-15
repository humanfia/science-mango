import M5Signature
#check (∀ P : M5.BinaryPolynomial, P ≠ 0 → P.Monic)
#check (∀ P Q : M5.BinaryPolynomial, P ∣ Q → Q ∣ P → P = Q)
#check (∀ P a : M5.BinaryPolynomial, P ∣ a → a.coeff 0 = 1 → P.coeff 0 = 1)
#check (∀ a b : M5.BinaryPolynomial, a.coeff 0 = 1 → b.coeff 0 = 1 → (EuclideanDomain.gcd a b).Monic ∧ (EuclideanDomain.gcd a b).coeff 0 = 1 ∧ (EuclideanDomain.gcd a b).natDegree ≤ b.natDegree)
#check (∀ (a b : M5.BinaryPolynomial) (T E j : ℕ), EuclideanDomain.gcd a b ∣ M5.cyclicModulus E → M5.completeSignature a b (T+j*E) = M5.completeSignature a b T)
#check (∀ a b : M5.BinaryPolynomial, a.coeff 0 = 1 → b.coeff 0 = 1 → 0 < M5.signaturePeriod (EuclideanDomain.gcd a b) ∧ M5.signaturePeriod (EuclideanDomain.gcd a b) ≤ 2 ^ b.natDegree)
