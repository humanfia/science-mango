import M6Cyclic

theorem M6.Cyclic.signature_bezout : ∀ a b M : M6.Cyclic.BinaryPolynomial, ∃ p q r : M6.Cyclic.BinaryPolynomial, M6.Cyclic.signature a b M = p*a + q*b + r*M := by
  intro a b M
  classical
  unfold M6.Cyclic.signature
  first
  | change ∃ p q r, EuclideanDomain.gcd (EuclideanDomain.gcd a b) M = p*a + q*b + r*M
    refine ⟨EuclideanDomain.gcdA (EuclideanDomain.gcd a b) M * EuclideanDomain.gcdA a b, EuclideanDomain.gcdA (EuclideanDomain.gcd a b) M * EuclideanDomain.gcdB a b, EuclideanDomain.gcdB (EuclideanDomain.gcd a b) M, ?_⟩
    calc
      _ = (EuclideanDomain.gcd a b) * EuclideanDomain.gcdA (EuclideanDomain.gcd a b) M + M * EuclideanDomain.gcdB (EuclideanDomain.gcd a b) M := EuclideanDomain.gcd_eq_gcd_ab _ _
      _ = _ := by
        rw [EuclideanDomain.gcd_eq_gcd_ab a b]
        ring
  | change ∃ p q r, EuclideanDomain.gcd a (EuclideanDomain.gcd b M) = p*a + q*b + r*M
    refine ⟨EuclideanDomain.gcdA a (EuclideanDomain.gcd b M), EuclideanDomain.gcdB a (EuclideanDomain.gcd b M) * EuclideanDomain.gcdA b M, EuclideanDomain.gcdB a (EuclideanDomain.gcd b M) * EuclideanDomain.gcdB b M, ?_⟩
    calc
      _ = a * EuclideanDomain.gcdA a (EuclideanDomain.gcd b M) + (EuclideanDomain.gcd b M) * EuclideanDomain.gcdB a (EuclideanDomain.gcd b M) := EuclideanDomain.gcd_eq_gcd_ab _ _
      _ = _ := by
        rw [EuclideanDomain.gcd_eq_gcd_ab b M]
        ring

theorem M6.Cyclic.signature_divides : ∀ a b M : M6.Cyclic.BinaryPolynomial, M6.Cyclic.signature a b M ∣ a ∧ M6.Cyclic.signature a b M ∣ b ∧ M6.Cyclic.signature a b M ∣ M := by
  change ∀ a b M : M6.Cyclic.BinaryPolynomial, M6.Cyclic.signature a b M ∣ a ∧ M6.Cyclic.signature a b M ∣ b ∧ M6.Cyclic.signature a b M ∣ M
  intro a b M
  unfold M6.Cyclic.signature
  exact ⟨dvd_trans (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_left _ _), dvd_trans (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_right _ _), EuclideanDomain.gcd_dvd_right _ _⟩
def QuantumHarnessFrozenTarget : Prop :=
  ∀ a b M h : M6.Cyclic.BinaryPolynomial, (M ∣ a*h ∧ M ∣ b*h) ↔ M ∣ M6.Cyclic.signature a b M * h
