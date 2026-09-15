import FrozenTarget_f90e2f25508fdcad
theorem M5.Signature.ordinary_gcd_properties : QuantumHarnessFrozenTarget := by
  change ∀ a b : M5.BinaryPolynomial, a.coeff 0 = 1 → b.coeff 0 = 1 → (EuclideanDomain.gcd a b).Monic ∧ (EuclideanDomain.gcd a b).coeff 0 = 1 ∧ (EuclideanDomain.gcd a b).natDegree ≤ b.natDegree
  intro a b ha hb
  have hc : (EuclideanDomain.gcd a b).coeff 0 = 1 :=
    M5.Signature.divisor_constant_one _ a (EuclideanDomain.gcd_dvd_left a b) ha
  have hg : EuclideanDomain.gcd a b ≠ 0 := by
    intro h
    simp [h] at hc
  have hb0 : b ≠ 0 := by
    intro h
    simp [h] at hb
  exact ⟨M5.Signature.binary_monic _ hg, hc,
    Polynomial.natDegree_le_of_dvd (EuclideanDomain.gcd_dvd_right a b) hb0⟩
