import FrozenTarget_886652ab5b826f10
theorem M6.Cyclic.signature_divides : QuantumHarnessFrozenTarget := by
  change ∀ a b M : M6.Cyclic.BinaryPolynomial, M6.Cyclic.signature a b M ∣ a ∧ M6.Cyclic.signature a b M ∣ b ∧ M6.Cyclic.signature a b M ∣ M
  intro a b M
  unfold M6.Cyclic.signature
  exact ⟨dvd_trans (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_left _ _), dvd_trans (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_right _ _), EuclideanDomain.gcd_dvd_right _ _⟩
