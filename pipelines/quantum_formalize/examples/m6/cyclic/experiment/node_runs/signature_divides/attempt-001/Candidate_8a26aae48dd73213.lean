import FrozenTarget_8a26aae48dd73213
theorem M6.Cyclic.signature_divides : QuantumHarnessFrozenTarget := by
  change ∀ a b M : M6.Cyclic.BinaryPolynomial, M6.Cyclic.signature a b M ∣ a ∧ M6.Cyclic.signature a b M ∣ b ∧ M6.Cyclic.signature a b M ∣ M
  intro a b M
  unfold M6.Cyclic.signature
  refine ⟨?_, ?_, ?_⟩
  all_goals
    first
    | exact EuclideanDomain.gcd_dvd_left _ _
    | exact EuclideanDomain.gcd_dvd_right _ _
    | exact (EuclideanDomain.gcd_dvd_left _ _).trans (EuclideanDomain.gcd_dvd_left _ _)
    | exact (EuclideanDomain.gcd_dvd_left _ _).trans (EuclideanDomain.gcd_dvd_right _ _)
    | exact (EuclideanDomain.gcd_dvd_right _ _).trans (EuclideanDomain.gcd_dvd_left _ _)
    | exact (EuclideanDomain.gcd_dvd_right _ _).trans (EuclideanDomain.gcd_dvd_right _ _)
