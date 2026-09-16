import FrozenTarget_b932c4d6005f9579
theorem M8.Coverage.p3_physical : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], 3 ≤ N → 3 ∣ N → M8.Coverage.PhysicalTwo (M8.P3Family.recipe N)
  intro N inst hN hdiv
  have hp0 := M8.P3Family.nontrivial.2.1
  have hp1 := M8.P3Family.nontrivial.1
  have hdeg : M8.P3Family.polynomial.degree < (N : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hp0, M8.P3Family.nontrivial.2.2]
    exact_mod_cast (show 2 < N by omega)
  have hprops := M7.RecipeSignature.signature_properties N (M8.P3Family.recipe N)
  have hsig := M8.P3Family.signature N hN hdiv
  have hmonic : M8.P3Family.polynomial.Monic := by
    rw [hsig] at hprops
    aesop
  have hmod := M8.P3Family.divides_modulus N hdiv
  have hnot := M8.DiagonalPolynomial.delta_not_image N M8.P3Family.polynomial M8.P3Family.polynomial hdeg hmonic hp1 (dvd_refl _) hmod
  have hdist := M8.DiagonalPolynomial.distance_two N M8.P3Family.polynomial M8.P3Family.polynomial hp0 hdeg hmonic hp1 (dvd_refl _) hmod
  have hnz := M8.DiagonalPolynomial.coefficients_nonzero N M8.P3Family.polynomial hp0 hdeg
  have hw := M8.Diagonal.diagonal_witness N (M6.Coordinates.coefficients N M8.P3Family.polynomial)
  have hl := M8.Diagonal.logical_lower_bound N (M6.Coordinates.coefficients N M8.P3Family.polynomial)
  unfold M8.Coverage.PhysicalTwo
  simp only [M7.Transport.distance, M7.Transport.LX, M8.P3Family.recipe, M8.P3Family.literal_polynomial N hN]
  change M8.Diagonal.distance N (M6.Coordinates.coefficients N M8.P3Family.polynomial) = some 2 ∧ _
  refine ⟨hdist, ?_⟩
  unfold M8.Coverage.deltaPair
   aesop
