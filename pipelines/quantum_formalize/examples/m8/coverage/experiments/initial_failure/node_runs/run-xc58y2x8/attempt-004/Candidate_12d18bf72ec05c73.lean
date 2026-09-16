import FrozenTarget_12d18bf72ec05c73
theorem M8.Coverage.p3_physical : QuantumHarnessFrozenTarget := by
  intro N inst hN hdiv
  classical
  have hlit := M8.P3Family.literal_polynomial N hN
  have hne := M8.P3Family.nontrivial
  have hdeg : M8.P3Family.polynomial.degree < (N : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hne.2.1, hne.2.2]
    exact_mod_cast (show 2 < N by omega)
  have hmonic : M8.P3Family.polynomial.Monic := by
    have hs := M7.RecipeSignature.signature_properties N (M8.P3Family.recipe N)
    rw [M8.P3Family.signature N hN hdiv] at hs
    aesop
  have hmod := M8.P3Family.divides_modulus N hdiv
  have hdist := M8.DiagonalPolynomial.distance_two N M8.P3Family.polynomial M8.P3Family.polynomial hne.2.1 hdeg hmonic hne.1 (dvd_refl _) hmod
  have hdelta := M8.DiagonalPolynomial.delta_not_image N M8.P3Family.polynomial M8.P3Family.polynomial hdeg hmonic hne.1 (dvd_refl _) hmod
  have hnz := M8.DiagonalPolynomial.coefficients_nonzero N M8.P3Family.polynomial hne.2.1 hdeg
  unfold M8.Coverage.PhysicalTwo
  dsimp [M7.Transport.distance, M7.Transport.LX, M8.P3Family.recipe]
  simp only [hlit]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hdist
  · unfold M8.Coverage.deltaPair
    aesop (add safe M8.Diagonal.diagonal_witness)
  · unfold M8.Coverage.deltaPair
    aesop (add safe M8.Diagonal.diagonal_witness)
  · exact M8.Diagonal.logical_lower_bound N (M6.Coordinates.coefficients N M8.P3Family.polynomial) hnz
