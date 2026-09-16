import FrozenTarget_94747eb3958a53ac
theorem M8.Coverage.p3_physical : QuantumHarnessFrozenTarget := by
  intro N inst hN hdiv
  have hp0 := M8.P3Family.nontrivial.2.1
  have hp1 := M8.P3Family.nontrivial.1
  have hdeg : M8.P3Family.polynomial.degree < (N : WithBot ℕ) := by
    apply Polynomial.degree_lt_of_natDegree_lt
    rw [M8.P3Family.nontrivial.2.2]
    omega
  have hm : M8.P3Family.polynomial.Monic := by
    have hs := M7.RecipeSignature.signature_properties N (M8.P3Family.recipe N)
    rw [M8.P3Family.signature N hN hdiv] at hs
    first
    | exact hs.1
    | exact hs.2.1
    | exact hs.2.2.1
    | exact hs
  have hdvd := M8.P3Family.divides_modulus N hdiv
  have hn := M8.DiagonalPolynomial.coefficients_nonzero N M8.P3Family.polynomial hp0 hdeg
  have hi := M8.DiagonalPolynomial.delta_not_image N M8.P3Family.polynomial M8.P3Family.polynomial hdeg hm hp1 (dvd_refl _) hdvd
  have hd := M8.DiagonalPolynomial.distance_two N M8.P3Family.polynomial M8.P3Family.polynomial hp0 hdeg hm hp1 (dvd_refl _) hdvd
  have hw := M8.Diagonal.diagonal_witness N (M6.Coordinates.coefficients N M8.P3Family.polynomial)
  repeat first | specialize hw hn | specialize hw hi
  unfold M8.Coverage.PhysicalTwo
  simp only [M7.Transport.distance, M7.Transport.LX, M8.P3Family.recipe, M8.P3Family.literal_polynomial N hN]
  refine ⟨hd, ?_, ?_, ?_⟩
  · first | exact hw.1 | exact hw
  · first | exact hw.2 | exact hw.2.1
  · intros u hu
    apply M8.Diagonal.logical_lower_bound N (M6.Coordinates.coefficients N M8.P3Family.polynomial)
    all_goals assumption
