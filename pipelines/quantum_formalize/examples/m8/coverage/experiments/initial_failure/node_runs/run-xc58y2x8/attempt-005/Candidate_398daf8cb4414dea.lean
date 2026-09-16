import FrozenTarget_398daf8cb4414dea
theorem M8.Coverage.p3_physical : QuantumHarnessFrozenTarget := by
    change ∀ (N : ℕ) [NeZero N], 3 ≤ N → 3 ∣ N → M8.Coverage.PhysicalTwo (M8.P3Family.recipe N)
    intro N inst hN hdiv
    have hlit := M8.P3Family.literal_polynomial N hN
    have hdeg : M8.P3Family.polynomial.degree < (N : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree M8.P3Family.nontrivial.2.1, M8.P3Family.nontrivial.2.2]
      exact_mod_cast (show 2 < N by omega)
    have hmonic : M8.P3Family.polynomial.Monic := by
      have h := M7.RecipeSignature.signature_properties N (M8.P3Family.recipe N)
      rw [M8.P3Family.signature N hN hdiv] at h
      exact h.1
    have hmod := M8.P3Family.divides_modulus N hdiv
    have hdist := M8.DiagonalPolynomial.distance_two N _ _ M8.P3Family.nontrivial.2.1 hdeg hmonic M8.P3Family.nontrivial.1 (dvd_refl _) hmod
    have hdelta := M8.DiagonalPolynomial.delta_not_image N _ _ hdeg hmonic M8.P3Family.nontrivial.1 (dvd_refl _) hmod
    have hnz := M8.DiagonalPolynomial.coefficients_nonzero N _ M8.P3Family.nontrivial.2.1 hdeg
    have hcoeff : M6.Coordinates.coefficients N M8.P3Family.polynomial = M7.Supports.indicator (M8.P3Family.support N) := by
      rw [← hlit]
      exact M7.Domain.coefficients_indicator N (M8.P3Family.support N)
    rw [hcoeff] at hdist hdelta hnz
    have hw := M8.Diagonal.diagonal_witness N (M7.Supports.indicator (M8.P3Family.support N)) hdelta
    unfold M8.Coverage.PhysicalTwo
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [M7.Transport.distance, M8.P3Family.recipe, ← hcoeff, ← hlit] using hdist
    · simpa only [M8.Coverage.deltaPair, M7.Transport.LX, M7.Transport.CX, M7.Transport.BX, M8.P3Family.recipe] using hw.1
    · exact hw.2
    · intro u hu
      apply M8.Diagonal.logical_lower_bound N (M7.Supports.indicator (M8.P3Family.support N)) u
      all_goals first | exact hnz | simpa only [M7.Transport.LX, M7.Transport.CX, M7.Transport.BX, M8.P3Family.recipe] using hu
