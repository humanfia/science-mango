import M8Coverage

theorem M8.Coverage.p3_physical : ∀ (N : ℕ) [NeZero N], 3 ≤ N → 3 ∣ N → M8.Coverage.PhysicalTwo (M8.P3Family.recipe N) := by
  intro N inst hN hdiv
  have hp0 := M8.P3Family.nontrivial.2.1
  have hp1 := M8.P3Family.nontrivial.1
  have hdeg : M8.P3Family.polynomial.degree < (N : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hp0, M8.P3Family.nontrivial.2.2]
    exact_mod_cast (show 2 < N by omega)
  have hm : M8.P3Family.polynomial.Monic := by
    have hs := (M7.RecipeSignature.signature_properties N (M8.P3Family.recipe N)).1
    rw [M8.P3Family.signature N hN hdiv] at hs
    exact hs
  have hdvd := M8.P3Family.divides_modulus N hdiv
  have hn := M8.DiagonalPolynomial.coefficients_nonzero N M8.P3Family.polynomial hp0 hdeg
  have hi := M8.DiagonalPolynomial.delta_not_image N M8.P3Family.polynomial M8.P3Family.polynomial hdeg hm hp1 (dvd_refl _) hdvd
  have hd := M8.DiagonalPolynomial.distance_two N M8.P3Family.polynomial M8.P3Family.polynomial hp0 hdeg hm hp1 (dvd_refl _) hdvd
  have hw := M8.Diagonal.diagonal_witness N (M6.Coordinates.coefficients N M8.P3Family.polynomial) hi
  have hc : M6.Coordinates.coefficients N M8.P3Family.polynomial = M7.Supports.indicator (M8.P3Family.support N) := by
    rw [← M8.P3Family.literal_polynomial N hN]
    exact M7.Domain.coefficients_indicator N _
  have hx : M7.Transport.LX (M8.P3Family.recipe N) = M6.Spaces.logicalWords N (M6.Coordinates.coefficients N M8.P3Family.polynomial) (M6.Coordinates.coefficients N M8.P3Family.polynomial) := by
    simp only [M7.Transport.LX, M7.Transport.CX, M7.Transport.BX, M8.P3Family.recipe, M6.Spaces.logicalWords, hc]
  refine ⟨?_, ?_, hw.2, ?_⟩
  · simpa only [M7.Transport.distance, M8.P3Family.recipe, M8.P3Family.literal_polynomial N hN, M6.Final.quantumDistance, M6.Final.BX, M6.Final.CX, M6.Final.BZ, M6.Final.CZ, M8.Diagonal.distance] using hd
  · rw [hx]
    exact hw.1
  · intro u hu
    rw [hx] at hu
    exact M8.Diagonal.logical_lower_bound N _ u hn hu
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], 3 ≤ N → 3 ∣ N → M8.PhysicalBridge.signature (M8.P3Family.recipe N) = M8.P3Family.polynomial ∧ M8.Coverage.RecognizedTwo (M8.P3Family.recipe N) ∧ (∀ g : M7.Action.Record N, ¬ M8.CoverageFoundation.Separated (M7.Action.act g (M8.P3Family.recipe N)))
