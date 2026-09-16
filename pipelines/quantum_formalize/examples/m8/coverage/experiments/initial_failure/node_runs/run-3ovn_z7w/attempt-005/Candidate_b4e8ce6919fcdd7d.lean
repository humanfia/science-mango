import FrozenTarget_b4e8ce6919fcdd7d
theorem M8.Coverage.p4_physical : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], 8 ≤ N → Even N → M8.Coverage.PhysicalTwo (M8.P4Family.recipe N)
  intro N inst hN hEven
  classical
  let p := M7.Supports.polynomial (M8.P4Family.support N)
  let F := M7.RecipeSignature.signature (M8.P4Family.recipe N)
  have hp : p = M8.P4Family.polynomial := M8.P4Family.literal_polynomial N hN
  have hp0 : p ≠ 0 := by
    rw [hp]
    exact M8.P4Family.nontrivial.2.1
  have hpdeg : p.degree < (N : WithBot ℕ) := by
    apply Polynomial.degree_lt_of_natDegree_lt
    rw [hp, M8.P4Family.nontrivial.2.2]
    omega
  have hprops := M7.RecipeSignature.signature_properties N (M8.P4Family.recipe N)
  have hmon : F.Monic := by
    aesop
  have hmod : F ∣ M6.Cyclic.modulus N := by
    aesop
  have hF : F ≠ 1 := by
    dsimp [F]
    rw [M8.P4Gcd.signature_even N hN hEven]
    split_ifs
    · exact M8.P4Family.nontrivial.1
    · intro heq
      have hd := congrArg Polynomial.natDegree heq
      norm_num [Polynomial.natDegree_pow, Polynomial.natDegree_X_add_one] at hd
  have hdiv : F ∣ p := by
    first
    | aesop
    | change EuclideanDomain.gcd (EuclideanDomain.gcd p p) (M6.Cyclic.modulus N) ∣ p
      exact dvd_trans (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_left _ _)
  have hd := M8.DiagonalPolynomial.distance_two N p F hp0 hpdeg hmon hF hdiv hmod
  have hn := M8.DiagonalPolynomial.delta_not_image N p F hpdeg hmon hF hdiv hmod
  have ha := M8.DiagonalPolynomial.coefficients_nonzero N p hp0 hpdeg
  have hw := M8.Diagonal.diagonal_witness N (M6.Coordinates.coefficients N p)
  have hl := M8.Diagonal.logical_lower_bound N (M6.Coordinates.coefficients N p)
  unfold M8.Coverage.PhysicalTwo
  simp only [p, M7.Domain.coefficients_indicator] at hd hn ha hw hl
  simpa [M7.Transport.distance, M7.Transport.LX, M8.Diagonal.distance,
    M8.Coverage.deltaPair, M8.P4Family.recipe] using
    (show M8.Diagonal.distance N (M7.Supports.indicator (M8.P4Family.support N)) = some 2 ∧
      M8.Coverage.deltaPair N ∈ M7.Transport.LX (M8.P4Family.recipe N) ∧
      M6.Pinned.weight (M8.Coverage.deltaPair N) = 2 ∧
      ∀ u ∈ M7.Transport.LX (M8.P4Family.recipe N), 2 ≤ M6.Pinned.weight u from by
        refine ⟨hd, ?_⟩
        dsimp [M8.Coverage.deltaPair, M7.Transport.LX, M8.P4Family.recipe] at *
        aesop)
