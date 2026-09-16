import FrozenTarget_5bf559a781d0d3ec
theorem M8.Coverage.p4_physical : QuantumHarnessFrozenTarget := by
  intro N inst hN hEven
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
  have hmonic : F.Monic := by
    dsimp [F]
    aesop
  have hmod : F ∣ M6.Cyclic.modulus N := by
    dsimp [F]
    aesop
  have hdiv : F ∣ p := by
    exact dvd_trans (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_left _ _)
  have hF : F ≠ 1 := by
    dsimp [F]
    rw [M8.P4Gcd.signature_even N hN hEven]
    split_ifs
    · exact M8.P4Family.nontrivial.1
    · intro h
      have hd := congrArg Polynomial.natDegree h
      norm_num [Polynomial.natDegree_pow] at hd
  have hd := M8.DiagonalPolynomial.distance_two N p F hp0 hpdeg hmonic hF hdiv hmod
  have hn := M8.DiagonalPolynomial.coefficients_nonzero N p hp0 hpdeg
  have he := M8.DiagonalPolynomial.delta_not_image N p F hpdeg hmonic hF hdiv hmod
  have hc : M6.Coordinates.coefficients N p = M7.Supports.indicator (M8.P4Family.support N) := by
    exact M7.Domain.coefficients_indicator N (M8.P4Family.support N)
  rw [hc] at hd hn he
  unfold M8.Coverage.PhysicalTwo
  constructor
  · simpa only [M7.Transport.distance, M8.P4Family.recipe, M7.Domain.coefficients_indicator] using hd
  · have hw := M8.Diagonal.diagonal_witness N (M7.Supports.indicator (M8.P4Family.support N)) he
    have hl := M8.Diagonal.logical_lower_bound N (M7.Supports.indicator (M8.P4Family.support N)) hn
    simpa only [M8.Coverage.deltaPair, M7.Transport.LX, M8.P4Family.recipe, M7.Domain.coefficients_indicator] using And.intro hw.1 (And.intro hw.2 hl)
