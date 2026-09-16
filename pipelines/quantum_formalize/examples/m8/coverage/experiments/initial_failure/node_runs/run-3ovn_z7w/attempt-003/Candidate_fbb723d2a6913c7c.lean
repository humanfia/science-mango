import FrozenTarget_fbb723d2a6913c7c
theorem M8.Coverage.p4_physical : QuantumHarnessFrozenTarget := by
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
  have hmonic : F.Monic := by
    dsimp [F]
    aesop
  have hmod : F ∣ M6.Cyclic.modulus N := by
    dsimp [F]
    aesop
  have hF : F ≠ 1 := by
    dsimp [F]
    rw [M8.P4Gcd.signature_even N hN hEven]
    split_ifs
    · exact M8.P4Family.nontrivial.1
    · intro he
      have hv := congrArg (Polynomial.eval (1 : ZMod 2)) he
      norm_num at hv
  have hdiv : F ∣ p := by
    dsimp [F, p, M7.RecipeSignature.signature, M8.P4Family.recipe]
    exact dvd_trans (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_left _ _)
  have hd := M8.DiagonalPolynomial.distance_two N p F hp0 hpdeg hmonic hF hdiv hmod
  have hn := M8.DiagonalPolynomial.delta_not_image N p F hpdeg hmonic hF hdiv hmod
  have ha := M8.DiagonalPolynomial.coefficients_nonzero N p hp0 hpdeg
  have hw := M8.Diagonal.diagonal_witness N (M6.Coordinates.coefficients N p)
  have hl := M8.Diagonal.logical_lower_bound N (M6.Coordinates.coefficients N p)
  unfold M8.Coverage.PhysicalTwo
  constructor
  · simpa [M7.Transport.distance, M8.Diagonal.distance, M8.P4Family.recipe, p,
      M7.Domain.coefficients_indicator] using hd
  · dsimp [M8.Coverage.deltaPair, M7.Transport.LX, M8.P4Family.recipe]
    simp only [p, M7.Domain.coefficients_indicator] at hn ha hw hl
    aesop
