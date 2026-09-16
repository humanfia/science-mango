import M8Coverage

theorem M8.Coverage.mixed_recognized : ∀ (N : ℕ) [NeZero N], 7 ≤ N → M8.Coverage.Recognized (M8.MixedFamily.recipe N) ∧ M8.PhysicalBridge.signature (M8.MixedFamily.recipe N) = M8.MixedFamily.a ∧ (∀ g : M7.Action.Record N, ¬ M8.CoverageFoundation.Separated (M7.Action.act g (M8.MixedFamily.recipe N))) ∧ (∀ g : M7.Action.Record N, ¬ M8.MixedNonproduct.Product (M7.Action.act g (M8.MixedFamily.recipe N))) := by
  intro N inst hN
  have hv := M8.MixedFamily.valid N hN
  have hs : M8.PhysicalBridge.signature (M8.MixedFamily.recipe N) = M8.MixedFamily.a := by
    exact M8.MixedFamily.signature N hN
  rcases M8.MixedFamily.support_data N hN with ⟨_, _, hL, hR, _⟩
  have ha : M7.Action.affine (1 : (ZMod N)ˣ) (0 : ZMod N) = id := by
    funext x
    simp [M7.Action.affine]
  have ht : M8.Anchor.trial (M8.MixedFamily.recipe N) false 1 0 0 = M8.MixedFamily.recipe N := by
    simp [M8.Anchor.trial, M8.Anchor.record, M7.Action.act] <;> simp [ha]
  have he : M8.Anchor.Eligible (M8.MixedFamily.recipe N) false 0 0 := by
    simpa [M8.Anchor.Eligible, M8.Anchor.left, M8.Anchor.right, M8.MixedFamily.recipe] using And.intro hL hR
  have ho : M8.OrbitSpan.value (M8.MixedFamily.recipe N) ≤ M8.Cutoff.limit N := by
    apply (M8.OrbitSpan.anchor_minimum N (M8.MixedFamily.recipe N) ⟨0, hL⟩ ⟨0, hR⟩ (M8.Cutoff.limit N)).mpr
    refine ⟨false, 1, 0, 0, he, ?_⟩
    rw [ht]
    exact M8.MixedFamily.span_cutoff N hN
  refine ⟨?_, hs, ?_, M8.MixedNonproduct.orbit_nonproduct N hN⟩
  · unfold M8.Coverage.Recognized
    apply (M8.Solver.recognized_exact N (M8.MixedFamily.recipe N) 2 (by decide) hv).mpr
    refine ⟨?_, ho⟩
    rw [hs]
    exact M8.MixedFamily.nontrivial.1
  · intro g
    apply M8.CoverageFoundation.orbit_no_separated N (M8.MixedFamily.recipe N) g
    exact Or.inl (M8.MixedFamily.full_direction N hN)

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

theorem M8.Coverage.p4_physical : ∀ (N : ℕ) [NeZero N], 8 ≤ N → Even N → M8.Coverage.PhysicalTwo (M8.P4Family.recipe N) := by
  intro N inst hN hEven
  let p := M7.Supports.polynomial (M8.P4Family.support N)
  let F := M7.RecipeSignature.signature (M8.P4Family.recipe N)
  have hp : p = M8.P4Family.polynomial := M8.P4Family.literal_polynomial N hN
  have hp0 : p ≠ 0 := by
    rw [hp]
    exact M8.P4Family.nontrivial.2.1
  have hdeg : p.degree < (N : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hp0, hp, M8.P4Family.nontrivial.2.2]
    exact_mod_cast (show 3 < N by omega)
  have hm : F.Monic := (M7.RecipeSignature.signature_properties N (M8.P4Family.recipe N)).1
  have hmod : F ∣ M6.Cyclic.modulus N := (M7.RecipeSignature.signature_properties N (M8.P4Family.recipe N)).2
  have hdvd : F ∣ p := dvd_trans (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_left _ _)
  have hF : F ≠ 1 := by
    dsimp [F]
    rw [M8.P4Gcd.signature_even N hN hEven]
    split_ifs
    · exact M8.P4Family.nontrivial.1
    · intro h
      have he := congrArg (Polynomial.eval (1 : ZMod 2)) h
      norm_num at he
      exact (by decide : (2 : ZMod 2) ≠ 1) he
  have hn := M8.DiagonalPolynomial.coefficients_nonzero N p hp0 hdeg
  have hi := M8.DiagonalPolynomial.delta_not_image N p F hdeg hm hF hdvd hmod
  have hd := M8.DiagonalPolynomial.distance_two N p F hp0 hdeg hm hF hdvd hmod
  have hw := M8.Diagonal.diagonal_witness N (M6.Coordinates.coefficients N p) hi
  have hc : M6.Coordinates.coefficients N p = M7.Supports.indicator (M8.P4Family.support N) := M7.Domain.coefficients_indicator N _
  have hx : M7.Transport.LX (M8.P4Family.recipe N) = M6.Spaces.logicalWords N (M6.Coordinates.coefficients N p) (M6.Coordinates.coefficients N p) := by
    simp only [M7.Transport.LX, M7.Transport.CX, M7.Transport.BX, M8.P4Family.recipe, M6.Spaces.logicalWords, hc]
  refine ⟨?_, ?_, hw.2, ?_⟩
  · simpa only [M7.Transport.distance, M8.P4Family.recipe, M6.Final.quantumDistance, M6.Final.BX, M6.Final.CX, M6.Final.BZ, M6.Final.CZ, M8.Diagonal.distance] using hd
  · rw [hx]
    exact hw.1
  · intro u hu
    rw [hx] at hu
    exact M8.Diagonal.logical_lower_bound N _ u hn hu

theorem M8.Coverage.p3_recognized : ∀ (N : ℕ) [NeZero N], 3 ≤ N → 3 ∣ N → M8.PhysicalBridge.signature (M8.P3Family.recipe N) = M8.P3Family.polynomial ∧ M8.Coverage.RecognizedTwo (M8.P3Family.recipe N) ∧ (∀ g : M7.Action.Record N, ¬ M8.CoverageFoundation.Separated (M7.Action.act g (M8.P3Family.recipe N))) := by
  intro N inst hN hdiv
  have hv := M8.P3Family.valid N hN
  have hp := M8.Coverage.p3_physical N hN hdiv
  have hs : M8.PhysicalBridge.signature (M8.P3Family.recipe N) = M8.P3Family.polynomial := M8.P3Family.signature N hN hdiv
  have hz := (M8.P3Family.support_data N hN).2.1
  have hn : (M8.P3Family.support N).Nonempty := ⟨0, hz⟩
  have hsig : M8.PhysicalBridge.signature (M8.P3Family.recipe N) ≠ 1 := by
    rw [hs]
    exact M8.P3Family.nontrivial.1
  let g : M7.Action.Record N := ⟨1, false, 0, 0⟩
  have ha : M7.Action.affine (1 : (ZMod N)ˣ) 0 = id := by
    funext x
    simp [M7.Action.affine]
  have hg : M7.Action.act g (M8.P3Family.recipe N) = M8.P3Family.recipe N := by
    change (Finset.image (M7.Action.affine 1 0) (M8.P3Family.recipe N).1, Finset.image (M7.Action.affine 1 0) (M8.P3Family.recipe N).2) = M8.P3Family.recipe N
    rw [ha]
    simp
  have hspan : M8.OrbitSpan.value (M8.P3Family.recipe N) ≤ M8.Cutoff.limit N := by
    apply (M8.OrbitSpan.small_iff N (M8.P3Family.recipe N) hn hn (M8.Cutoff.limit N)).2
    refine ⟨g, ?_, ?_⟩
    · rw [hg]
      change 0 ∈ M8.P3Family.support N ∧ 0 ∈ M8.P3Family.support N
      exact ⟨hz, hz⟩
    · rw [hg]
      exact M8.P3Family.span_cutoff N hN
  obtain ⟨d, z, choice, k, hr⟩ := (M8.Solver.recognized_exact N (M8.P3Family.recipe N) 3 (by omega) hv).2 ⟨hsig, hspan⟩
  have hd := (M8.Solver.recognized_correct N (M8.P3Family.recipe N) 3 (by omega) hv _ d z choice k hr).2.2.1
  have hd2 : d = 2 := Option.some.inj (hd.symm.trans hp.1)
  subst d
  refine ⟨hs, ⟨z, choice, k, hr⟩, ?_⟩
  intro a
  apply M8.CoverageFoundation.orbit_no_separated N (M8.P3Family.recipe N) a
  exact Or.inl (M8.P3Family.full_direction N hN)

theorem M8.Coverage.p4_recognized : ∀ (N : ℕ) [NeZero N], 8 ≤ N → Even N → M8.Coverage.RecognizedTwo (M8.P4Family.recipe N) ∧ M8.PhysicalBridge.signature (M8.P4Family.recipe N) = (if 4 ∣ N then M8.P4Family.polynomial else (Polynomial.X+1)^2) ∧ (∀ g : M7.Action.Record N, ¬ M8.CoverageFoundation.Separated (M7.Action.act g (M8.P4Family.recipe N))) := by
  intro N inst hN hEven
  have hv := M8.P4Family.valid N (by omega)
  have hp := M8.Coverage.p4_physical N hN hEven
  have hd : M7.Transport.distance (M8.P4Family.recipe N) = some 2 := hp.1
  have hz : (0 : ZMod N) ∈ M8.P4Family.support N := (M8.P4Family.support_data N (by omega)).2.1
  have hne : (M8.P4Family.support N).Nonempty := ⟨0, hz⟩
  let g : M7.Action.Record N := M8.Anchor.record false 1 0 0
  have hg : M7.Action.act g (M8.P4Family.recipe N) = M8.P4Family.recipe N := by
    simp [g, M8.Anchor.record, M7.Action.act]
    have ha : M7.Action.affine (1 : (ZMod N)ˣ) 0 = id := by
      funext x
      simp [M7.Action.affine]
    simpa only [ha, Finset.image_id]
  have hs : M8.OrbitSpan.value (M8.P4Family.recipe N) ≤ M8.Cutoff.limit N := by
    apply (M8.OrbitSpan.small_iff N (M8.P4Family.recipe N) hne hne (M8.Cutoff.limit N)).2
    refine ⟨g, ?_, ?_⟩
    · rw [hg]
      change (0 : ZMod N) ∈ M8.P4Family.support N ∧ (0 : ZMod N) ∈ M8.P4Family.support N
      exact ⟨hz, hz⟩
    · rw [hg]
      exact M8.P4Family.span_cutoff N (by omega)
  have hF : M8.PhysicalBridge.signature (M8.P4Family.recipe N) ≠ 1 := by
    intro h
    have hn := (M8.RawParameters.raw_noLogical N 4 (M8.P4Family.recipe N) (by omega) hv).1.mpr h
    rw [hd] at hn
    contradiction
  obtain ⟨d, z, choice, k, hr⟩ := (M8.Solver.recognized_exact N (M8.P4Family.recipe N) 4 (by omega) hv).2 ⟨hF, hs⟩
  have hc := M8.Solver.recognized_correct N (M8.P4Family.recipe N) 4 (by omega) hv _ d z choice k hr
  have he : d = 2 := Option.some.inj (hc.2.2.1.symm.trans hd)
  subst d
  refine ⟨⟨z, choice, k, hr⟩, ?_, ?_⟩
  · exact M8.P4Gcd.signature_even N hN hEven
  · intro a
    apply M8.CoverageFoundation.orbit_no_separated N (M8.P4Family.recipe N) a
    exact Or.inl (M8.P4Family.full_direction N (by omega))

theorem M8.Coverage.p4_full_multiplicity : ∀ (N : ℕ) [NeZero N], 8 ≤ N → ∀ v m : ℕ, 0 < v → Odd m → N = 2^v*m → M8.PhysicalBridge.signature (M8.P4Family.recipe N) = (Polynomial.X+1)^(min 3 (2^v)) ∧ M8.Coverage.RecognizedTwo (M8.P4Family.recipe N) := by
  intro N inst hN v m hv hm hEq
  have hEven : Even N := by
    cases v with
    | zero => omega
    | succ k =>
      refine ⟨2^k*m, ?_⟩
      rw [hEq, pow_succ]
      ring
  constructor
  · exact M8.P4Gcd.full_multiplicity N hN v m hv hm hEq
  · exact (M8.Coverage.p4_recognized N hN hEven).1
#print axioms M8.Coverage.mixed_recognized
#print axioms M8.Coverage.p3_physical
#print axioms M8.Coverage.p3_recognized
#print axioms M8.Coverage.p4_physical
#print axioms M8.Coverage.p4_recognized
#print axioms M8.Coverage.p4_full_multiplicity
