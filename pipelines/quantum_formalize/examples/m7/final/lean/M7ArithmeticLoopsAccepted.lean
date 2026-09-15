import M7ArithmeticLoops

theorem M7.ArithmeticLoops.character_card : ∀ D : ℕ, Fintype.card (M5.Character.BinaryVector D) = 2^D := by
  change ∀ D : ℕ, Fintype.card (Fin D → ZMod 2) = 2 ^ D
  intro D
  simp [Fintype.card_fun, ZMod.card]

theorem M7.ArithmeticLoops.divisor_card : ∀ (N : ℕ), 0 < N → ∀ A B : Finset ℕ, (M5.Connectivity.supportGcd N A B).divisors.card ≤ M7.ArithmeticLoops.divisorCount N := by
  intro N hN A B
  change (M5.Connectivity.supportGcd N A B).divisors.card ≤ N.divisors.card
  apply Finset.card_le_card
  intro d hd
  apply Nat.mem_divisors.mpr
  refine ⟨dvd_trans (Nat.mem_divisors.mp hd).1 ?_, Nat.ne_of_gt hN⟩
  rw [M7.ResiduePrefix.gcd_union]
  exact Nat.gcd_dvd_left N ((A ∪ B).gcd id)

theorem M7.ArithmeticLoops.exclusion_cap : ∀ (N : ℕ), 0 < N → ∀ (F : M5.BinaryPolynomial) (S : Finset M5.BinaryPolynomial), F.Monic → F ∣ M5.cyclicModulus N → S ⊆ M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F → (F * (∏ p ∈ S, p)).Monic ∧ (F * (∏ p ∈ S, p)).natDegree ≤ N := by
  classical
  intro N hN F S hF hFdvd hS
  have hmonic : (F * (∏ p ∈ S, p)).Monic := by
    apply hF.mul
    apply Polynomial.monic_prod_of_monic
    intro p hp
    exact (M5.PolynomialIndicator.residual_factors_regular F N hN hF hFdvd p (hS hp)).1
  have hdvd : F * (∏ p ∈ S, p) ∣ M5.cyclicModulus N := by
    apply M5.FactorProduct.cyclic_cap <;> assumption
  have hne : M5.cyclicModulus N ≠ 0 := by
    intro hz
    have hq := M5.PolynomialExclusion.cyclic_quotient_nonzero F N hN hF hFdvd
    apply hq
    simp [hz]
  have hdeg : (M5.cyclicModulus N).natDegree ≤ N := by
    simpa [M5.cyclicModulus] using
      (Polynomial.natDegree_add_le ((Polynomial.X : M5.BinaryPolynomial) ^ N) 1)
  exact ⟨hmonic, (Polynomial.natDegree_le_of_dvd hdvd hne).trans hdeg⟩

theorem M7.ArithmeticLoops.factor_card : ∀ (N : ℕ), 0 < N → ∀ F : M5.BinaryPolynomial, F.Monic → F ∣ M5.cyclicModulus N → (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).card ≤ M7.ArithmeticLoops.factorCount N := by
  classical
  intro N hN F hF hdiv
  have hq : M5.cyclicModulus N / F ≠ 0 :=
    M5.PolynomialExclusion.cyclic_quotient_nonzero F N hN hF hdiv
  have hM : M5.cyclicModulus N ≠ 0 := by
    intro h
    apply hq
    simp [h]
  have hprod : F * (M5.cyclicModulus N / F) ∣ M5.cyclicModulus N :=
    (M5.PolynomialExclusion.factor_dvd_quotient F (M5.cyclicModulus N)
      (M5.cyclicModulus N / F) hF.ne_zero hdiv).mp (dvd_refl _)
  have hd : M5.cyclicModulus N / F ∣ M5.cyclicModulus N :=
    dvd_trans ⟨F, mul_comm _ _⟩ hprod
  have hle :=
    (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hq hM).mp hd
  change (UniqueFactorizationMonoid.normalizedFactors (M5.cyclicModulus N / F)).toFinset.card ≤
    (UniqueFactorizationMonoid.normalizedFactors (M5.cyclicModulus N)).toFinset.card
  apply Finset.card_le_card
  intro p hp
  simp only [Multiset.mem_toFinset] at hp ⊢
  exact Multiset.mem_of_le hle hp

theorem M7.ArithmeticLoops.character_visits : ∀ (N : ℕ), 0 < N → ∀ (w : ℕ) (E : Finset M5.BinaryPolynomial) (A B : Finset ℕ), M7.PrefixSector.ValidSector N E → M7.ArithmeticLoops.characterVisits N w E A B ≤ 2 * E.card * M7.ArithmeticLoops.divisorCount N * 2^(M7.ArithmeticLoops.factorCount N + N) := by
  classical
  intro N hN w E A B hE
  change M7.ArithmeticLoops.characterVisits N w E A B ≤ _
  unfold M7.ArithmeticLoops.characterVisits
  split_ifs with hguard
  · have hinner : ∀ F ∈ E,
        (∑ S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset,
          2 * Fintype.card (M5.Character.BinaryVector (F * (∏ p ∈ S, p)).natDegree)) ≤
        2 ^ M7.ArithmeticLoops.factorCount N * (2 * 2 ^ N) := by
      intro F hFE
      have hF : F.Monic ∧ F ∣ M5.cyclicModulus N := by
        have hv := hE
        unfold M7.PrefixSector.ValidSector at hv
        aesop
      calc
        _ ≤ ∑ S ∈ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).powerset,
            2 * 2 ^ N := by
          apply Finset.sum_le_sum
          intro S hS
          rw [M7.ArithmeticLoops.character_card]
          apply Nat.mul_le_mul_left
          apply Nat.pow_le_pow_right (by omega)
          exact (M7.ArithmeticLoops.exclusion_cap N hN F S hF.1 hF.2
            (Finset.mem_powerset.mp hS)).2
        _ = 2 ^ (M5.PolynomialExclusion.residualFactors (M5.cyclicModulus N) F).card *
            (2 * 2 ^ N) := by
          simp
        _ ≤ 2 ^ M7.ArithmeticLoops.factorCount N * (2 * 2 ^ N) := by
          apply Nat.mul_le_mul_right
          exact Nat.pow_le_pow_right (by omega)
            (M7.ArithmeticLoops.factor_card N hN F hF.1 hF.2)
    calc
      _ ≤ ∑ F ∈ E, M7.ArithmeticLoops.divisorCount N *
          (2 ^ M7.ArithmeticLoops.factorCount N * (2 * 2 ^ N)) := by
        apply Finset.sum_le_sum
        intro F hFE
        calc
          _ ≤ ∑ _d ∈ (M5.Connectivity.supportGcd N A B).divisors,
              2 ^ M7.ArithmeticLoops.factorCount N * (2 * 2 ^ N) := by
            apply Finset.sum_le_sum
            intro d hd
            exact hinner F hFE
          _ = (M5.Connectivity.supportGcd N A B).divisors.card *
              (2 ^ M7.ArithmeticLoops.factorCount N * (2 * 2 ^ N)) := by
            simp
          _ ≤ M7.ArithmeticLoops.divisorCount N *
              (2 ^ M7.ArithmeticLoops.factorCount N * (2 * 2 ^ N)) :=
            Nat.mul_le_mul_right _ (M7.ArithmeticLoops.divisor_card N hN A B)
      _ = 2 * E.card * M7.ArithmeticLoops.divisorCount N *
          2 ^ (M7.ArithmeticLoops.factorCount N + N) := by
        simp only [Finset.sum_const, smul_eq_mul, pow_add]
        ring
  · exact Nat.zero_le _
#print axioms M7.ArithmeticLoops.character_card
#print axioms M7.ArithmeticLoops.divisor_card
#print axioms M7.ArithmeticLoops.exclusion_cap
#print axioms M7.ArithmeticLoops.factor_card
#print axioms M7.ArithmeticLoops.character_visits
