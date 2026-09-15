import M5FactorProduct

theorem M5.FactorProduct.common_factor_dvd : ∀ F H A : M5.BinaryPolynomial, F ≠ 0 → F ∣ A → (F * H ∣ A ↔ H ∣ A / F) := by
  change ∀ F H A : M5.BinaryPolynomial, F ≠ 0 → F ∣ A → (F * H ∣ A ↔ H ∣ A / F)
  intro F H A hF hFA
  constructor
  · intro h
    exact EuclideanDomain.dvd_div_of_mul_dvd h
  · rintro ⟨K, hK⟩
    refine ⟨K, ?_⟩
    calc
      A = F * (A / F) := (EuclideanDomain.mul_div_cancel' hF hFA).symm
      _ = F * (H * K) := congrArg (fun x => F * x) hK
      _ = (F * H) * K := (mul_assoc F H K).symm

theorem M5.FactorProduct.distinct_irreducibles_coprime : ∀ p q : M5.BinaryPolynomial, p.Monic → q.Monic → Irreducible p → Irreducible q → p ≠ q → IsCoprime p q := by
  change ∀ p q : M5.BinaryPolynomial, p.Monic → q.Monic → Irreducible p → Irreducible q → p ≠ q → IsCoprime p q
  intro p q hpm hqm hp hq hpq
  apply hp.coprime_iff_not_dvd.mpr
  rintro ⟨r, hr⟩
  rcases hq.isUnit_or_isUnit hr with hpu | hru
  · exact hp.not_isUnit hpu
  · rcases hru with ⟨u, hu⟩
    apply hpq
    apply Polynomial.eq_of_monic_of_associated hpm hqm
    exact ⟨u, by simpa only [hu] using hr.symm⟩

theorem M5.FactorProduct.irreducible_product_dvd : ∀ (S : Finset M5.BinaryPolynomial) (A : M5.BinaryPolynomial), (∀ p ∈ S, p.Monic ∧ Irreducible p) → ((∏ p ∈ S, p) ∣ A ↔ ∀ p ∈ S, p ∣ A) := by
  classical
  change ∀ (S : Finset M5.BinaryPolynomial) (A : M5.BinaryPolynomial), (∀ p ∈ S, p.Monic ∧ Irreducible p) → ((∏ p ∈ S, p) ∣ A ↔ ∀ p ∈ S, p ∣ A)
  intro S A hS
  constructor
  · intro h p hp
    exact (Finset.dvd_prod_of_mem (fun q : M5.BinaryPolynomial => q) hp).trans h
  · intro h
    refine Finset.prod_dvd_of_coprime ?_ h
    intro p hp q hq hpq
    exact M5.FactorProduct.distinct_irreducibles_coprime p q
      (hS p hp).1 (hS q hq).1 (hS p hp).2 (hS q hq).2 hpq

theorem M5.FactorProduct.cyclic_cap : ∀ (S : Finset M5.BinaryPolynomial) (F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → S ⊆ M5.FactorProduct.residualFactors (M5.cyclicModulus N) F → F * (∏ p ∈ S, p) ∣ M5.cyclicModulus N := by
  classical
  change ∀ (S : Finset M5.BinaryPolynomial) (F : M5.BinaryPolynomial) (N : ℕ), 0 < N → F.Monic → F ∣ M5.cyclicModulus N → S ⊆ M5.FactorProduct.residualFactors (M5.cyclicModulus N) F → F * (∏ p ∈ S, p) ∣ M5.cyclicModulus N
  intro S F N hN hF hFdvd hS
  have hmem : ∀ p ∈ S, p ∈ UniqueFactorizationMonoid.normalizedFactors (M5.cyclicModulus N / F) := by
    intro p hp
    simpa [M5.FactorProduct.residualFactors] using hS hp
  have hprops : ∀ p ∈ S, p.Monic ∧ Irreducible p := by
    intro p hp
    have hi := UniqueFactorizationMonoid.irreducible_of_normalized_factor p (hmem p hp)
    refine ⟨?_, hi⟩
    apply M5.Signature.binary_monic
    exact hi.ne_zero
  apply (M5.FactorProduct.common_factor_dvd F (∏ p ∈ S, p) (M5.cyclicModulus N) hF.ne_zero hFdvd).mpr
  apply (M5.FactorProduct.irreducible_product_dvd S (M5.cyclicModulus N / F) hprops).mpr
  intro p hp
  exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (hmem p hp)

theorem M5.FactorProduct.product_event_iff : ∀ (S : Finset M5.BinaryPolynomial) (F A : M5.BinaryPolynomial), F ≠ 0 → F ∣ A → (∀ p ∈ S, p.Monic ∧ Irreducible p) → (F * (∏ p ∈ S, p) ∣ A ↔ ∀ p ∈ S, F * p ∣ A) := by
  classical
  change ∀ (S : Finset M5.BinaryPolynomial) (F A : M5.BinaryPolynomial), F ≠ 0 → F ∣ A → (∀ p ∈ S, p.Monic ∧ Irreducible p) → (F * (∏ p ∈ S, p) ∣ A ↔ ∀ p ∈ S, F * p ∣ A)
  intro S F A hF hFA hS
  rw [M5.FactorProduct.common_factor_dvd F (∏ p ∈ S, p) A hF hFA,
    M5.FactorProduct.irreducible_product_dvd S (A / F) hS]
  constructor
  · intro h p hp
    exact (M5.FactorProduct.common_factor_dvd F p A hF hFA).mpr (h p hp)
  · intro h p hp
    exact (M5.FactorProduct.common_factor_dvd F p A hF hFA).mp (h p hp)
#print axioms M5.FactorProduct.common_factor_dvd
#print axioms M5.FactorProduct.distinct_irreducibles_coprime
#print axioms M5.FactorProduct.irreducible_product_dvd
#print axioms M5.FactorProduct.cyclic_cap
#print axioms M5.FactorProduct.product_event_iff
