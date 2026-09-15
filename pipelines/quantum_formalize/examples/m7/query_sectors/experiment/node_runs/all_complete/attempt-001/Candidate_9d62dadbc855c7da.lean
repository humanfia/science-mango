import FrozenTarget_9d62dadbc855c7da
theorem M7.QuerySectors.all_complete : QuantumHarnessFrozenTarget := by
  classical
  change ∀ (N : ℕ) [NeZero N], ∀ (F : M6.Cyclic.BinaryPolynomial), F.Monic → F ∣ M6.Cyclic.modulus N → F ∈ M7.QuerySectors.allSectors N
  intro N inst F hF hdiv
  have hmod : M6.Cyclic.modulus N ≠ 0 := by
    intro hz
    have hc := congrArg (fun p : M6.Cyclic.BinaryPolynomial => p.coeff 0) hz
    simpa [M6.Cyclic.modulus, Polynomial.coeff_X_pow, NeZero.ne N] using hc
  have hle : UniqueFactorizationMonoid.normalizedFactors F ≤
      UniqueFactorizationMonoid.normalizedFactors (M6.Cyclic.modulus N) := by
    first
    | exact (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hF.ne_zero hmod).mp hdiv
    | exact (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hmod).mp hdiv
  have hprod : (UniqueFactorizationMonoid.normalizedFactors F).prod = F := by
    simpa [hF.leadingCoeff] using Polynomial.leadingCoeff_mul_prod_normalizedFactors F
  simp only [M7.QuerySectors.allSectors, Multiset.mem_toFinset, Multiset.mem_map,
    Finset.mem_image, Multiset.mem_powerset]
  exact ⟨UniqueFactorizationMonoid.normalizedFactors F, hle, hprod⟩
