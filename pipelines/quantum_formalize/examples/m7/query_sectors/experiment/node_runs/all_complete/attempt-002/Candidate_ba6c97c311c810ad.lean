import FrozenTarget_ba6c97c311c810ad
theorem M7.QuerySectors.all_complete : QuantumHarnessFrozenTarget := by
  change ∀ (N : ℕ) [NeZero N], ∀ (F : M6.Cyclic.BinaryPolynomial), F.Monic → F ∣ M6.Cyclic.modulus N → F ∈ M7.QuerySectors.allSectors N
  intro N inst F hF hdiv
  classical
  have hmod : M6.Cyclic.modulus N ≠ 0 := by
    intro hz
    have hc := congrArg (fun p : M6.Cyclic.BinaryPolynomial => p.coeff 0) hz
    simpa [M6.Cyclic.modulus, NeZero.ne N, (NeZero.ne N).symm] using hc
  have hle : UniqueFactorizationMonoid.normalizedFactors F ≤ UniqueFactorizationMonoid.normalizedFactors (M6.Cyclic.modulus N) :=
    (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hF.ne_zero hmod).mp hdiv
  have hprod : (UniqueFactorizationMonoid.normalizedFactors F).prod = F := by
    simpa [hF.leadingCoeff] using Polynomial.leadingCoeff_mul_prod_normalizedFactors F
  simp only [M7.QuerySectors.allSectors, Multiset.mem_toFinset, Finset.mem_image, Multiset.mem_powerset]
  exact ⟨UniqueFactorizationMonoid.normalizedFactors F, hle, hprod⟩
