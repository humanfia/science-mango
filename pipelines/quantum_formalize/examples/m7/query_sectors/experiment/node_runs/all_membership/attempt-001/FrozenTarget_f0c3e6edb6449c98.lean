import M7QuerySectors

theorem M7.QuerySectors.all_complete : ∀ (N : ℕ) [NeZero N], ∀ (F : M6.Cyclic.BinaryPolynomial), F.Monic → F ∣ M6.Cyclic.modulus N → F ∈ M7.QuerySectors.allSectors N := by
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

theorem M7.QuerySectors.all_sound : ∀ (N : ℕ) [NeZero N], ∀ (F : M6.Cyclic.BinaryPolynomial), F ∈ M7.QuerySectors.allSectors N → F.Monic ∧ F ∣ M6.Cyclic.modulus N := by
  classical
  change ∀ (N : ℕ) [NeZero N], ∀ (F : M6.Cyclic.BinaryPolynomial), F ∈ M7.QuerySectors.allSectors N → F.Monic ∧ F ∣ M6.Cyclic.modulus N
  intro N inst F hF
  simp only [M7.QuerySectors.allSectors, Finset.mem_image, Multiset.mem_toFinset,
    Multiset.mem_map, Multiset.mem_powerset] at hF
  rcases hF with ⟨s, hs, rfl⟩
  have hmod : M6.Cyclic.modulus N ≠ 0 := (M7.SignatureTau.modulus_monic N).ne_zero
  have hd : s.prod ∣ M6.Cyclic.modulus N :=
    (Multiset.prod_dvd_prod_of_le hs).trans
      (UniqueFactorizationMonoid.prod_normalizedFactors hmod).dvd
  refine ⟨?_, hd⟩
  apply M7.SignatureTau.binary_monic
  intro hz
  rw [hz] at hd
  exact hmod (zero_dvd_iff.mp hd)
def QuantumHarnessFrozenTarget : Prop :=
  ∀ (N : ℕ) [NeZero N], ∀ (F : M6.Cyclic.BinaryPolynomial), F ∈ M7.QuerySectors.allSectors N ↔ F.Monic ∧ F ∣ M6.Cyclic.modulus N
