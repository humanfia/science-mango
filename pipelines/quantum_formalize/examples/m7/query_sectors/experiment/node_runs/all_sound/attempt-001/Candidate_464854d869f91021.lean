import FrozenTarget_464854d869f91021
theorem M7.QuerySectors.all_sound : QuantumHarnessFrozenTarget := by
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
