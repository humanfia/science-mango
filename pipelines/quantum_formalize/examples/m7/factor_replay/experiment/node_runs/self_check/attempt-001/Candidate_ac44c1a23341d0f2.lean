import FrozenTarget_ac44c1a23341d0f2
theorem M7.FactorReplay.self_check : QuantumHarnessFrozenTarget := by
  change ∀ F : M7.FactorReplay.BP, F.Monic → M7.FactorReplay.check F (M7.FactorReplay.expected F) = true
  intro F hF
  classical
  apply (M7.FactorReplay.factor_check_exact F _).2
  refine ⟨?_, ?_, ?_⟩
  · simp [M7.FactorReplay.expected, List.map_map, Function.comp_def]
  · intro t ht
    simp only [M7.FactorReplay.expected, List.mem_map, Finset.mem_toList,
      Multiset.mem_toFinset] at ht
    obtain ⟨p, hp, rfl⟩ := ht
    have hi : Irreducible p := by
      first
      | exact (UniqueFactorizationMonoid.prime_of_normalized_factor hp).irreducible
      | exact (UniqueFactorizationMonoid.prime_of_normalized_factor p hp).irreducible
    have hn : normalize p = p := by
      first
      | exact UniqueFactorizationMonoid.normalize_normalized_factor hp
      | exact UniqueFactorizationMonoid.normalize_normalized_factor p hp
      | simpa using UniqueFactorizationMonoid.normalize_eq_self_of_mem_normalizedFactors hp
    refine ⟨?_, hi, ?_⟩
    · rw [← hn]
      exact Polynomial.monic_normalize hi.ne_zero
    · exact Multiset.count_pos.mpr hp
  · have hprod : (UniqueFactorizationMonoid.normalizedFactors F).prod = F := by
      rw [UniqueFactorizationMonoid.prod_normalizedFactors_eq hF.ne_zero]
      exact hF.normalize
    rw [← hprod]
    first
    | simpa [M7.FactorReplay.product, M7.FactorReplay.expected,
        List.map_map, Function.comp_def] using
        (Finset.prod_multiset_count (UniqueFactorizationMonoid.normalizedFactors F))
    | simpa [M7.FactorReplay.product, M7.FactorReplay.expected,
        List.map_map, Function.comp_def, ← Multiset.prod_coe] using
        (Finset.prod_multiset_count (UniqueFactorizationMonoid.normalizedFactors F))
