import FrozenTarget_f11b1b7483f382a4
theorem M7.FactorReplay.self_check : QuantumHarnessFrozenTarget := by
  change ∀ F : M7.FactorReplay.BP, F.Monic → M7.FactorReplay.check F (M7.FactorReplay.expected F) = true
  intro F hF
  classical
  apply (M7.FactorReplay.factor_check_exact F _).2
  refine ⟨?_, ?_, ?_⟩
  · simpa [M7.FactorReplay.expected, List.map_map, Function.comp_def] using
      (UniqueFactorizationMonoid.normalizedFactors F).toFinset.nodup_toList
  · intro t ht
    change t ∈ ((UniqueFactorizationMonoid.normalizedFactors F).toFinset.toList.map
      (fun p => (p, (UniqueFactorizationMonoid.normalizedFactors F).count p))) at ht
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
    have hp' : p ∈ UniqueFactorizationMonoid.normalizedFactors F :=
      Multiset.mem_toFinset.mp (Finset.mem_toList.mp hp)
    have hprime := UniqueFactorizationMonoid.prime_of_normalized_factor p hp'
    refine ⟨?_, hprime.irreducible, Multiset.count_pos.mpr hp'⟩
    have hm := Polynomial.monic_normalize hprime.ne_zero
    rw [UniqueFactorizationMonoid.normalize_normalized_factor p hp'] at hm
    exact hm
  · unfold M7.FactorReplay.product M7.FactorReplay.expected
    simp only [List.map_map, Function.comp_def]
    change ((↑((UniqueFactorizationMonoid.normalizedFactors F).toFinset.toList) :
      Multiset M7.FactorReplay.BP).map
        (fun p => p ^ (UniqueFactorizationMonoid.normalizedFactors F).count p)).prod = F
    rw [Finset.coe_toList]
    change (∏ p ∈ (UniqueFactorizationMonoid.normalizedFactors F).toFinset,
      p ^ (UniqueFactorizationMonoid.normalizedFactors F).count p) = F
    rw [← Finset.prod_multiset_count,
      UniqueFactorizationMonoid.prod_normalizedFactors_eq hF.ne_zero,
      Polynomial.Monic.normalize_eq_self hF]
