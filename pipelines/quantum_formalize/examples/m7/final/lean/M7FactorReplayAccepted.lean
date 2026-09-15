import M7FactorReplay

theorem M7.FactorReplay.pool_complete : ∀ (n : ℕ) (p : M7.FactorReplay.BP), p ∈ M7.FactorReplay.pool n ↔ p.natDegree ≤ n := by
  change ∀ (n : ℕ) (p : M7.FactorReplay.BP), p ∈ M7.FactorReplay.pool n ↔ p.natDegree ≤ n
  intro n p
  classical
  unfold M7.FactorReplay.pool
  rw [Finset.mem_image]
  constructor
  · rintro ⟨v, _, rfl⟩
    have h := Polynomial.ofFn_natDegree_lt (show 1 ≤ n + 1 by omega) v
    omega
  · intro hp
    refine ⟨Polynomial.toFn (n + 1) p, Finset.mem_univ _, ?_⟩
    exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)

theorem M7.FactorReplay.irreducible_check_exact : ∀ p : M7.FactorReplay.BP, M7.FactorReplay.irreducibleCheck p = true ↔ p.Monic ∧ Irreducible p := by
  change ∀ p : M7.FactorReplay.BP, M7.FactorReplay.irreducibleCheck p = true ↔ p.Monic ∧ Irreducible p
  intro p
  classical
  by_cases hp : p.Monic
  · by_cases hp1 : p = 1
    · subst p
      simp [M7.FactorReplay.irreducibleCheck]
    · rw [and_iff_right hp, hp.irreducible_iff_lt_natDegree_lt hp1]
      simp only [M7.FactorReplay.irreducibleCheck, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true, Finset.mem_toList, M7.FactorReplay.pool_complete,
        Bool.not_eq_true_eq_eq_false, decide_eq_false_iff_not, Finset.mem_Ioc, EuclideanDomain.mod_eq_zero]
      constructor
      · rintro ⟨⟨_, _⟩, h⟩ q hq hd
        exact fun hdiv => h q hd.2 ⟨hq, hd.1, hd.2, hdiv⟩
      · intro h
        refine ⟨⟨hp,hp1⟩, ?_⟩
        intro q hq hh
        exact h q hh.1 ⟨hh.2.1,hh.2.2.1⟩ hh.2.2.2
  · simp [M7.FactorReplay.irreducibleCheck, hp]

theorem M7.FactorReplay.factor_check_exact : ∀ (F : M7.FactorReplay.BP) (factors : List (M7.FactorReplay.BP × ℕ)), M7.FactorReplay.check F factors = true ↔ (factors.map Prod.fst).Nodup ∧ (∀ t ∈ factors, t.1.Monic ∧ Irreducible t.1 ∧ 0 < t.2) ∧ M7.FactorReplay.product factors = F := by
  change ∀ (F : M7.FactorReplay.BP) (factors : List (M7.FactorReplay.BP × ℕ)), M7.FactorReplay.check F factors = true ↔ (factors.map Prod.fst).Nodup ∧ (∀ t ∈ factors, t.1.Monic ∧ Irreducible t.1 ∧ 0 < t.2) ∧ M7.FactorReplay.product factors = F
  intro F factors
  classical
  simp [M7.FactorReplay.check, List.all_eq_true, M7.FactorReplay.irreducible_check_exact, and_assoc] <;> aesop

theorem M7.FactorReplay.self_check : ∀ F : M7.FactorReplay.BP, F.Monic → M7.FactorReplay.check F (M7.FactorReplay.expected F) = true := by
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
#print axioms M7.FactorReplay.pool_complete
#print axioms M7.FactorReplay.irreducible_check_exact
#print axioms M7.FactorReplay.factor_check_exact
#print axioms M7.FactorReplay.self_check
