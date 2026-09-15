import FrozenTarget_4f7de926d703b106
theorem M7.FactorReplay.irreducible_check_exact : QuantumHarnessFrozenTarget := by
  change ∀ p : M7.FactorReplay.BP, M7.FactorReplay.irreducibleCheck p = true ↔ p.Monic ∧ Irreducible p
  intro p
  classical
  by_cases hm : p.Monic
  · by_cases h1 : p = 1
    · subst p
      simp [M7.FactorReplay.irreducibleCheck]
    · have hc := Polynomial.Monic.irreducible_iff_lt_natDegree_lt hm
      simp_all [M7.FactorReplay.irreducibleCheck, List.all_eq_true,
        Finset.mem_toList, M7.FactorReplay.pool_complete,
        EuclideanDomain.mod_eq_zero]
      all_goals aesop
  · simp [M7.FactorReplay.irreducibleCheck, hm]
