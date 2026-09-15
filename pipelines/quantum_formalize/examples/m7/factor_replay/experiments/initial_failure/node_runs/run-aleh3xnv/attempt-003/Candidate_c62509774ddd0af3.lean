import FrozenTarget_c62509774ddd0af3
theorem M7.FactorReplay.irreducible_check_exact : QuantumHarnessFrozenTarget := by
  change ∀ p : M7.FactorReplay.BP, M7.FactorReplay.irreducibleCheck p = true ↔ p.Monic ∧ Irreducible p
  intro p
  classical
  by_cases hm : p.Monic
  · by_cases h1 : p = 1
    · subst p
      simp [M7.FactorReplay.irreducibleCheck]
    · simp_all [M7.FactorReplay.irreducibleCheck,
        Polynomial.Monic.irreducible_iff_lt_natDegree_lt,
        List.all_eq_true, Finset.mem_toList,
        M7.FactorReplay.pool_complete, EuclideanDomain.mod_eq_zero,
        Nat.lt_iff_add_one_le]
      <;> aesop
  · simp [M7.FactorReplay.irreducibleCheck, hm]
