import FrozenTarget_64ab9ad5ed493b0b
theorem M7.FactorReplay.irreducible_check_exact : QuantumHarnessFrozenTarget := by
  change ∀ p : M7.FactorReplay.BP, M7.FactorReplay.irreducibleCheck p = true ↔ p.Monic ∧ Irreducible p
  intro p
  classical
  by_cases hp : p.Monic
  · by_cases hp1 : p = 1
    · subst p
      simp [M7.FactorReplay.irreducibleCheck]
    · rw [and_iff_right hp, hp.irreducible_iff_lt_natDegree_lt hp1]
      simp [M7.FactorReplay.irreducibleCheck, hp, hp1, List.all_eq_true,
        Finset.mem_toList, M7.FactorReplay.pool_complete, Finset.mem_Ioc,
        EuclideanDomain.mod_eq_zero, ite_eq_iff]
      <;> aesop
  · simp [M7.FactorReplay.irreducibleCheck, hp]
