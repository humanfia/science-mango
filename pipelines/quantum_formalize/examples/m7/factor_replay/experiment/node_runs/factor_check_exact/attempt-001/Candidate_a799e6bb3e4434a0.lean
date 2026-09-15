import FrozenTarget_a799e6bb3e4434a0
theorem M7.FactorReplay.factor_check_exact : QuantumHarnessFrozenTarget := by
  change ∀ (F : M7.FactorReplay.BP) (factors : List (M7.FactorReplay.BP × ℕ)), M7.FactorReplay.check F factors = true ↔ (factors.map Prod.fst).Nodup ∧ (∀ t ∈ factors, t.1.Monic ∧ Irreducible t.1 ∧ 0 < t.2) ∧ M7.FactorReplay.product factors = F
  intro F factors
  classical
  simp [M7.FactorReplay.check, List.all_eq_true, M7.FactorReplay.irreducible_check_exact, and_assoc] <;> aesop
