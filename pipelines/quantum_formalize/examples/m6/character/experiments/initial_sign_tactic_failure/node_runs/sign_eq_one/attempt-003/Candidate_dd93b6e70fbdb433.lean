import FrozenTarget_dd93b6e70fbdb433
theorem M6.Character.sign_eq_one : QuantumHarnessFrozenTarget := by
  change ∀ (a : ZMod 2), (M6.Character.sign a = 1 ↔ a = 0) ∧ (M6.Character.sign a = -1 ↔ a ≠ 0)
  intro a
  fin_cases a <;> norm_num [M6.Character.sign]
