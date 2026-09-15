import FrozenTarget_7dda8521ff8d8a16
theorem M6.Character.sign_eq_one : QuantumHarnessFrozenTarget := by
  change ∀ (a : ZMod 2), (M6.Character.sign a = 1 ↔ a = 0) ∧ (M6.Character.sign a = -1 ↔ a ≠ 0)
  intro a
  fin_cases a <;> norm_num [M6.Character.sign, ZMod.val_zero, ZMod.val_one_eq_one_mod]
