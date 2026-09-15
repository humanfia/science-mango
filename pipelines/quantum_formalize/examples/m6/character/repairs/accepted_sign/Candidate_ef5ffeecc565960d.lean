import FrozenTarget_ef5ffeecc565960d
theorem M6.Character.sign_eq_one : QuantumHarnessFrozenTarget := by
  change ∀ (a : ZMod 2), (M6.Character.sign a = 1 ↔ a = 0) ∧ (M6.Character.sign a = -1 ↔ a ≠ 0)
  intro a
  have ha : a = 0 ∨ a = 1 := by
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases ha with rfl | rfl <;> norm_num [M6.Character.sign, ZMod.val_zero, ZMod.val_one_eq_one_mod]
