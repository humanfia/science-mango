import FrozenTarget_847ec27394ae851c
theorem M6.Character.sign_eq_one : QuantumHarnessFrozenTarget := by
  change ∀ (a : ZMod 2), (M6.Character.sign a = 1 ↔ a = 0) ∧ (M6.Character.sign a = -1 ↔ a ≠ 0)
  intro a
  fin_cases a <;> norm_num [M6.Character.sign]
